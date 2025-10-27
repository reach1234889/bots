import os
import sys
import subprocess
import requests
import json
import random
import string
import datetime
import time
import logging
import socket
import traceback
import shutil
import sqlite3
import threading
import uuid
import shlex
from collections import deque
from functools import wraps
from io import BytesIO

# Flask and extensions
from flask import Flask, render_template, request, jsonify, redirect, url_for, session, send_file
from flask_socketio import SocketIO, emit
from flask_login import LoginManager, UserMixin, login_user, login_required, logout_user, current_user
from werkzeug.security import generate_password_hash, check_password_hash
from werkzeug.utils import secure_filename
from flask_limiter import Limiter
from flask_limiter.util import get_remote_address

# Other libs
import docker
import psutil
import paramiko
import smtplib
from email.mime.text import MIMEText
from dotenv import load_dotenv

# ---- Basic checks / Docker install helpers ----
def check_docker_installed():
    try:
        subprocess.run(["docker", "--version"], check=True, capture_output=True)
        return True
    except Exception:
        return False

def check_docker_running():
    try:
        subprocess.run(["docker", "info"], check=True, capture_output=True)
        return True
    except Exception:
        return False

def install_docker():
    try:
        resp = requests.get("https://get.docker.com", timeout=30)
        with open("get-docker.sh", "w") as f:
            f.write(resp.text)
        subprocess.run(["sh", "get-docker.sh"], check=True)
        subprocess.run(["systemctl", "enable", "--now", "docker"], check=True)
        os.remove("get-docker.sh")
        return True
    except Exception as e:
        print(f"[Docker install error] {e}")
        return False

# If Docker missing, try install (best-effort)
if not check_docker_installed():
    print("Docker not detected. Attempting install...")
    ok = install_docker()
    if not ok:
        print("Docker install failed or skipped. Exiting.")
        # continue but docker_client will be None
if not check_docker_running():
    try:
        subprocess.run(["systemctl", "start", "docker"], check=True)
    except Exception:
        pass

# ---- Logging ----
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s',
    handlers=[logging.FileHandler('gvm_panel.log'), logging.StreamHandler()]
)
logger = logging.getLogger('GVMPanel')

# ---- Config / Env ----
load_dotenv()

SECRET_KEY = os.getenv('SECRET_KEY', ''.join(random.choices(string.ascii_letters + string.digits, k=32)))
ADMIN_USERNAME = os.getenv('ADMIN_USERNAME', 'admin')
ADMIN_PASSWORD = os.getenv('ADMIN_PASSWORD', 'admin')
PANEL_NAME = os.getenv('PANEL_NAME', 'GVM PANEL')
WATERMARK = os.getenv('WATERMARK', 'GVM VPS Service')
WELCOME_MESSAGE = os.getenv('WELCOME_MESSAGE', 'Welcome to GVM PANEL! Power Your Future!')
MAX_VPS_PER_USER = int(os.getenv('MAX_VPS_PER_USER', '5'))
DEFAULT_OS_IMAGE = os.getenv('DEFAULT_OS_IMAGE', 'ubuntu:22.04')
DOCKER_NETWORK = os.getenv('DOCKER_NETWORK', 'gvm_network')
MAX_CONTAINERS = int(os.getenv('MAX_CONTAINERS', '200'))
DB_FILE = os.getenv('DB_FILE', 'gvm_panel.db')
BACKUP_FILE = os.getenv('BACKUP_FILE', 'gvm_panel_backup.json')
try:
    SERVER_IP = os.getenv('SERVER_IP', socket.gethostbyname(socket.gethostname()))
except Exception:
    SERVER_IP = os.getenv('SERVER_IP', '127.0.0.1')
SERVER_PORT = int(os.getenv('SERVER_PORT', '3000'))
DEBUG = os.getenv('DEBUG', 'False').lower() == 'true'
UPLOAD_FOLDER = os.getenv('UPLOAD_FOLDER', 'uploads')
ALLOWED_EXTENSIONS = set(os.getenv('ALLOWED_EXTENSIONS', 'tar,gz,iso,dockerfile,png,jpg,jpeg').split(','))
SMTP_SERVER = os.getenv('SMTP_SERVER', 'smtp.example.com')
SMTP_PORT = int(os.getenv('SMTP_PORT', 587))
SMTP_USER = os.getenv('SMTP_USER', 'user@example.com')
SMTP_PASS = os.getenv('SMTP_PASS', 'password')
NOTIFICATION_EMAIL = os.getenv('NOTIFICATION_EMAIL', SMTP_USER)
VPS_HOSTNAME_PREFIX = os.getenv('VPS_HOSTNAME_PREFIX', 'gvm-')

# Dockerfile template for building base images
DOCKERFILE_TEMPLATE = """
FROM {base_image}
ENV DEBIAN_FRONTEND=noninteractive
RUN apt-get update && \\
    apt-get install -y systemd systemd-sysv dbus sudo \\
                       curl gnupg2 apt-transport-https ca-certificates \\
                       software-properties-common \\
                       docker.io openssh-server tmate && \\
    apt-get clean && rm -rf /var/lib/apt/lists/*
RUN mkdir /var/run/sshd && \\
    sed -i 's/#PermitRootLogin prohibit-password/PermitRootLogin yes/' /etc/ssh/sshd_config && \\
    sed -i 's/#PasswordAuthentication yes/PasswordAuthentication yes/' /etc/ssh/sshd_config
RUN systemctl enable ssh && \\
    systemctl enable docker
RUN apt-get update && \\
    apt-get install -y neofetch htop nano vim wget git tmux net-tools dnsutils iputils-ping ufw \\
                       fail2ban nmap iotop btop wireguard openvpn glances iftop tcpdump samba apache2 clamav sysbench && \\
    apt-get clean && \\
    rm -rf /var/lib/apt/lists/*
STOPSIGNAL SIGRTMIN+3
CMD ["/sbin/init"]
"""

# Ensure upload folder
os.makedirs(UPLOAD_FOLDER, exist_ok=True)

# ---- Flask app + extensions ----
app = Flask(__name__, static_folder='static', template_folder='templates')
app.config['SECRET_KEY'] = SECRET_KEY
app.config['UPLOAD_FOLDER'] = UPLOAD_FOLDER
app.config['MAX_CONTENT_LENGTH'] = 64 * 1024 * 1024  # 64 MB

socketio = SocketIO(app, async_mode='threading', cors_allowed_origins="*")
login_manager = LoginManager()
login_manager.init_app(app)
login_manager.login_view = 'login'

limiter = Limiter(get_remote_address, app=app, default_limits=["200 per day", "50 per hour"], storage_uri="memory://")

# ---- Database helper class ----
class Database:
    def __init__(self, db_file):
        self.db_file = db_file
        self.lock = threading.Lock()
        self.conn = None
        self.cursor = None
        self._connect()
        self._create_tables()
        self._migrate_database()
        self._initialize_settings()

    def _connect(self):
        self.conn = sqlite3.connect(self.db_file, check_same_thread=False)
        self.conn.row_factory = sqlite3.Row
        self.cursor = self.conn.cursor()

    def _execute(self, query, params=()):
        with self.lock:
            try:
                self.cursor.execute(query, params)
                self.conn.commit()
            except sqlite3.OperationalError as e:
                if "database is locked" in str(e).lower():
                    time.sleep(0.1)
                    self.cursor.execute(query, params)
                    self.conn.commit()
                else:
                    logger.exception("DB operational error")
                    raise

    def _fetchone(self, query, params=()):
        with self.lock:
            self.cursor.execute(query, params)
            return self.cursor.fetchone()

    def _fetchall(self, query, params=()):
        with self.lock:
            self.cursor.execute(query, params)
            return self.cursor.fetchall()

    def _create_tables(self):
        # users
        self._execute('''
            CREATE TABLE IF NOT EXISTS users (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                username TEXT UNIQUE,
                password TEXT,
                role TEXT DEFAULT 'user',
                email TEXT,
                created_at TEXT,
                theme TEXT DEFAULT 'light',
                credits INTEGER DEFAULT 0,
                session_id TEXT DEFAULT NULL
            )
        ''')
        # vps_instances
        self._execute('''
            CREATE TABLE IF NOT EXISTS vps_instances (
                token TEXT PRIMARY KEY,
                vps_id TEXT UNIQUE,
                container_id TEXT,
                memory INTEGER,
                cpu INTEGER,
                disk INTEGER,
                bandwidth_limit INTEGER DEFAULT 0,
                username TEXT,
                password TEXT,
                root_password TEXT,
                created_by INTEGER,
                created_at TEXT,
                tmate_session TEXT,
                watermark TEXT,
                os_image TEXT,
                restart_count INTEGER DEFAULT 0,
                last_restart TEXT,
                status TEXT DEFAULT 'running',
                port INTEGER,
                image_id TEXT,
                expires_at TEXT,
                expires_days INTEGER DEFAULT 30,
                expires_hours INTEGER DEFAULT 0,
                expires_minutes INTEGER DEFAULT 0,
                additional_ports TEXT DEFAULT '',
                uptime_start TEXT,
                tags TEXT DEFAULT '',
                shared_with TEXT DEFAULT '',
                pufferpanel_url TEXT DEFAULT NULL,
                processor_type TEXT DEFAULT 'Intel',
                FOREIGN KEY (created_by) REFERENCES users (id) ON DELETE CASCADE
            )
        ''')
        # transactions
        self._execute('''
            CREATE TABLE IF NOT EXISTS transactions (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                user_id INTEGER,
                amount INTEGER,
                upi_transaction_id TEXT,
                screenshot_path TEXT,
                status TEXT DEFAULT 'pending',
                created_at TEXT,
                processed_at TEXT,
                FOREIGN KEY (user_id) REFERENCES users (id) ON DELETE CASCADE
            )
        ''')
        # redeem_codes
        self._execute('''
            CREATE TABLE IF NOT EXISTS redeem_codes (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                code TEXT UNIQUE,
                credits INTEGER,
                name TEXT,
                created_by INTEGER,
                created_at TEXT,
                used_by INTEGER DEFAULT NULL,
                used_at TEXT DEFAULT NULL,
                status TEXT DEFAULT 'active',
                FOREIGN KEY (created_by) REFERENCES users (id),
                FOREIGN KEY (used_by) REFERENCES users (id)
            )
                # banned_users (added)
        self._execute('''
            CREATE TABLE IF NOT EXISTS banned_users (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                user_id INTEGER UNIQUE,
                reason TEXT,
                created_at TEXT,
                FOREIGN KEY (user_id) REFERENCES users (id) ON DELETE CASCADE
            )
        ''')

''')
        # system_settings
        self._execute('''
            CREATE TABLE IF NOT EXISTS system_settings (
                key TEXT PRIMARY KEY,
                value TEXT
            )
        ''')
        # usage_stats
        self._execute('''
            CREATE TABLE IF NOT EXISTS usage_stats (
                key TEXT PRIMARY KEY,
                value INTEGER DEFAULT 0
            )
        ''')
        # docker_images
        self._execute('''
            CREATE TABLE IF NOT EXISTS docker_images (
                image_id TEXT PRIMARY KEY,
                os_image TEXT,
                created_at TEXT
            )
        ''')
        # notifications
        self._execute('''
            CREATE TABLE IF NOT EXISTS notifications (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                user_id INTEGER,
                message TEXT,
                created_at TEXT,
                read BOOLEAN DEFAULT FALSE,
                FOREIGN KEY (user_id) REFERENCES users (id) ON DELETE CASCADE
            )
        ''')
        # audit_logs
        self._execute('''
            CREATE TABLE IF NOT EXISTS audit_logs (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                user_id INTEGER,
                action TEXT,
                details TEXT,
                timestamp TEXT,
                FOREIGN KEY (user_id) REFERENCES users (id) ON DELETE CASCADE
            )
        ''')
        # resource history
        self._execute('''
            CREATE TABLE IF NOT EXISTS resource_history (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                vps_id TEXT,
                cpu_percent REAL,
                memory_percent REAL,
                disk_usage REAL,
                bandwidth_in REAL,
                bandwidth_out REAL,
                timestamp TEXT,
                FOREIGN KEY (vps_id) REFERENCES vps_instances (vps_id) ON DELETE CASCADE
            )
        ''')
        # support tickets and referrals (optional)
        self._execute('''
            CREATE TABLE IF NOT EXISTS support_tickets (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                user_id INTEGER,
                subject TEXT,
                description TEXT,
                status TEXT DEFAULT 'open',
                created_at TEXT,
                FOREIGN KEY (user_id) REFERENCES users (id) ON DELETE CASCADE
            )
        ''')
        self._execute('''
            CREATE TABLE IF NOT EXISTS referrals (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                user_id INTEGER,
                referral_code TEXT UNIQUE,
                referred_users INTEGER DEFAULT 0,
                FOREIGN KEY (user_id) REFERENCES users (id) ON DELETE CASCADE
            )
        ''')

    def _migrate_database(self):
        # attempt to ensure columns exist (safe)
        try:
            rows = self._fetchall("PRAGMA table_info(vps_instances)")
            vps_columns = [r['name'] for r in rows] if rows else []
            if 'shared_with' not in vps_columns:
                self._execute('ALTER TABLE vps_instances ADD COLUMN shared_with TEXT DEFAULT ""')
            if 'pufferpanel_url' not in vps_columns:
                self._execute('ALTER TABLE vps_instances ADD COLUMN pufferpanel_url TEXT DEFAULT NULL')
            if 'processor_type' not in vps_columns:
                self._execute('ALTER TABLE vps_instances ADD COLUMN processor_type TEXT DEFAULT "Intel"')
        except Exception as e:
            logger.debug(f"_migrate_database warning: {e}")

    def _initialize_settings(self):
        defaults = {
            'max_containers': str(MAX_CONTAINERS),
            'max_vps_per_user': str(MAX_VPS_PER_USER),
            'panel_name': PANEL_NAME,
            'watermark': WATERMARK,
            'welcome_message': WELCOME_MESSAGE,
            'server_ip': SERVER_IP,
            'maintenance_mode': 'off',
            'registration_enabled': 'on',
            'upi_id': os.getenv('UPI_ID', ''),
            'upi_number': os.getenv('UPI_NUMBER', '')
        }
        for k,v in defaults.items():
            self._execute('INSERT OR IGNORE INTO system_settings (key, value) VALUES (?, ?)', (k, v))
        # create admin user if missing
        admin = self._fetchone('SELECT id FROM users WHERE username = ?', (ADMIN_USERNAME,))
        if not admin:
            hashed = generate_password_hash(ADMIN_PASSWORD)
            self._execute('INSERT INTO users (username, password, role, created_at, credits) VALUES (?, ?, ?, ?, ?)',
                          (ADMIN_USERNAME, hashed, 'admin', str(datetime.datetime.now()), 100000))

    # Basic getters / setters and utilities
    def get_setting(self, key, default=None):
        row = self._fetchone('SELECT value FROM system_settings WHERE key = ?', (key,))
        return row['value'] if row else default

    def set_setting(self, key, value):
        self._execute('INSERT OR REPLACE INTO system_settings (key, value) VALUES (?, ?)', (key, str(value)))

    def get_user(self, username):
        row = self._fetchone('SELECT * FROM users WHERE username = ?', (username,))
        return dict(row) if row else None

    def get_user_by_id(self, user_id):
        row = self._fetchone('SELECT * FROM users WHERE id = ?', (user_id,))
        return dict(row) if row else None

    def create_user(self, username, password, role='user', email=None, theme='light'):
        try:
            hashed = generate_password_hash(password)
            self._execute('INSERT INTO users (username, password, role, email, created_at, theme) VALUES (?, ?, ?, ?, ?, ?)',
                          (username, hashed, role, email, str(datetime.datetime.now()), theme))
            return True
        except sqlite3.IntegrityError:
            return False

    def update_user_session(self, user_id, session_id):
        self._execute('UPDATE users SET session_id = ? WHERE id = ?', (session_id, user_id))

    def update_user_credits(self, user_id, amount):
        self._execute('UPDATE users SET credits = credits + ? WHERE id = ?', (amount, user_id))

    def get_user_credits(self, user_id):
        r = self._fetchone('SELECT credits FROM users WHERE id = ?', (user_id,))
        return r['credits'] if r else 0

    def create_transaction(self, user_id, amount, upi_txn_id, screenshot_path):
        self._execute('INSERT INTO transactions (user_id, amount, upi_transaction_id, screenshot_path, status, created_at) VALUES (?, ?, ?, ?, "pending", ?)',
                      (user_id, amount, upi_txn_id, screenshot_path, str(datetime.datetime.now())))
        return self.cursor.lastrowid

    def get_pending_transactions(self):
        rows = self._fetchall('SELECT * FROM transactions WHERE status = "pending" ORDER BY created_at DESC')
        return [dict(r) for r in rows]

    def approve_transaction(self, txn_id, user_id, credits):
        self._execute('UPDATE transactions SET status = "approved", processed_at = ? WHERE id = ?',
                      (str(datetime.datetime.now()), txn_id))
        self.update_user_credits(user_id, credits)

    def reject_transaction(self, txn_id):
        self._execute('UPDATE transactions SET status = "rejected", processed_at = ? WHERE id = ?',
                      (str(datetime.datetime.now()), txn_id))

    def create_redeem_code(self, name, credits, created_by):
        code = ''.join(random.choices(string.ascii_uppercase + string.digits, k=12))
        try:
            self._execute('INSERT INTO redeem_codes (code, credits, name, created_by, created_at, status) VALUES (?, ?, ?, ?, ?, "active")',
                          (code, credits, name, created_by, str(datetime.datetime.now())))
            return code
        except sqlite3.IntegrityError:
            return self.create_redeem_code(name, credits, created_by)

    def redeem_code(self, code, user_id):
        row = self._fetchone('SELECT * FROM redeem_codes WHERE code = ? AND status = "active"', (code,))
        if not row:
            return False, "Invalid or already used code"
        redeem = dict(row)
        self._execute('UPDATE redeem_codes SET status = "used", used_by = ?, used_at = ? WHERE code = ?',
                      (user_id, str(datetime.datetime.now()), code))
        self.update_user_credits(user_id, redeem['credits'])
        return True, f"Redeemed {redeem['credits']} credits"

    def get_all_redeem_codes(self):
        rows = self._fetchall('SELECT * FROM redeem_codes ORDER BY created_at DESC')
        return [dict(r) for r in rows]

    def get_vps_by_id(self, vps_id):
        row = self._fetchone('SELECT * FROM vps_instances WHERE vps_id = ?', (vps_id,))
        if row:
            v = dict(row)
            return v['token'], v
        return None, None

    def get_vps_by_token(self, token):
        row = self._fetchone('SELECT * FROM vps_instances WHERE token = ?', (token,))
        return dict(row) if row else None

    def get_user_vps(self, user_id):
        rows = self._fetchall('SELECT * FROM vps_instances WHERE created_by = ? OR shared_with LIKE ?', (user_id, f'%{user_id}%'))
        return [dict(r) for r in rows]

    def get_all_vps(self):
        rows = self._fetchall('SELECT * FROM vps_instances')
        return [dict(r) for r in rows]

    def add_vps(self, vps_data):
        try:
            columns = list(vps_data.keys())
            placeholders = ','.join(['?']*len(columns))
            sql = f'INSERT INTO vps_instances ({",".join(columns)}) VALUES ({placeholders})'
            self._execute(sql, tuple(vps_data.values()))
            # increment stat
            cur = self._fetchone('SELECT value FROM usage_stats WHERE key = ?', ('total_vps_created',))
            if cur:
                self._execute('UPDATE usage_stats SET value = value + 1 WHERE key = ?', ('total_vps_created',))
            else:
                self._execute('INSERT INTO usage_stats (key, value) VALUES (?, ?)', ('total_vps_created', 1))
            return True
        except Exception as e:
            logger.error(f"add_vps error: {e}")
            return False

    def update_vps(self, token, updates):
        try:
            set_clause = ', '.join([f"{k} = ?" for k in updates.keys()])
            vals = list(updates.values()) + [token]
            self._execute(f'UPDATE vps_instances SET {set_clause} WHERE token = ?', tuple(vals))
            return True
        except Exception as e:
            logger.error(f"update_vps error: {e}")
            return False

    def remove_vps(self, token):
        self._execute('DELETE FROM vps_instances WHERE token = ?', (token,))
        return True

    def add_image(self, image_data):
        columns = ','.join(image_data.keys())
        placeholders = ','.join(['?']*len(image_data))
        self._execute(f'INSERT OR REPLACE INTO docker_images ({columns}) VALUES ({placeholders})', tuple(image_data.values()))

    def get_image(self, os_image):
        row = self._fetchone('SELECT * FROM docker_images WHERE os_image = ?', (os_image,))
        return dict(row) if row else None

    def add_notification(self, user_id, message):
        self._execute('INSERT INTO notifications (user_id, message, created_at) VALUES (?, ?, ?)', (user_id, message, str(datetime.datetime.now())))

    def get_notifications(self, user_id):
        rows = self._fetchall('SELECT * FROM notifications WHERE user_id = ? ORDER BY created_at DESC', (user_id,))
        return [dict(r) for r in rows]

    def log_action(self, user_id, action, details):
        self._execute('INSERT INTO audit_logs (user_id, action, details, timestamp) VALUES (?, ?, ?, ?)', (user_id, action, details, str(datetime.datetime.now())))

    def add_resource_history(self, vps_id, cpu, mem, disk, band_in, band_out):
        self._execute('INSERT INTO resource_history (vps_id, cpu_percent, memory_percent, disk_usage, bandwidth_in, bandwidth_out, timestamp) VALUES (?, ?, ?, ?, ?, ?, ?)',
                      (vps_id, cpu, mem, disk, band_in, band_out, str(datetime.datetime.now())))

    def get_resource_history(self, vps_id, limit=100):
        rows = self._fetchall('SELECT * FROM resource_history WHERE vps_id = ? ORDER BY timestamp DESC LIMIT ?', (vps_id, limit))
        return [dict(r) for r in rows]

    def get_all_users(self):
        rows = self._fetchall('SELECT id, username, role, created_at, email, theme, credits FROM users')
        return [dict(r) for r in rows]

    def close(self):
        self.conn.close()

    # ----- New helper methods ----- #
    def increment_referred(self, user_id):
        """Increment referred_users for a given referrer in referrals table."""
        try:
            row = self._fetchone('SELECT id FROM referrals WHERE user_id = ?', (user_id,))
            if row:
                self._execute('UPDATE referrals SET referred_users = referred_users + 1 WHERE user_id = ?', (user_id,))
            else:
                # create a referral row if it doesn't exist
                code = ''.join(random.choices(string.ascii_uppercase + string.digits, k=8))
                self._execute('INSERT INTO referrals (user_id, referral_code, referred_users) VALUES (?, ?, ?)', (user_id, code, 1))
            return True
        except Exception as e:
            logger.error(f"increment_referred error: {e}")
            return False

    def backup_data(self, path=BACKUP_FILE):
        """Dump key tables into a JSON file (best-effort)."""
        try:
            data = {}
            tables = ['users', 'vps_instances', 'transactions', 'redeem_codes', 'system_settings', 'usage_stats', 'docker_images', 'notifications', 'audit_logs', 'resource_history', 'support_tickets', 'referrals']
            for t in tables:
                try:
                    rows = self._fetchall(f"SELECT * FROM {t}")
                    data[t] = [dict(r) for r in rows]
                except Exception as e:
                    data[t] = {"error": str(e)}
            with open(path, 'w') as f:
                json.dump({'backup_at': str(datetime.datetime.now()), 'data': data}, f, default=str, indent=2)
            return True
        except Exception as e:
            logger.error(f"backup_data error: {e}")
            return False

# instantiate DB
db = Database(DB_FILE)

# ---- Docker client init ----
try:
    docker_client = docker.from_env()
    try:
        docker_client.networks.get(DOCKER_NETWORK)
    except docker.errors.NotFound:
        docker_client.networks.create(DOCKER_NETWORK)
    logger.info("Docker client initialized")
except Exception as e:
    logger.error(f"Docker init failed: {e}")
    docker_client = None

# ---- In-memory caches / helpers ----
system_stats = {}
vps_stats_cache = {}
console_sessions = {}  # sid -> dict(process/master/vps_id)
image_build_lock = threading.Lock()
resource_history_cache = {}
for v in db.get_all_vps():
    try:
        resource_history_cache[v['vps_id']] = deque(maxlen=3600)
    except Exception:
        pass

# ---- Utility functions ----
def generate_token():
    return str(uuid.uuid4())

def generate_vps_id():
    return ''.join(random.choices(string.ascii_uppercase + string.digits, k=12))

def generate_ssh_password():
    chars = string.ascii_letters + string.digits + "!@#$%^&*()_+-=[]{}|;:,.<>?"
    return ''.join(random.choices(chars, k=20))

def run_command(command, timeout=30):
    if isinstance(command, str):
        command = shlex.split(command)
    try:
        r = subprocess.run(command, capture_output=True, text=True, timeout=timeout, check=True)
        return True, r.stdout, r.stderr
    except subprocess.CalledProcessError as e:
        return False, e.stdout, e.stderr
    except subprocess.TimeoutExpired:
        return False, "", "Timeout"
    except Exception as e:
        return False, "", str(e)

def run_docker_command(container_id, command, timeout=1200):
    if isinstance(command, str):
        cmd = shlex.split(command)
    else:
        cmd = command
    try:
        r = subprocess.run(["docker", "exec", container_id] + cmd, capture_output=True, text=True, timeout=timeout, check=True)
        return True, r.stdout, r.stderr
    except subprocess.CalledProcessError as e:
        return False, e.stdout, e.stderr
    except subprocess.TimeoutExpired:
        return False, "", "Timeout"
    except Exception as e:
        return False, "", str(e)

def allowed_file(filename):
    return '.' in filename and filename.rsplit('.', 1)[1].lower() in ALLOWED_EXTENSIONS

def send_email(to_email, subject, body):
    """Send email if SMTP configured. Return True on success, False otherwise."""
    if not SMTP_SERVER or not SMTP_USER or not SMTP_PASS:
        logger.warning("SMTP not configured; skipping send_email.")
        return False
    try:
        msg = MIMEText(body)
        msg['Subject'] = subject
        msg['From'] = SMTP_USER
        msg['To'] = to_email
        with smtplib.SMTP(SMTP_SERVER, SMTP_PORT, timeout=10) as server:
            server.starttls()
            server.login(SMTP_USER, SMTP_PASS)
            server.sendmail(SMTP_USER, [to_email], msg.as_string())
        return True
    except Exception as e:
        logger.error(f"send_email error: {e}")
        return False

# ---- Image build / cache ----
def build_custom_image(base_image=DEFAULT_OS_IMAGE, dockerfile_content=None):
    with image_build_lock:
        existing = db.get_image(base_image)
        if existing:
            try:
                docker_client.images.get(existing['image_id'])
                return existing['image_id']
            except Exception:
                # remove stale DB entry
                try:
                    db._execute('DELETE FROM docker_images WHERE os_image = ?', (base_image,))
                except:
                    pass
        temp_dir = f"image_cache/{base_image.replace(':', '-')}"
        try:
            os.makedirs(temp_dir, exist_ok=True)
            dockerfile_path = os.path.join(temp_dir, 'Dockerfile')
            if dockerfile_content:
                with open(dockerfile_path, 'w') as f:
                    f.write(dockerfile_content)
            else:
                dockerfile = DOCKERFILE_TEMPLATE.format(base_image=base_image)
                with open(dockerfile_path, 'w') as f:
                    f.write(dockerfile)
            image_tag = f"hvm/{base_image.replace(':','-').lower()}:latest"
            image, logs = docker_client.images.build(path=temp_dir, tag=image_tag, rm=True, forcerm=True)
            db.add_image({
                'image_id': image_tag,
                'os_image': base_image,
                'created_at': str(datetime.datetime.now())
            })
            return image_tag
        except Exception as e:
            logger.error(f"build_custom_image error: {e}")
            raise
        finally:
            try:
                shutil.rmtree(temp_dir)
            except Exception:
                pass

# ---- Container setup after creation ----
def setup_container(container_id, memory, vps_id, ssh_port, root_password, watermark, welcome):
    try:
        # Ensure running
        container = docker_client.containers.get(container_id)
        if container.status != "running":
            container.start()
            time.sleep(3)

        # set root password
        whole = shlex.quote(f"root:{root_password}")
        cmd = f"echo {whole} | chpasswd"
        ok, out, err = run_docker_command(container_id, ["bash", "-c", cmd])
        if not ok:
            logger.warning(f"Password set failed: {err}")

        # MOTD
        welcome_q = shlex.quote(welcome)
        cmd = f"echo {welcome_q} > /etc/motd && echo 'echo {welcome_q}' >> /root/.bashrc"
        ok, out, err = run_docker_command(container_id, ["bash", "-c", cmd])

        # Hostname
        prefix = db.get_setting('vps_hostname_prefix', VPS_HOSTNAME_PREFIX)
        hostname = f"{prefix}{vps_id}"
        hostname_q = shlex.quote(hostname)
        hostname_cmd = f"echo {hostname_q} > /etc/hostname && hostname {hostname_q}"
        ok, out, err = run_docker_command(container_id, ["bash", "-c", hostname_cmd])

        # Watermark
        try:
            water_q = shlex.quote(watermark)
            run_docker_command(container_id, ["bash", "-c", f"echo {water_q} > /etc/machine-info"])
        except:
            pass

        # Basic security commands (best-effort)
        security_cmds = [
            "apt-get update -y",
            "apt-get upgrade -y",
            "ufw allow 22 || true",
            "ufw --force enable || true",
            "systemctl enable fail2ban || true",
            "systemctl start fail2ban || true"
        ]
        for c in security_cmds:
            try:
                run_docker_command(container_id, ["bash", "-c", c], timeout=300)
            except Exception:
                pass

        return True, vps_id
    except Exception as e:
        logger.error(f"setup_container error: {e}")
        return False, None

# ---- tmate session retrieval ----
def get_tmate_session(container_id, timeout=12):
    try:
        proc = subprocess.Popen(["docker", "exec", container_id, "tmate", "-F"], stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
        start = time.time()
        session = None
        while time.time() - start < timeout:
            line = proc.stdout.readline()
            if not line:
                time.sleep(0.1)
                continue
            if "ssh session:" in line:
                session = line.split("ssh session:")[-1].strip()
                break
        try:
            proc.terminate()
        except:
            pass
        return session
    except Exception as e:
        logger.error(f"get_tmate_session error: {e}")
        return None

# ---- System & VPS stats threads ----
def update_system_stats():
    global system_stats
    try:
        cpu = psutil.cpu_percent(interval=0.1)
        mem = psutil.virtual_memory()
        disk = psutil.disk_usage('/')
        net = psutil.net_io_counters()
        system_stats = {
            'cpu_usage': cpu,
            'memory_usage': mem.percent,
            'memory_used': mem.used / (1024**3),
            'memory_total': mem.total / (1024**3),
            'disk_usage': disk.percent,
            'disk_used': disk.used / (1024**3),
            'disk_total': disk.total / (1024**3),
            'network_sent_mb': net.bytes_sent / (1024**2),
            'network_recv_mb': net.bytes_recv / (1024**2),
            'last_updated': time.time()
        }
    except Exception as e:
        logger.error(f"update_system_stats error: {e}")

def update_vps_stats():
    global vps_stats_cache
    try:
        all_vps = {v['vps_id']: v for v in db.get_all_vps()}
        for vps_id, v in all_vps.items():
            if v.get('status') != 'running':
                vps_stats_cache[vps_id] = {'status': v.get('status')}
                continue
            try:
                container = docker_client.containers.get(v['container_id'])
                stats = container.stats(stream=False)
                mem_stats = stats.get('memory_stats', {})
                cpu_stats = stats.get('cpu_stats', {})
                networks = stats.get('networks', {}) or {}
                mem_usage = mem_stats.get('usage', 0) / (1024**2)
                mem_limit = mem_stats.get('limit', 1) / (1024**2)
                cpu_usage = 0
                if cpu_stats and cpu_stats.get('system_cpu_usage'):
                    total = cpu_stats['cpu_usage'].get('total_usage', 0)
                    system = cpu_stats.get('system_cpu_usage', 1)
                    cpu_usage = (total / system) * 100 if system else 0
                net_in = sum(n.get('rx_bytes', 0) for n in networks.values()) / (1024**2)
                net_out = sum(n.get('tx_bytes', 0) for n in networks.values()) / (1024**2)
                uptime_seconds = 0
                try:
                    uptime_start = datetime.datetime.fromisoformat(v.get('uptime_start'))
                    uptime_seconds = (datetime.datetime.now() - uptime_start).total_seconds()
                except Exception:
                    uptime_seconds = 0
                disk_path = f'/var/lib/docker/volumes/hvm-{vps_id}/_data'
                disk_pct = psutil.disk_usage(disk_path).percent if os.path.exists(disk_path) else 0
                vps_stats_cache[vps_id] = {
                    'cpu_percent': round(cpu_usage, 2),
                    'memory_percent': round((mem_usage / mem_limit) * 100, 2) if mem_limit else 0,
                    'net_in_mb': round(net_in, 2),
                    'net_out_mb': round(net_out, 2),
                    'disk_percent': round(disk_pct, 2),
                    'status': 'running',
                    'uptime_seconds': uptime_seconds
                }
                db.add_resource_history(vps_id, cpu_usage, (mem_usage / mem_limit * 100) if mem_limit else 0, disk_pct, net_in, net_out)
                resource_history_cache.setdefault(vps_id, deque(maxlen=3600)).append(vps_stats_cache[vps_id])
            except Exception as e:
                logger.debug(f"update_vps_stats: could not fetch for {vps_id}: {e}")
                vps_stats_cache[vps_id] = {'status': 'error'}
    except Exception as e:
        logger.error(f"update_vps_stats error: {e}")

def stats_loop():
    while True:
        try:
            update_system_stats()
            if docker_client:
                update_vps_stats()
            time.sleep(5)
        except Exception as e:
            logger.error(f"stats_loop error: {e}")
            time.sleep(5)

stats_thread = threading.Thread(target=stats_loop, daemon=True)
stats_thread.start()

# ---- Auth helpers ----
class User(UserMixin):
    def __init__(self, id, username, role='user', email=None, theme='light', credits=0):
        self.id = id
        self.username = username
        self.role = role
        self.email = email
        self.theme = theme
        self.credits = credits

@login_manager.user_loader
def load_user(user_id):
    u = db.get_user_by_id(user_id)
    if u:
        return User(u['id'], u['username'], u.get('role', 'user'), u.get('email'), u.get('theme', 'light'), u.get('credits', 0))
    return None

def is_admin(user_obj):
    u = db.get_user_by_id(user_obj.id)
    return u and u.get('role') == 'admin'

def admin_required(f):
    @wraps(f)
    def decorated(*args, **kwargs):
        if not current_user.is_authenticated or not is_admin(current_user):
            return jsonify({'error': 'Admin required'}), 403
        return f(*args, **kwargs)
    return decorated

# ---- Routes ----
@app.before_request
def single_session_check():
    # If user logged in from another session, force logout
    if current_user.is_authenticated:
        stored = db.get_user_by_id(current_user.id).get('session_id')
        if stored and stored != session.get('session_token'):
            logout_user()
            session.clear()
            return redirect(url_for('login', error='Another session detected. Please login again.'))

@app.route('/')
def index():
    if current_user.is_authenticated:
        return redirect(url_for('dashboard'))
    return redirect(url_for('login'))

@app.route('/login', methods=['GET', 'POST'])
@limiter.limit("10 per minute")
def login():
    if current_user.is_authenticated:
        return redirect(url_for('dashboard'))
    error = None
    if request.method == 'POST':
        username = request.form.get('username', '').strip()
        password = request.form.get('password', '')
        if not username or not password:
            error = 'Invalid input'
            return render_template('login.html', error=error, panel_name=db.get_setting('panel_name', PANEL_NAME))
        user = db.get_user(username)
        if user and check_password_hash(user['password'], password):
            if db._fetchone('SELECT 1 FROM banned_users WHERE user_id = ?', (user['id'],)):
                reason = db._fetchone('SELECT reason FROM banned_users WHERE user_id = ?', (user['id'],))
                return render_template('login.html', error=f'Banned: {reason[0] if reason else "No reason"}', panel_name=db.get_setting('panel_name', PANEL_NAME))
            session_token = str(uuid.uuid4())
            session['session_token'] = session_token
            db.update_user_session(user['id'], session_token)
            u = User(user['id'], user['username'], user.get('role', 'user'), user.get('email'), user.get('theme', 'light'), user.get('credits', 0))
            login_user(u)
            db.log_action(user['id'], 'login', f'Logged in from {request.remote_addr}')
            return redirect(url_for('dashboard'))
        else:
            error = 'Invalid credentials'
    return render_template('login.html', error=error, panel_name=db.get_setting('panel_name', PANEL_NAME))

@app.route('/register', methods=['GET', 'POST'])
@limiter.limit("5 per minute")
def register():
    if db.get_setting('registration_enabled', 'on') == 'off':
        return render_template('register.html', error='Registration disabled', panel_name=db.get_setting('panel_name', PANEL_NAME))
    if current_user.is_authenticated:
        return redirect(url_for('dashboard'))
    error = None
    if request.method == 'POST':
        username = request.form.get('username', '').strip()
        password = request.form.get('password', '')
        confirm = request.form.get('confirm_password', '')
        email = request.form.get('email', '').strip()
        referral = request.form.get('referral_code', '').strip()
        if not username or not password or not email:
            error = 'All fields required'
            return render_template('register.html', error=error, panel_name=db.get_setting('panel_name', PANEL_NAME))
        if password != confirm or len(password) < 6:
            error = 'Password mismatch or too short'
            return render_template('register.html', error=error, panel_name=db.get_setting('panel_name', PANEL_NAME))
        ok = db.create_user(username, password, 'user', email=email, theme='light')
        if not ok:
            error = 'Username exists'
            return render_template('register.html', error=error, panel_name=db.get_setting('panel_name', PANEL_NAME))
        user = db.get_user(username)
        db.update_user_credits(user['id'], 10)  # signup bonus
        if referral:
            ref = db._fetchone('SELECT user_id FROM referrals WHERE referral_code = ?', (referral,))
            if ref:
                db.increment_referred(ref[0])
                db.add_notification(ref[0], f'New referral: {username}')
        send_email(email, 'Welcome to GVM Panel', 'Your account has been created.')
        db.log_action(user['id'], 'register', f'Registered from {request.remote_addr}')
        return redirect(url_for('login'))
    return render_template('register.html', panel_name=db.get_setting('panel_name', PANEL_NAME))

@app.route('/logout')
@login_required
def logout():
    db.update_user_session(current_user.id, None)
    db.log_action(current_user.id, 'logout', 'User logged out')
    logout_user()
    session.clear()
    return redirect(url_for('login'))

@app.route('/dashboard')
@login_required
def dashboard():
    if db._fetchone('SELECT 1 FROM banned_users WHERE user_id = ?', (current_user.id,)):
        logout_user()
        return render_template('login.html', error='Account banned', panel_name=db.get_setting('panel_name', PANEL_NAME))
    vps_list = db.get_user_vps(current_user.id)
    notifications = db.get_notifications(current_user.id)
    stats = {
        'total_vps': len(vps_list),
        'running_vps': len([v for v in vps_list if v.get('status') == 'running']),
        'stopped_vps': len([v for v in vps_list if v.get('status') == 'stopped']),
        'credits': db.get_user_credits(current_user.id)
    }
    return render_template('dashboard.html', vps_list=vps_list, notifications=notifications, panel_name=db.get_setting('panel_name', PANEL_NAME), stats=stats, system_stats=system_stats)

# ---- Admin panel routes ----
@app.route('/admin')
@login_required
@admin_required
def admin_panel():
    users = db.get_all_users()
    all_vps = db.get_all_vps()
    pending_txns = db.get_pending_transactions()
    redeem_codes = db.get_all_redeem_codes()
    stats = {
        'total_users': len(users),
        'total_vps': len(all_vps),
        'pending_payments': len(pending_txns),
    }
    return render_template('admin.html', users=users, transactions=pending_txns, redeem_codes=redeem_codes, stats=stats, panel_name=db.get_setting('panel_name', PANEL_NAME))

@app.route('/admin/approve_payment/<int:txn_id>')
@login_required
@admin_required
def approve_payment(txn_id):
    txns = db.get_pending_transactions()
    txn = next((t for t in txns if t['id'] == txn_id), None)
    if txn:
        db.approve_transaction(txn_id, txn['user_id'], txn['amount'])
        db.add_notification(txn['user_id'], f'{txn["amount"]} credits added to your account')
        db.log_action(current_user.id, 'approve_payment', f'Approved txn {txn_id}')
    return redirect(url_for('admin_panel'))

@app.route('/admin/reject_payment/<int:txn_id>')
@login_required
@admin_required
def reject_payment(txn_id):
    txns = db.get_pending_transactions()
    txn = next((t for t in txns if t['id'] == txn_id), None)
    if txn:
        db.reject_transaction(txn_id)
        db.add_notification(txn['user_id'], 'Your payment was rejected')
        db.log_action(current_user.id, 'reject_payment', f'Rejected txn {txn_id}')
    return redirect(url_for('admin_panel'))

@app.route('/admin/create_redeem', methods=['POST'])
@login_required
@admin_required
def admin_create_redeem():
    name = request.form.get('name', '').strip()
    credits = int(request.form.get('credits', 0))
    if name and credits > 0:
        code = db.create_redeem_code(name, credits, current_user.id)
        db.log_action(current_user.id, 'create_redeem', f'Created code {code}')
    return redirect(url_for('admin_panel'))

# ---- VPS creation / management ----
@app.route('/create_vps', methods=['GET', 'POST'])
@login_required
def create_vps():
    # Admins or special flows; keep it accessible (can be restricted)
    if not docker_client:
        return render_template('error.html', error='Docker unavailable', panel_name=db.get_setting('panel_name', PANEL_NAME))
    os_images = ['ubuntu:22.04', 'ubuntu:24.04', 'debian:12', 'debian:11', 'alpine:latest']
    users = db.get_all_users()
    if request.method == 'POST':
        try:
            memory = int(request.form.get('memory', 2))
            cpu = int(request.form.get('cpu', 1))
            disk = int(request.form.get('disk', 10))
            os_image = request.form.get('os_image', DEFAULT_OS_IMAGE)
            additional_ports = request.form.get('additional_ports', '')
            expires_days = int(request.form.get('expires_days', 30))
            bandwidth_limit = int(request.form.get('bandwidth_limit', 0))
            tags = request.form.get('tags', '')
            user_id = int(request.form.get('user_id', current_user.id))

            # validate quotas
            if db.get_user_vps(user_id) and len(db.get_user_vps(user_id)) >= int(db.get_setting('max_vps_per_user', MAX_VPS_PER_USER)):
                raise ValueError('User reached max VPS')

            if len(docker_client.containers.list(all=True)) >= int(db.get_setting('max_containers', MAX_CONTAINERS)):
                raise ValueError('Max containers reached')

            vps_id = generate_vps_id()
            token = generate_token()
            root_password = generate_ssh_password()

            # pick unique ssh port
            used = set()
            for v in db.get_all_vps():
                used.add(v.get('port'))
                for p in (v.get('additional_ports') or '').split(','):
                    if p.strip():
                        try:
                            used.add(int(p.split(':')[0]))
                        except Exception:
                            pass
            ssh_port = random.randint(20000, 30000)
            while ssh_port in used:
                ssh_port = random.randint(20000, 30000)

            # build image
            dockerfile_content = None
            if 'custom_dockerfile' in request.files:
                f = request.files['custom_dockerfile']
                if f and allowed_file(f.filename):
                    dockerfile_content = f.read().decode('utf-8')

            image_tag = build_custom_image(os_image, dockerfile_content)

            # prepare ports mapping
            ports = {'22/tcp': ssh_port}
            for port_str in additional_ports.split(','):
                ps = port_str.strip()
                if not ps:
                    continue
                host_p, cont_p = ps.split(':')
                ports[f"{cont_p}/tcp"] = int(host_p)

            cpuset = f"0-{max(0,cpu-1)}" if cpu > 1 else "0"
            prefix = db.get_setting('vps_hostname_prefix', VPS_HOSTNAME_PREFIX)
            container = docker_client.containers.run(
                image_tag,
                detach=True,
                privileged=True,
                hostname=f"{prefix}{vps_id}",
                mem_limit=f"{memory}g",
                nano_cpus=cpu * 10**9,
                cpuset_cpus=cpuset,
                cap_add=["SYS_ADMIN", "NET_ADMIN"],
                security_opt=["seccomp=unconfined"],
                network=DOCKER_NETWORK,
                volumes={f'hvm-{vps_id}': {'bind': '/data', 'mode': 'rw'}},
                restart_policy={"Name": "always"},
                ports=ports
            )

            time.sleep(3)
            container.reload()

            watermark = db.get_setting('watermark', WATERMARK)
            welcome = db.get_setting('welcome_message', WELCOME_MESSAGE)
            ok, _ = setup_container(container.id, memory, vps_id, ssh_port, root_password, watermark, welcome)
            if not ok:
                container.stop()
                container.remove()
                raise Exception("Container setup failed")

            tmate = get_tmate_session(container.id)
            now = datetime.datetime.now()
            expires_at = now + datetime.timedelta(days=expires_days)
            vps_data = {
                'token': token,
                'vps_id': vps_id,
                'container_id': container.id,
                'memory': memory,
                'cpu': cpu,
                'disk': disk,
                'bandwidth_limit': bandwidth_limit,
                'username': 'root',
                'password': root_password,
                'root_password': root_password,
                'created_by': user_id,
                'created_at': str(now),
                'tmate_session': tmate,
                'watermark': watermark,
                'os_image': os_image,
                'restart_count': 0,
                'last_restart': None,
                'status': 'running',
                'port': ssh_port,
                'image_id': image_tag,
                'expires_at': str(expires_at),
                'expires_days': expires_days,
                'additional_ports': additional_ports,
                'uptime_start': str(now),
                'tags': tags
            }
            if db.add_vps(vps_data):
                db.log_action(current_user.id, 'create_vps', f'Created VPS {vps_id}')
                db.add_notification(user_id, f'New VPS {vps_id} created')
                user = db.get_user_by_id(user_id)
                if user and user.get('email'):
                    send_email(user['email'], 'VPS Created', f'Your VPS {vps_id} is ready. SSH:{SERVER_IP}:{ssh_port}')
                resource_history_cache[vps_id] = deque(maxlen=3600)
                return render_template('vps_created.html', vps=vps_data, server_ip=db.get_setting('server_ip', SERVER_IP))
            else:
                container.stop()
                container.remove()
                raise Exception('DB insert failed')
        except Exception as e:
            logger.error(f"create_vps error: {e}")
            return render_template('create_vps.html', error=str(e), os_images=os_images, users=users, panel_name=db.get_setting('panel_name', PANEL_NAME))
    return render_template('create_vps.html', os_images=os_images, users=users, panel_name=db.get_setting('panel_name', PANEL_NAME))

@app.route('/vps/<vps_id>')
@login_required
def vps_details(vps_id):
    token, vps = db.get_vps_by_id(vps_id)
    if not vps:
        return render_template('error.html', error='VPS not found', panel_name=db.get_setting('panel_name', PANEL_NAME))
    # access control: owner or shared or admin
    if vps['created_by'] != current_user.id and str(current_user.id) not in (vps.get('shared_with') or '') and not is_admin(current_user):
        return render_template('error.html', error='Access denied', panel_name=db.get_setting('panel_name', PANEL_NAME))
    # container status
    try:
        container = docker_client.containers.get(vps['container_id'])
        status = container.status
    except Exception:
        status = 'not_found'
    history = db.get_resource_history(vps_id, 360)
    return render_template('vps_details.html', vps=vps, container_status=status, server_ip=db.get_setting('server_ip', SERVER_IP), history=history)

@app.route('/vps/<vps_id>/start')
@login_required
def start_vps(vps_id):
    token, vps = db.get_vps_by_id(vps_id)
    if not vps or (vps['created_by'] != current_user.id and not is_admin(current_user)):
        return jsonify({'error': 'Access denied'}), 403
    try:
        container = docker_client.containers.get(vps['container_id'])
        if container.status == 'running':
            return jsonify({'error': 'Already running'}), 400
        container.start()
        db.update_vps(token, {'status': 'running', 'uptime_start': str(datetime.datetime.now())})
        db.log_action(current_user.id, 'start_vps', f'Started {vps_id}')
        return jsonify({'message': 'Started'})
    except Exception as e:
        logger.error(f"start_vps error: {e}")
        return jsonify({'error': str(e)}), 500

@app.route('/vps/<vps_id>/stop')
@login_required
def stop_vps(vps_id):
    token, vps = db.get_vps_by_id(vps_id)
    if not vps or (vps['created_by'] != current_user.id and not is_admin(current_user)):
        return jsonify({'error': 'Access denied'}), 403
    try:
        container = docker_client.containers.get(vps['container_id'])
        if container.status != 'running':
            return jsonify({'error': 'Already stopped'}), 400
        container.stop()
        db.update_vps(token, {'status': 'stopped'})
        db.log_action(current_user.id, 'stop_vps', f'Stopped {vps_id}')
        return jsonify({'message': 'Stopped'})
    except Exception as e:
        logger.error(f"stop_vps error: {e}")
        return jsonify({'error': str(e)}), 500

@app.route('/vps/<vps_id>/restart')
@login_required
def restart_vps(vps_id):
    token, vps = db.get_vps_by_id(vps_id)
    if not vps or (vps['created_by'] != current_user.id and not is_admin(current_user)):
        return jsonify({'error': 'Access denied'}), 403
    try:
        container = docker_client.containers.get(vps['container_id'])
        container.restart()
        db.update_vps(token, {'restart_count': (vps.get('restart_count', 0) + 1), 'last_restart': str(datetime.datetime.now()), 'status': 'running', 'uptime_start': str(datetime.datetime.now())})
        tmate = get_tmate_session(container.id)
        if tmate:
            db.update_vps(token, {'tmate_session': tmate})
        db.log_action(current_user.id, 'restart_vps', f'Restarted {vps_id}')
        return jsonify({'message': 'Restarted'})
    except Exception as e:
        logger.error(f"restart_vps error: {e}")
        return jsonify({'error': str(e)}), 500

@app.route('/vps/<vps_id>/delete', methods=['POST'])
@login_required
def delete_vps(vps_id):
    token, vps = db.get_vps_by_id(vps_id)
    if not vps or (vps['created_by'] != current_user.id and not is_admin(current_user)):
        return jsonify({'error': 'Access denied'}), 403
    try:
        try:
            container = docker_client.containers.get(vps['container_id'])
            if container.status == 'running':
                container.stop()
            container.remove()
        except Exception:
            pass
        try:
            vol = docker_client.volumes.get(f'hvm-{vps_id}')
            vol.remove(force=True)
        except Exception:
            pass
        db.remove_vps(token)
        db.log_action(current_user.id, 'delete_vps', f'Deleted {vps_id}')
        return jsonify({'message': 'Deleted'})
    except Exception as e:
        logger.error(f"delete_vps error: {e}")
        return jsonify({'error': str(e)}), 500

# ---- Console via SocketIO (basic) ----
@socketio.on('connect', namespace='/console')
def console_connect():
    emit('output', 'Console connected.\n')

@socketio.on('start_shell', namespace='/console')
def start_shell(data):
    vps_id = data.get('vps_id')
    token, vps = db.get_vps_by_id(vps_id)
    if not vps:
        emit('error', 'VPS not found')
        return
    # Check access
    if vps['created_by'] != current_user.id and not is_admin(current_user) and str(current_user.id) not in (vps.get('shared_with') or ''):
        emit('error', 'Access denied')
        return
    try:
        container_id = vps['container_id']
        # spawn pty process to docker exec -it bash
        import pty, os, select
        master, slave = pty.openpty()
        cmd = ["docker", "exec", "-it", container_id, "/bin/bash"]
        process = subprocess.Popen(cmd, stdin=slave, stdout=slave, stderr=slave, preexec_fn=os.setsid)
        console_sessions[request.sid] = {'process': process, 'master': master, 'vps_id': vps_id}
        def read_loop():
            while request.sid in console_sessions:
                try:
                    r, _, _ = select.select([master], [], [], 0.1)
                    if r:
                        out = os.read(master, 4096).decode('utf-8', errors='ignore')
                        socketio.emit('output', out, room=request.sid, namespace='/console')
                except Exception:
                    break
        threading.Thread(target=read_loop, daemon=True).start()
        emit('output', f"Connected to {vps_id}\n")
    except Exception as e:
        logger.error(f"start_shell error: {e}")
        emit('error', str(e))

@socketio.on('input', namespace='/console')
def console_input(data):
    if request.sid in console_sessions:
        master = console_sessions[request.sid]['master']
        try:
            os.write(master, data.encode('utf-8'))
        except Exception:
            pass

@socketio.on('disconnect', namespace='/console')
def console_disconnect():
    if request.sid in console_sessions:
        sess = console_sessions.pop(request.sid)
        try:
            os.close(sess['master'])
            sess['process'].terminate()
        except Exception:
            pass

# ---- Redeem / Buy credits ----
@app.route('/buy_credits', methods=['GET', 'POST'])
@login_required
def buy_credits():
    if request.method == 'POST':
        amount = int(request.form.get('amount', 0))
        upi_id = request.form.get('upi_id', '')
        txn = request.form.get('transaction_id', '').strip()
        screenshot = request.files.get('screenshot')
        if amount <= 0 or not txn or not screenshot:
            return render_template('buy_credits.html', error='All fields required', panel_name=db.get_setting('panel_name', PANEL_NAME))
        filename = secure_filename(f"{current_user.id}_{int(time.time())}_{screenshot.filename}")
        path = os.path.join(UPLOAD_FOLDER, filename)
        screenshot.save(path)
        db.create_transaction(current_user.id, amount, txn, path)
        db.add_notification(current_user.id, f'Payment of {amount} credits submitted')
        return render_template('buy_credits.html', success='Payment submitted, waiting approval', panel_name=db.get_setting('panel_name', PANEL_NAME))
    return render_template('buy_credits.html', panel_name=db.get_setting('panel_name', PANEL_NAME))

@app.route('/redeem', methods=['GET', 'POST'])
@login_required
def redeem():
    if request.method == 'POST':
        code = request.form.get('code', '').strip().upper()
        ok, msg = db.redeem_code(code, current_user.id)
        if ok:
            db.log_action(current_user.id, 'redeem', f'Redeemed {code}')
            db.add_notification(current_user.id, msg)
            return render_template('redeem.html', success=msg, panel_name=db.get_setting('panel_name', PANEL_NAME))
        else:
            return render_template('redeem.html', error=msg, panel_name=db.get_setting('panel_name', PANEL_NAME))
    return render_template('redeem.html', panel_name=db.get_setting('panel_name', PANEL_NAME))

# ---- Misc admin actions ----
@app.route('/admin/backup')
@login_required
@admin_required
def admin_backup():
    ok = db.backup_data() if hasattr(db, 'backup_data') else False
    return jsonify({'backup': bool(ok)})

# ---- Startup ----
if __name__ == '__main__':
    logger.info(f"Starting GVM Panel on {SERVER_IP}:{SERVER_PORT}")
    # For development use: socketio.run with allow_unsafe_werkzeug True to avoid Prod-only errors in dev
    socketio.run(app, host='0.0.0.0', port=SERVER_PORT, debug=DEBUG, allow_unsafe_werkzeug=True)
