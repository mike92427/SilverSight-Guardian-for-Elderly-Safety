import cv2
import mediapipe as mp
import numpy as np
import time
import threading
import requests
import math
import os
import json
from collections import deque
from ultralytics import YOLO
from gtts import gTTS
import pygame
from dotenv import load_dotenv
import uuid
import uuid
import secrets
import hashlib

# ================ 多使用者/授權設定讀取 ================
USERS_DB_PATH = os.path.join(os.path.dirname(__file__), 'users.json')

def _load_json(path, default):
    try:
        with open(path, 'r', encoding='utf-8') as f:
            data = json.load(f)
            # 如果載入的是舊格式 list，轉換成新格式
            if isinstance(data, list) and path.endswith('users.json'):
                print(f"[UsersDB] 偵測到舊格式，自動轉換...")
                return {"users": []}
            return data
    except Exception as e:
        print(f"[Load JSON] {path} 載入失敗: {e}")
        return default

USERS_DB = _load_json(USERS_DB_PATH, {"users": []})

def _save_users_db():
    try:
        print(f"[DEBUG] 準備保存到: {USERS_DB_PATH}")
        print(f"[DEBUG] 數據內容: {json.dumps(USERS_DB, ensure_ascii=False, indent=2)}")
        with open(USERS_DB_PATH, 'w', encoding='utf-8') as f:
            json.dump(USERS_DB, f, ensure_ascii=False, indent=2)
        print(f"[DEBUG] 保存成功！")
    except Exception as e:
        print(f"[UsersDB] Save error: {e}")

def _find_user_by_chat(chat_id):
    for u in USERS_DB.get('users', []):
        # 支援單一 chat_id 與多裝置 chat_ids
        if u.get('chat_id') == chat_id:
            return u
        chat_ids = u.get('chat_ids', [])
        if isinstance(chat_ids, list) and chat_id in chat_ids:
            return u
    return None

def _find_user_by_pair_code(code):
    for u in USERS_DB.get('users', []):
        if u.get('pair_code') == code:
            return u
    return None

def _allowed_camera_names_for_user(user):
    """取得使用者自己的鏡頭列表"""
    cameras = user.get('cameras', [])
    return set([c.get('name') for c in cameras if c.get('name')])

def _authorized_chat_ids_for_cam(cam_name):
    """取得擁有指定鏡頭的使用者 chat_id 列表（支援多裝置）。"""
    result = []
    for u in USERS_DB.get('users', []):
        cameras = u.get('cameras', [])
        for cam in cameras:
            if cam.get('name') == cam_name:
                # 多裝置
                chat_ids = u.get('chat_ids', [])
                if isinstance(chat_ids, list) and chat_ids:
                    result.extend([cid for cid in chat_ids if cid])
                else:
                    cid = u.get('chat_id')
                    if cid: result.append(cid)
                break
    return result

# ================= 系統設定區 (CONFIGURATION) =================
# 從 .env 載入秘密
load_dotenv()
TELEGRAM_TOKEN = os.getenv('TELEGRAM_TOKEN', '')
TELEGRAM_CHAT_ID = os.getenv('TELEGRAM_CHAT_ID', '')

# 功能設定
PRIVACY_MODE = True           # 隱私模式 (平時模糊，出事才清晰)
SEDENTARY_ALERT_SEC = 10      # 久坐提醒時間 (秒) - 測試用60秒，正式可設3600
SEDENTARY_DIST_THRES = 0.15   # 久坐移動判斷門檻

# 物品追蹤清單
TRACK_ITEMS = {67: 'cell phone', 26: 'handbag', 24: 'backpack', 65: 'remote', 39: 'bottle', 41: 'cup', 64: 'mouse', 65: 'keyboard'}

# 錄影參數
VIDEO_BUFFER_SECONDS = 5
VIDEO_POST_SECONDS = 5
FPS = 10
# =============================================================

# 初始化音效與全域鎖 (防止新增鏡頭時發生衝突)
pygame.mixer.init()
data_lock = threading.Lock()

# 使用者名單檔案（改名避免冲突）
USER_CONFIG_FILE = 'subscribed_users.json'

def load_users():
    """讀取已訂閱的使用者清單"""
    if os.path.exists(USER_CONFIG_FILE):
        try:
            with open(USER_CONFIG_FILE, 'r', encoding='utf-8') as f:
                return set(json.load(f)) # 用 set 避免重複
        except: return set()
    return set()

def save_users(users):
    """儲存使用者清單"""
    try:
        with open(USER_CONFIG_FILE, 'w', encoding='utf-8') as f:
            json.dump(list(users), f) # 轉回 list 才能存 JSON
    except Exception as e: print(f"儲存使用者失敗: {e}")

# 初始化全域使用者清單
SUBSCRIBED_USERS = load_users()
# 如果有原本的單一 ID，也加進去以免遺失
if TELEGRAM_CHAT_ID: SUBSCRIBED_USERS.add(int(TELEGRAM_CHAT_ID))

def speak_text(text):
    """Google 語音廣播"""
    def _run():
        try:
            print(f"[語音] 生成: {text}")
            tts = gTTS(text=text, lang='zh-tw')
            filename = f"voice_{int(time.time())}.mp3"
            tts.save(filename)
            while pygame.mixer.music.get_busy(): time.sleep(0.1)
            pygame.mixer.music.load(filename)
            pygame.mixer.music.play()
            while pygame.mixer.music.get_busy(): time.sleep(0.1)
            pygame.mixer.music.unload()
            try: os.remove(filename)
            except: pass
        except Exception as e: print(f"[語音錯誤] {e}")  
    threading.Thread(target=_run).start()

class VideoRecorder:
    def __init__(self, cam_name):
        self.cam_name = cam_name
        self.buffer_size = VIDEO_BUFFER_SECONDS * FPS
        self.buffer = deque(maxlen=self.buffer_size)
        self.is_recording_event = False
        self.post_event_counter = 0
        self.event_frames = []
        self.last_record_time = 0

    def update(self, frame):
        current_time = time.time()
        if current_time - self.last_record_time < (1.0 / FPS): return
        self.last_record_time = current_time
        rec_frame = cv2.resize(frame, (640, 480)).copy()
        
        time_str = time.strftime("%H:%M:%S", time.localtime())
        ms = int((current_time % 1) * 10)
        stamp = f"{time_str}.{ms}"
        cv2.putText(rec_frame, stamp, (10, 30), cv2.FONT_HERSHEY_SIMPLEX, 0.7, (0, 0, 255), 2)

        if self.is_recording_event:
            self.event_frames.append(rec_frame)
            self.post_event_counter -= 1
            if self.post_event_counter <= 0:
                self.finish_event()
        else:
            self.buffer.append(rec_frame)

    def trigger_event(self):
        if not self.is_recording_event:
            self.is_recording_event = True
            self.post_event_counter = VIDEO_POST_SECONDS * FPS
            self.event_frames = list(self.buffer)
            print(f"[{self.cam_name}] 🔴 啟動事件錄影...")

    def finish_event(self):
        """結束並上傳"""
        self.is_recording_event = False
        filename = f"fall_{self.cam_name}_{int(time.time())}.mp4"
        
        if len(self.event_frames) > 10:
            h, w, _ = self.event_frames[0].shape
            try:
                fourcc = cv2.VideoWriter_fourcc(*'avc1') # 優先嘗試 H.264
                out = cv2.VideoWriter(filename, fourcc, FPS, (w, h))
            except:
                print("avc1 失敗，退回 mp4v")
                fourcc = cv2.VideoWriter_fourcc(*'mp4v')
                out = cv2.VideoWriter(filename, fourcc, FPS, (w, h))
            
            for f in self.event_frames: out.write(f)
            out.release()
            
            print(f"[{self.cam_name}] 封裝影片中...")
            time.sleep(1.0) # 等待寫入
            send_telegram_alert(f"🚨 【跌倒影片回放】{self.cam_name}", video_path=filename)
        else:
            print(f"[{self.cam_name}] 錄影失敗: 畫面過少")
        self.event_frames = []

class CameraStream:
    def __init__(self, src, name, timeout=1.0):
        self.src = src
        self.name = name
        self.timeout = timeout
        self.capture = cv2.VideoCapture(self.src)
        self.capture.set(cv2.CAP_PROP_BUFFERSIZE, 0)
        self.status = False
        self.frame = None
        self.stopped = False
        self.lock = threading.Lock()
        self.last_read_time = time.time()
        
        print(f"[{self.name}] 連線至: {self.src}")
        if self.capture.isOpened():
            self.status, self.frame = self.capture.read()
            if self.status:
                self.last_read_time = time.time()
                print(f"[{self.name}] 連線成功！")
        
    def start(self):
        t = threading.Thread(target=self.update, args=())
        t.daemon = True
        t.start()
        return self

    def reconnect(self):
        with self.lock: self.status = False
        try: self.capture.release()
        except: pass
        time.sleep(1.0)
        try:
            new_cap = cv2.VideoCapture(self.src)
            if new_cap.isOpened():
                ret, frame = new_cap.read()
                if ret:
                    self.capture = new_cap
                    with self.lock:
                        self.frame = frame
                        self.status = True
                    self.last_read_time = time.time()
        except: pass

    def update(self):
        while not self.stopped:
            if (time.time() - self.last_read_time > self.timeout):
                self.reconnect()
                continue
            if self.capture.isOpened():
                ret, frame = self.capture.read()
                if ret and frame is not None:
                    with self.lock:
                        self.frame = frame
                        self.status = True
                    self.last_read_time = time.time()
                else:
                    time.sleep(0.1)
            else: time.sleep(0.1)

    def read(self):
        with self.lock:
            return self.status, self.frame.copy() if self.frame is not None else None

    def stop(self):
        self.stopped = True
        try: self.capture.release()
        except: pass

class ItemTracker:
    def __init__(self):
        print(">>> 載入 YOLOv8...")
        self.model = YOLO('yolov8n.pt') 
        self.last_known_positions = {}

    def scan(self, frame, cam_name):
        results = self.model(frame, verbose=False, conf=0.4)
        current_time_str = time.strftime("%H:%M:%S", time.localtime())
        for result in results:
            boxes = result.boxes
            for box in boxes:
                cls_id = int(box.cls[0])
                if cls_id in TRACK_ITEMS:
                    item_name = TRACK_ITEMS[cls_id]
                    x1, y1, x2, y2 = map(int, box.xyxy[0])
                    self.last_known_positions[item_name] = {
                        "cam_name": cam_name,
                        "frame": frame.copy(),
                        "box": (x1, y1, x2, y2),
                        "time_str": current_time_str
                    }
    def get_last_seen(self, item_name):
        return self.last_known_positions.get(item_name)

def send_telegram_reply(chat_id, msg, img=None, parse_mode=None):
    def _send():
        if not TELEGRAM_TOKEN:
            print(f"[Telegram] ⚠️ TELEGRAM_TOKEN 未設定，略過回應: {msg[:20]}")
            return
        
        base_url = f"https://api.telegram.org/bot{TELEGRAM_TOKEN}"
        data = {"chat_id": chat_id, "text": msg}
        if parse_mode:
            data["parse_mode"] = parse_mode
        
        try:
            if img is not None:
                data = {"chat_id": chat_id, "caption": msg}
                _, img_encoded = cv2.imencode('.jpg', img)
                requests.post(f"{base_url}/sendPhoto", data=data, files={'photo': img_encoded.tobytes()}, timeout=10)
            else:
                requests.post(f"{base_url}/sendMessage", data=data, timeout=10)
        except Exception as e:
            print(f"[Telegram] 回應失敗: {e}")
    
    threading.Thread(target=_send).start()

def send_telegram_alert(msg, img=None, video_path=None, target_cam_name=None):
    def _send():
        if not TELEGRAM_TOKEN:
            print("[Telegram] ⚠️ TELEGRAM_TOKEN 未設定，略過發送: ", msg[:20])
            return

        recipients = []
        if target_cam_name:
            recipients.extend(_authorized_chat_ids_for_cam(target_cam_name))
        if not recipients:
            recipients.extend(list(SUBSCRIBED_USERS))
        recipients = [int(cid) for cid in set(recipients) if cid]

        if not recipients:
            print("[Telegram] ⚠️ 無已綁定用戶，警報未發送")
            return

        base_url = f"https://api.telegram.org/bot{TELEGRAM_TOKEN}"
        print(f"[Telegram] 廣播給 {len(recipients)} 位目標用戶: {msg[:10]}...")

        base_data = {"caption": msg} if (img is not None or video_path) else {"text": msg}
        img_encoded = None
        if img is not None:
            _, img_encoded = cv2.imencode('.jpg', img)

        for chat_id in recipients:
            try:
                data = dict(base_data)
                data["chat_id"] = chat_id

                if video_path:
                    with open(video_path, 'rb') as f:
                        requests.post(f"{base_url}/sendVideo", data=data, files={'video': f}, timeout=60)
                elif img_encoded is not None:
                    requests.post(f"{base_url}/sendPhoto", data=data, files={'photo': img_encoded.tobytes()}, timeout=10)
                else:
                    requests.post(f"{base_url}/sendMessage", data=data, timeout=10)
            except Exception as e:
                print(f"[Telegram] 發送給 {chat_id} 失敗: {e}")

        if video_path:
            try: os.remove(video_path)
            except: pass

    threading.Thread(target=_send).start()

def send_command_menu(chat_id):
    base_url = f"https://api.telegram.org/bot{TELEGRAM_TOKEN}"
    if not TELEGRAM_TOKEN:
        print("[Telegram] ⚠️ TELEGRAM_TOKEN 未設定，無法傳送菜單")
        return
    keyboard_layout = {
        "keyboard": [
            [{"text": "/find 手機"}, {"text": "/find 鑰匙"}, {"text": "/find 遙控器"}],
            [{"text": "/say 站起來"}, {"text": "/say 吃藥囉"}, {"text": "/say 喝水囉"}],
            [{"text": "/current"}, {"text": "/listcams"}, {"text": "/help"}]    
        ],
        "resize_keyboard": True
    }
    requests.post(f"{base_url}/sendMessage", 
                 data={"chat_id": chat_id, "text": "🤖 控制面板", "reply_markup": json.dumps(keyboard_layout)})

def check_telegram_updates(tracker, system_context):
    offset = 0
    base_url = f"https://api.telegram.org/bot{TELEGRAM_TOKEN}"
    print(">>> Telegram 多人監聽模式啟動...")
    
    search_map = {"手機": "cell phone", "電話": "cell phone", "鍵盤": "keyboard", "滑鼠": "mouse",
        "錢包": "handbag", "皮夾": "handbag", "包包": "handbag", "背包": "backpack",
        "遙控器": "remote", "水壺": "bottle", "藥罐": "bottle", "鑰匙": "handbag", "菸": "handbag", "打火機": "handbag"}

    while True:
        try:
            resp = requests.get(f"{base_url}/getUpdates?offset={offset}&timeout=5", timeout=10)
            result = resp.json()
            
            if result.get("ok"):
                for update in result.get("result", []):
                    offset = update["update_id"] + 1
                    message = update.get("message", {})
                    text = message.get("text", "").strip()
                    cmd_lower = text.lower()
                    
                    # 取得使用者資訊
                    chat_id = message.get("chat", {}).get("id")
                    user_name = message.get("from", {}).get("first_name", "User")
                    
                    if not text or not chat_id: continue

                    # ==========================================
                    # 1. 訂閱與權限管理 (Subscription & Auth)
                    # ==========================================
                    
                    # ===== 自助註冊：/register <user_id> <password> =====
                    if cmd_lower.startswith("/register"):
                        parts = text.split()
                        if len(parts) == 3:
                            new_user_id = parts[1]
                            new_password = parts[2]
                            # 檢查 user_id 是否已存在 + 找出舊綁定
                            existing_user = None
                            old_user_with_same_chat = None
                            for u in USERS_DB.get('users', []):
                                if u.get('user_id') == new_user_id:
                                    existing_user = u
                                # 同時檢查 chat_id 和 chat_ids
                                if u.get('chat_id') == chat_id:
                                    old_user_with_same_chat = u
                                else:
                                    chat_ids = u.get('chat_ids', [])
                                    if isinstance(chat_ids, list) and chat_id in chat_ids:
                                        old_user_with_same_chat = u
                            
                            if existing_user:
                                send_telegram_reply(chat_id, f"❌ 此 user_id '{new_user_id}' 已存在，請使用其他名稱或用 /login {new_user_id} <密碼> 登入")
                            else:
                                # 清理所有用戶中的此 chat_id（確保唯一性）
                                for u in USERS_DB.get('users', []):
                                    old_chat_ids = u.get('chat_ids', [])
                                    if chat_id in old_chat_ids:
                                        old_chat_ids.remove(chat_id)
                                        u['chat_ids'] = old_chat_ids
                                    if u.get('chat_id') == chat_id:
                                        u['chat_id'] = None
                                
                                salt = secrets.token_hex(16)
                                pw_hash = hashlib.pbkdf2_hmac('sha256', new_password.encode('utf-8'), salt.encode('utf-8'), 100_000).hex()
                                new_user = {
                                    "user_id": new_user_id,
                                    "chat_id": chat_id,
                                    "chat_ids": [chat_id],
                                    "pair_code": None,
                                    "cameras": [],
                                    "password_salt": salt,
                                    "password_hash": pw_hash
                                }
                                USERS_DB['users'].append(new_user)
                                _save_users_db()
                                send_telegram_reply(chat_id, f"✅ 註冊成功！你的 user_id: {new_user_id}\n現在可以用 /addcam 新增你的鏡頭")
                                SUBSCRIBED_USERS.add(chat_id)
                                save_users(SUBSCRIBED_USERS)
                        else:
                            send_telegram_reply(chat_id, "用法：/register <你的user_id> <密碼>")
                        continue

                    # ===== 登入：/login <user_id> <password> 或 /login <pair_code> =====
                    elif cmd_lower.startswith("/login"):
                        parts = text.split()
                        if len(parts) == 3:
                            uid, pw = parts[1], parts[2]
                            target = None
                            for u in USERS_DB.get('users', []):
                                if u.get('user_id') == uid:
                                    target = u
                                    break
                            if not target:
                                send_telegram_reply(chat_id, "❌ 使用者不存在")
                            else:
                                salt = target.get('password_salt')
                                pw_hash = target.get('password_hash')
                                if salt and pw_hash:
                                    calc = hashlib.pbkdf2_hmac('sha256', pw.encode('utf-8'), salt.encode('utf-8'), 100_000).hex()
                                    if calc == pw_hash:
                                        # 清理其他用戶中的此 chat_id
                                        for u in USERS_DB.get('users', []):
                                            if u.get('user_id') != uid:
                                                old_chat_ids = u.get('chat_ids', [])
                                                if chat_id in old_chat_ids:
                                                    old_chat_ids.remove(chat_id)
                                                    u['chat_ids'] = old_chat_ids
                                                if u.get('chat_id') == chat_id:
                                                    u['chat_id'] = None
                                        
                                        # 綁定到目標用戶
                                        ids = set(target.get('chat_ids', []))
                                        ids.add(chat_id)
                                        target['chat_ids'] = list(ids)
                                        target['chat_id'] = chat_id
                                        _save_users_db()
                                        SUBSCRIBED_USERS.add(chat_id)
                                        save_users(SUBSCRIBED_USERS)
                                        send_telegram_reply(chat_id, "✅ 登入成功，已綁定此裝置")
                                    else:
                                        send_telegram_reply(chat_id, "❌ 密碼錯誤")
                                else:
                                    send_telegram_reply(chat_id, "⚠️ 此帳號目前不支援密碼登入，請使用配對碼或重新註冊")
                        elif len(parts) == 2:
                            code = parts[1]
                            user_obj = _find_user_by_pair_code(code)
                            if user_obj:
                                # 清理其他用戶中的此 chat_id
                                for u in USERS_DB.get('users', []):
                                    if u != user_obj:
                                        old_chat_ids = u.get('chat_ids', [])
                                        if chat_id in old_chat_ids:
                                            old_chat_ids.remove(chat_id)
                                            u['chat_ids'] = old_chat_ids
                                        if u.get('chat_id') == chat_id:
                                            u['chat_id'] = None
                                
                                # 綁定到目標用戶
                                chat_ids = user_obj.get('chat_ids', [])
                                if chat_id not in chat_ids:
                                    chat_ids.append(chat_id)
                                user_obj['chat_ids'] = chat_ids
                                user_obj['chat_id'] = chat_id
                                user_obj['pair_code'] = None
                                _save_users_db()
                                SUBSCRIBED_USERS.add(chat_id)
                                save_users(SUBSCRIBED_USERS)
                                send_telegram_reply(chat_id, "✅ 已綁定帳號，將僅能存取授權鏡頭。")
                            else:
                                send_telegram_reply(chat_id, "❌ 無效的配對碼或已使用")
                        else:
                            send_telegram_reply(chat_id, "用法：/login <user_id> <password> 或 /login <配對碼>")
                        continue

                    # 權限檢查：未登入的用戶提示
                    if chat_id not in SUBSCRIBED_USERS:
                        requests.post(f"{base_url}/sendMessage", data={"chat_id": chat_id, "text": "🔒 請輸入 /register [user] [password] 或 /login [user] [password] 加入系統後才能使用指令。"})
                        continue

                    # ==========================================
                    # 2. 一般功能指令
                    # ==========================================

                    if cmd_lower == "/menu":
                        send_command_menu(chat_id)

                    elif cmd_lower == "/help":
                        help_msg = (
                            "📖 <b>SilverSight 指令大全</b>\n\n"
                            "👤 <b>帳號管理</b>\n"
                            "/register [user] [password] - 註冊新帳號\n"
                            "/login [user] [password] - 登入帳號\n"
                            "/logout - 登出此裝置\n\n"
                            "📹 <b>即時監控</b>\n"
                            "/status - 查看監控畫面 (模糊保護隱私)\n"
                            "/current - 查看清晰實況畫面\n\n"
                            "🔍 <b>智能功能</b>\n"
                            "/find [物品] - 尋找物品位置\n"
                            "/say [內容] - 語音廣播訊息\n\n"
                            "🎥 <b>攝影機管理</b>\n"
                            "/listcams - 列出你的攝影機\n"
                            "/addcam [名稱] [網址] - 新增攝影機\n"
                            "/editcam [名稱] [新網址] - 修改攝影機網址\n"
                            "/delcam [名稱] - 刪除攝影機\n\n"
                            "⚙️ <b>其他</b>\n"
                            "/menu - 顯示快捷按鈕\n"
                            "/help - 顯示此說明"
                        )
                        requests.post(f"{base_url}/sendMessage", data={"chat_id": chat_id, "text": help_msg, "parse_mode": "HTML"})

                    # ==========================================
                    # 3. 攝影機管理指令 (需使用 Lock)
                    # ==========================================

                    elif cmd_lower == "/listcams":
                        # 顯示使用者自己的鏡頭
                        user_obj = _find_user_by_chat(chat_id)
                        if not user_obj:
                            send_telegram_reply(chat_id, "❌ 尚未綁定，請先 /login")
                        else:
                            cameras = user_obj.get('cameras', [])
                            cam_msg = "📋 <b>你的攝影機:</b>\n"
                            if not cameras:
                                cam_msg += "(你還沒有新增任何鏡頭)\n用 /addcam [名稱] [網址] 新增"
                            else:
                                for idx, cam in enumerate(cameras):
                                    cam_msg += f"{idx+1}. <b>{cam.get('name')}</b>\n   └ {cam.get('src')}\n"
                            send_telegram_reply(chat_id, cam_msg, parse_mode="HTML")

                    # ===== 登出：/logout =====
                    elif cmd_lower == "/logout":
                        user_obj = _find_user_by_chat(chat_id)
                        if not user_obj:
                            send_telegram_reply(chat_id, "❌ 你尚未登入")
                        else:
                            # 從 chat_ids 中移除
                            chat_ids = user_obj.get('chat_ids', [])
                            if chat_id in chat_ids:
                                chat_ids.remove(chat_id)
                                user_obj['chat_ids'] = chat_ids
                            # 如果沒有其他裝置，也清除 chat_id
                            if not chat_ids:
                                user_obj['chat_id'] = None
                            _save_users_db()
                            # 從訂閱列表移除
                            if chat_id in SUBSCRIBED_USERS:
                                SUBSCRIBED_USERS.remove(chat_id)
                                save_users(SUBSCRIBED_USERS)
                            send_telegram_reply(chat_id, "👋 已登出此裝置")
                        continue
                    
                    elif cmd_lower.startswith("/addcam"):
                        # 檢查是否已綁定
                        user_obj = _find_user_by_chat(chat_id)
                        if not user_obj:
                            send_telegram_reply(chat_id, "❌ 請先 /register 或 /login")
                            continue
                        
                        parts = text.split()
                        if len(parts) == 3:
                            new_name, new_src = parts[1], parts[2]
                            send_telegram_reply(chat_id, f"🔄 新增攝影機: {new_name}...")
                            try:
                                new_cam = CameraStream(new_src, new_name, 2.0).start()
                                new_rec = VideoRecorder(new_name)
                                mp_pose_cls = system_context['mp_pose_class']
                                new_pose = mp_pose_cls.Pose(min_detection_confidence=0.5, min_tracking_confidence=0.5)
                                
                                with data_lock:
                                    system_context['cams'].append(new_cam)
                                    system_context['recorders'][new_name] = new_rec
                                    system_context['pose_models'].append(new_pose)
                                    system_context['fall_cnt'].append(0)
                                    system_context['gesture_cnt'].append(0)
                                    system_context['person_presence'].append(0)
                                    
                                    new_config = {"src": new_src, "name": new_name, "timeout": 2.0}
                                    system_context['sources'].append(new_config)
                                
                                # 加到使用者自己的鏡頭列表（在鎖外，只寫入用戶數據庫）
                                cameras = user_obj.get('cameras', [])
                                cameras.append({"name": new_name, "src": new_src, "timeout": 2.0})
                                user_obj['cameras'] = cameras
                                _save_users_db()
                                
                                send_telegram_reply(chat_id, f"✅ 成功新增: {new_name}")
                            except Exception as e:
                                send_telegram_reply(chat_id, f"❌ 新增失敗: {e}")
                        else:
                            send_telegram_reply(chat_id, "用法: /addcam [名稱] [網址]")

                    elif cmd_lower.startswith("/delcam"):
                        user_obj = _find_user_by_chat(chat_id)
                        if not user_obj:
                            send_telegram_reply(chat_id, "❌ 請先 /register 或 /login")
                            continue
                        
                        target_name = text.replace("/delcam", "").strip()
                        if not target_name:
                            send_telegram_reply(chat_id, "用法: /delcam [名稱]")
                            continue
                        
                        # 檢查是否為用戶自己的鏡頭
                        user_cameras = user_obj.get('cameras', [])
                        cam_found = False
                        for cam in user_cameras:
                            if cam.get('name') == target_name:
                                cam_found = True
                                break
                        
                        if not cam_found:
                            send_telegram_reply(chat_id, f"❌ 找不到你的鏡頭: {target_name}")
                            continue
                        
                        deleted = False
                        with data_lock:
                            found_idx = -1
                            for i, src in enumerate(system_context['sources']):
                                if src['name'] == target_name:
                                    found_idx = i
                                    break
                            
                            if found_idx != -1:
                                send_telegram_reply(chat_id, f"🗑️ 刪除中: {target_name}...")
                                try: system_context['cams'][found_idx].stop()
                                except: pass

                                del system_context['cams'][found_idx]
                                del system_context['pose_models'][found_idx]
                                del system_context['fall_cnt'][found_idx]
                                del system_context['gesture_cnt'][found_idx]
                                del system_context['person_presence'][found_idx]
                                del system_context['sources'][found_idx]
                                if target_name in system_context['recorders']:
                                    del system_context['recorders'][target_name]

                                # 從用戶資料庫中移除鏡頭
                                user_cameras = [c for c in user_cameras if c.get('name') != target_name]
                                user_obj['cameras'] = user_cameras
                                _save_users_db()
                                
                                deleted = True
                        
                        if deleted: send_telegram_reply(chat_id, f"✅ 已刪除: {target_name}")
                        else: send_telegram_reply(chat_id, f"❌ 系統中找不到: {target_name}")

                    elif cmd_lower.startswith("/editcam"):
                        user_obj = _find_user_by_chat(chat_id)
                        if not user_obj:
                            send_telegram_reply(chat_id, "❌ 請先 /register 或 /login")
                            continue
                        
                        parts = text.split()
                        if len(parts) == 3:
                            target_name, new_url = parts[1], parts[2]
                            
                            # 檢查是否為用戶自己的鏡頭
                            user_cameras = user_obj.get('cameras', [])
                            cam_found = False
                            for cam in user_cameras:
                                if cam.get('name') == target_name:
                                    cam_found = True
                                    break
                            
                            if not cam_found:
                                send_telegram_reply(chat_id, f"❌ 找不到你的鏡頭: {target_name}")
                                continue
                            
                            edited = False
                            with data_lock:
                                found_idx = -1
                                for i, src in enumerate(system_context['sources']):
                                    if src['name'] == target_name:
                                        found_idx = i
                                        break
                                
                                if found_idx != -1:
                                    send_telegram_reply(chat_id, f"🔄 更新中: {target_name}...")
                                    try: system_context['cams'][found_idx].stop()
                                    except: pass
                                    
                                    try:
                                        new_cam = CameraStream(new_url, target_name, 2.0).start()
                                        system_context['cams'][found_idx] = new_cam
                                        system_context['sources'][found_idx]['src'] = new_url
                                        
                                        # 更新用戶資料庫中的鏡頭 URL
                                        for cam in user_cameras:
                                            if cam.get('name') == target_name:
                                                cam['src'] = new_url
                                                break
                                        user_obj['cameras'] = user_cameras
                                        _save_users_db()
                                        
                                        edited = True
                                    except Exception as e:
                                        send_telegram_reply(chat_id, f"❌ 更新失敗: {e}")
                            
                            if edited: send_telegram_reply(chat_id, f"✅ {target_name} 更新完成")
                            elif found_idx == -1: send_telegram_reply(chat_id, f"❌ 系統中找不到: {target_name}")
                        else:
                            send_telegram_reply(chat_id, "用法: /editcam [名稱] [新網址]")

                    # ==========================================
                    # 4. 監控與互動指令
                    # ==========================================

                    elif cmd_lower.startswith("/find"):
                        parts = text.split()
                        if len(parts) > 1:
                            # 獲取用戶的鏡頭列表
                            user_obj = _find_user_by_chat(chat_id)
                            if not user_obj:
                                send_telegram_reply(chat_id, "❌ 請先 /register 或 /login")
                                continue
                            
                            user_camera_names = set([c.get('name') for c in user_obj.get('cameras', [])])
                            if not user_camera_names:
                                send_telegram_reply(chat_id, "(空) 你還沒有新增任何鏡頭")
                                continue
                            
                            target_item = parts[1]
                            target_key = search_map.get(target_item, target_item)
                            info = tracker.get_last_seen(target_key)
                            
                            if info:
                                # 檢查物品所在鏡頭是否屬於該用戶
                                if info['cam_name'] not in user_camera_names:
                                    send_telegram_reply(chat_id, f"❌ 找不到 '{target_item}'")
                                else:
                                    # 原本的處理：顯示找到的物品
                                    img = info['frame'].copy()
                                    box = info['box']
                                    cv2.rectangle(img, (box[0], box[1]), (box[2], box[3]), (0, 255, 255), 3)
                                    cv2.putText(img, f"HERE! ({info['time_str']})", (box[0], box[1]-10), 
                                              cv2.FONT_HERSHEY_SIMPLEX, 0.8, (0, 255, 255), 2)
                                    send_telegram_reply(chat_id, f"🔍 找到了: {target_item}\n位置: {info['cam_name']}\n時間: {info['time_str']}", img=img)
                            else:
                                send_telegram_reply(chat_id, f"❌ 找不到 '{target_item}'")
                        else:
                            send_telegram_reply(chat_id, "用法: /find [物品名]")

                    elif cmd_lower.startswith("/say"):
                        content = text[4:].strip() 
                        if content:
                            send_telegram_reply(chat_id, f"📢 廣播: {content}")
                            speak_text(content)
                        else:
                            send_telegram_reply(chat_id, "用法: /say [內容]")

                    elif cmd_lower.startswith("/current") or cmd_lower.startswith("/status"):
                        # 僅允許已綁定且有自己鏡頭的使用者查看
                        user_obj = _find_user_by_chat(chat_id)
                        if not user_obj:
                            send_telegram_reply(chat_id, "🔒 請先 /register 或 /login 綁定帳號")
                            continue
                        cameras = user_obj.get('cameras', [])
                        camera_names = set([c.get('name') for c in cameras if c.get('name')])
                        if not camera_names:
                            send_telegram_reply(chat_id, "(空) 你還沒有新增任何鏡頭。請用 /addcam 新增")
                            continue

                        send_telegram_reply(chat_id, "📸 正在擷取畫面...")
                        found = False
                        with data_lock:
                            current_cams = list(system_context['cams'])

                        for cam in current_cams:
                            if cam.name not in camera_names:
                                continue
                            ret, frame = cam.read()
                            if ret:
                                if PRIVACY_MODE and not cmd_lower.startswith("/current"):
                                    frame = cv2.GaussianBlur(frame, (51, 51), 0)
                                    cv2.putText(frame, "PRIVACY MODE", (10, 240), cv2.FONT_HERSHEY_SIMPLEX, 1, (255,255,255), 2)
                                send_telegram_reply(chat_id, f"[{cam.name}]", img=frame)
                                found = True
                        if not found:
                            send_telegram_reply(chat_id, "⚠️ 無法讀取畫面或鏡頭離線")

        except Exception as e:
            print(f"[Telegram Loop Error] {e}")
            time.sleep(5)
        
        time.sleep(0.5)

def calculate_angle_with_vertical(p1, p2):
    dy = p2.y - p1.y
    dx = p2.x - p1.x
    return math.degrees(math.atan2(abs(dx), abs(dy)))

def is_fall_detected_v2(landmarks, frame_shape):
    nose = landmarks[0]
    l_sh, r_sh = landmarks[11], landmarks[12]
    l_hip, r_hip = landmarks[23], landmarks[24]
    l_knee, r_knee = landmarks[25], landmarks[26]
    
    core_points = [nose, l_sh, r_sh, l_hip, r_hip]
    if sum(1 for kp in core_points if kp.visibility > 0.4) < 3:
        return False, "Searching...", {"total_score": 0.0}

    sh_x, sh_y = (l_sh.x + r_sh.x)/2, (l_sh.y + r_sh.y)/2
    hip_x, hip_y = (l_hip.x + r_hip.x)/2, (l_hip.y + r_hip.y)/2
    
    trunk_len = math.sqrt((sh_x-hip_x)**2 + (sh_y-hip_y)**2)
    if trunk_len < 0.1: return False, "Too Small", {"total_score": 0.0}

    mid_sh = type('o', (object,), {'x': sh_x, 'y': sh_y})
    mid_hip = type('o', (object,), {'x': hip_x, 'y': hip_y})
    torso_angle = calculate_angle_with_vertical(mid_sh, mid_hip)
    
    active_kps = [l_sh, r_sh, l_hip, r_hip, l_knee, r_knee, nose]
    xs = [k.x for k in active_kps if k.visibility > 0.4]
    ys = [k.y for k in active_kps if k.visibility > 0.4]
    ar = (max(xs)-min(xs))/(max(ys)-min(ys)) if (xs and ys and (max(ys)-min(ys))>0) else 0

    # 坐姿過濾邏輯
    thigh_l_angle = calculate_angle_with_vertical(l_hip, l_knee)
    thigh_r_angle = calculate_angle_with_vertical(r_hip, r_knee)
    avg_thigh_angle = (thigh_l_angle + thigh_r_angle) / 2
    vertical_dist = hip_y - nose.y

    is_sitting = False
    if avg_thigh_angle > 40 and torso_angle < 45: is_sitting = True
    elif avg_thigh_angle > 40 and vertical_dist > 0.2: is_sitting = True
    elif torso_angle < 30 and vertical_dist > 0.15: is_sitting = True

    if is_sitting:
        return False, f"Sitting (T:{int(torso_angle)} V:{vertical_dist:.2f})", {"total_score": 0.0}

    score = 0.0
    if torso_angle > 60: score += 1.0
    elif torso_angle > 45: score += 0.6
    if ar > 1.4: score += 0.5
    elif ar > 1.0: score += 0.3
    if hip_y > 0.7: score += 0.2
    if vertical_dist < 0.1: score += 0.4
    if nose.y > hip_y: score += 0.5

    status = f"Norm (T:{int(torso_angle)} V:{vertical_dist:.2f})"
    is_fall = False
    if score >= 0.5:
        status = f"FALL! ({score:.1f})"
        is_fall = True
    elif score >= 0.3: 
        status = f"Warning ({score:.1f})"

    return is_fall, status, {"total_score": score}

def check_emergency_gesture(landmarks):
    nose = landmarks[0]
    l_wrist, r_wrist = landmarks[15], landmarks[16]
    if (l_wrist.y < nose.y and r_wrist.y < nose.y) and \
       (l_wrist.visibility > 0.5 and r_wrist.visibility > 0.5):
        return True
    return False

def main():
    mp_pose = mp.solutions.pose
    mp_drawing = mp.solutions.drawing_utils
    
    # 從所有用戶的 cameras 陣列中加載攝影機
    print(">>> 載入用戶攝影機...")
    camera_sources = []
    for user in USERS_DB.get('users', []):
        cameras = user.get('cameras', [])
        for cam in cameras:
            # 避免重複
            if not any(c.get('name') == cam.get('name') for c in camera_sources):
                camera_sources.append(cam)
                print(f"    - 載入 {user.get('user_id')} 的攝影機: {cam.get('name')}")
    
    # 3. 初始化物件容器
    pose_models = []
    cams = []
    recorders = {}
    fall_cnt = []
    gesture_cnt = []
    person_presence = []
    
    item_tracker = ItemTracker()

    print(">>> 初始化攝影機...")
    for src_info in camera_sources:
        cam = CameraStream(src_info["src"], src_info["name"], src_info.get("timeout", 1.0)).start()
        cams.append(cam)
        recorders[cam.name] = VideoRecorder(cam.name)
        pose_models.append(mp_pose.Pose(min_detection_confidence=0.5, min_tracking_confidence=0.5))
        fall_cnt.append(0)
        gesture_cnt.append(0)
        person_presence.append(0)

    # 包裝 context 傳給 Telegram 執行緒
    system_context = {'sources': camera_sources, 'cams': cams, 'recorders': recorders, 'pose_models': pose_models,
        'fall_cnt': fall_cnt, 'gesture_cnt': gesture_cnt, 'person_presence': person_presence, 'mp_pose_class': mp_pose}

    t_tg = threading.Thread(target=check_telegram_updates, args=(item_tracker, system_context))
    t_tg.daemon = True
    t_tg.start()

    print(">>> 系統啟動...")
    speak_text("系統啟動")
    send_telegram_alert("✅ SilverSight v5.0 (含動態鏡頭管理) 已啟動")
    
    sedentary_data = {} 
    alert_cooldown = 0
    frame_count = 0 

    try:
        while True:
            current_time = time.time()
            frame_count += 1
            display_frames = []

            # 使用 Lock 保護，避免迭代時列表被 Telegram 修改
            with data_lock:
                # 這裡不需要 deepcopy，只要確保迭代次數正確
                num_cams_now = len(cams)
                
                for i in range(num_cams_now):
                    cam = cams[i]
                    ret, frame = cam.read()
                    
                    if not ret or frame is None:
                        display_frames.append(np.zeros((480, 640, 3), dtype=np.uint8))
                        continue
                    
                    frame = cv2.resize(frame, (640, 480))
                    recorders[cam.name].update(frame)

                    if frame_count % 30 == 0:
                        item_tracker.scan(frame, cam.name)

                    rgb_frame = cv2.cvtColor(frame, cv2.COLOR_BGR2RGB)
                    rgb_frame.flags.writeable = False
                    results = pose_models[i].process(rgb_frame)
                    
                    status_text = "Safe"
                    color = (0, 255, 0)
                    is_emergency_event = False

                    if results.pose_landmarks:
                        person_presence[i] = min(person_presence[i] + 1, 30)
                        landmarks = results.pose_landmarks.landmark

                        # 1. 跌倒偵測
                        is_fall, debug_msg, scores = is_fall_detected_v2(landmarks, frame.shape)
                        cv2.putText(frame, debug_msg, (10, 80), cv2.FONT_HERSHEY_SIMPLEX, 0.6, (255, 255, 0), 2)
                        
                        if is_fall: fall_cnt[i] += 1
                        else: fall_cnt[i] = max(0, fall_cnt[i] - 1)

                        if fall_cnt[i] > 10: 
                            status_text = "FALL DETECTED!"
                            color = (0, 0, 255)
                            is_emergency_event = True
                            if current_time - alert_cooldown > 15:
                                send_telegram_alert(f"⚠️ 警告：{cam.name} 跌倒！", img=frame, target_cam_name=cam.name)
                                speak_text("警告，偵測到跌倒")
                                recorders[cam.name].trigger_event()
                                alert_cooldown = current_time

                        # 2. 求救手勢
                        if check_emergency_gesture(landmarks):
                            gesture_cnt[i] += 1
                            cv2.putText(frame, "SOS GESTURE!", (10, 110), cv2.FONT_HERSHEY_SIMPLEX, 0.8, (0, 0, 255), 2)
                            if gesture_cnt[i] > 30: 
                                status_text = "SOS REQUEST!"
                                color = (0, 0, 255)
                                is_emergency_event = True
                                if current_time - alert_cooldown > 15:
                                    send_telegram_alert(f"🆘 求救：{cam.name} 偵測到求救手勢！", img=frame, target_cam_name=cam.name)
                                    speak_text("收到求救信號")
                                    recorders[cam.name].trigger_event()
                                    alert_cooldown = current_time
                                    gesture_cnt[i] = 0
                        else:
                            gesture_cnt[i] = 0

                        # 3. 久坐偵測
                        l_hip, r_hip = landmarks[23], landmarks[24]
                        if l_hip.visibility > 0.5 and r_hip.visibility > 0.5:
                            cx, cy = (l_hip.x + r_hip.x)/2, (l_hip.y + r_hip.y)/2
                            
                            if i not in sedentary_data:
                                sedentary_data[i] = {'start': current_time, 'pos': (cx, cy), 'last_alert': 0}
                            
                            last_cx, last_cy = sedentary_data[i]['pos']
                            dist = math.sqrt((cx-last_cx)**2 + (cy-last_cy)**2)
                            
                            if dist > SEDENTARY_DIST_THRES:
                                sedentary_data[i]['start'] = current_time
                                sedentary_data[i]['pos'] = (cx, cy)
                            else:
                                duration = current_time - sedentary_data[i]['start']
                                cv2.putText(frame, f"Static: {int(duration)}s", (500, 450), cv2.FONT_HERSHEY_SIMPLEX, 0.6, (255,255,255), 1)
                                if duration > SEDENTARY_ALERT_SEC:
                                    if current_time - sedentary_data[i]['last_alert'] > 300: 
                                        speak_text("坐太久囉，起來走一走吧")
                                        send_telegram_alert(f"💤 提醒：{cam.name} 久坐", target_cam_name=cam.name)
                                        sedentary_data[i]['last_alert'] = current_time

                        mp_drawing.draw_landmarks(frame, results.pose_landmarks, mp_pose.POSE_CONNECTIONS)
                    else:
                        person_presence[i] = max(person_presence[i] - 1, 0)
                        if i in sedentary_data: sedentary_data.pop(i)

                    # 介面顯示
                    cv2.rectangle(frame, (0,0), (640, 40), color, -1)
                    cv2.putText(frame, f"{cam.name}: {status_text}", (10, 30), cv2.FONT_HERSHEY_SIMPLEX, 0.7, (255, 255, 255), 2)
                    
                    final_display_frame = frame
                    if PRIVACY_MODE and not is_emergency_event:
                        final_display_frame = cv2.GaussianBlur(frame, (51, 51), 0)
                        cv2.putText(final_display_frame, "PRIVACY PROTECTED", (160, 240), cv2.FONT_HERSHEY_SIMPLEX, 1, (255, 255, 255), 2)

                    display_frames.append(final_display_frame)

            num_cams = len(display_frames)
            if num_cams == 0:
                # 若無鏡頭，顯示提示訊息並持續運行
                blank = np.zeros((480, 640, 3), dtype=np.uint8)
                cv2.putText(blank, "No Cameras Yet", (150, 240), cv2.FONT_HERSHEY_SIMPLEX, 1, (255,255,255), 2)
                cv2.putText(blank, "Use /addcam to add cameras", (100, 300), cv2.FONT_HERSHEY_SIMPLEX, 0.8, (100,100,255), 2)
                cv2.imshow("SilverSight Pro", blank)
            elif num_cams == 1:
                final_view = display_frames[0]
                cv2.imshow("SilverSight Pro", final_view)
            elif num_cams == 2:
                final_view = np.hstack(display_frames)
                cv2.imshow("SilverSight Pro", final_view)
            elif num_cams >= 3:
                # 簡單網格拼接 (2xN)
                row1 = np.hstack(display_frames[:2])
                row2_list = display_frames[2:4]
                while len(row2_list) < 2: row2_list.append(np.zeros((480, 640, 3), dtype=np.uint8))
                row2 = np.hstack(row2_list)
                final_view = np.vstack([row1, row2])
                final_view = cv2.resize(final_view, (960, 720))
                cv2.imshow("SilverSight Pro", final_view)
            
            if cv2.waitKey(1) & 0xFF == ord('q'): break
            time.sleep(0.01)  # 避免 CPU 過度占用

    except KeyboardInterrupt: pass
    finally:
        for cam in cams: cam.stop()
        cv2.destroyAllWindows()

if __name__ == "__main__":
    main()