from flask import Flask, jsonify, request, render_template, session, redirect, url_for
from urllib.parse import urlparse, urljoin
from functools import wraps
from werkzeug.utils import secure_filename
import json
import os
import csv
import math
import re
import unicodedata
import urllib.error
import urllib.parse
import urllib.request
import uuid
from datetime import datetime, timedelta, timezone

# app.py はプロジェクト直下に置く。
# 実体（templates / static / data）は bousai_app/ 配下にあるので、そこを参照する。
BASE_DIR = os.path.dirname(os.path.abspath(__file__))
APP_DIR = os.path.join(BASE_DIR, 'bousai_app')

app = Flask(
    __name__,
    template_folder=os.path.join(APP_DIR, 'templates'),
    static_folder=os.path.join(APP_DIR, 'static'),
)
app.secret_key = 'your-secret-key-here'

# 管理者認証情報
ADMIN_CREDENTIALS = {
    'admin': '123'
}

# ────────────────────────────────
# 気象警報・注意報設定
PREFECTURE_CODE = "020000"  # 青森県
AREA_NAME = "青森市"

# 気象庁の青森市（市区町村）コード
AREA_CODE = "0220100"

WARNING_URL = (
    f"https://www.jma.go.jp/bosai/warning/data/risk/{PREFECTURE_CODE}.json"
)
TSUNAMI_URL = "https://www.jma.go.jp/bosai/tsunami/data/list.json"
JMA_HEADERS = {"User-Agent": "Mozilla/5.0 (compatible; BousaiApp/1.0)"}

JST = timezone(timedelta(hours=9))

# 警報・注意報のコード一覧
WARNING_CODES = {
    "00": "解除",
    "02": "暴風雪警報",
    "03": "レベル3大雨警報",
    "04": "洪水警報",
    "05": "暴風警報",
    "06": "大雪警報",
    "07": "波浪警報",
    "08": "レベル3高潮警報",
    "09": "レベル3土砂災害警報",
    "10": "レベル2大雨注意報",
    "12": "大雪注意報",
    "13": "風雪注意報",
    "14": "雷注意報",
    "15": "強風注意報",
    "16": "波浪注意報",
    "17": "融雪注意報",
    "18": "洪水注意報",
    "19": "レベル2高潮注意報",
    "20": "濃霧注意報",
    "21": "乾燥注意報",
    "22": "なだれ注意報",
    "23": "低温注意報",
    "24": "霜注意報",
    "25": "着氷注意報",
    "26": "着雪注意報",
    "27": "その他の注意報",
    "29": "レベル2土砂災害注意報",
    "32": "暴風雪特別警報",
    "33": "レベル5大雨特別警報",
    "35": "暴風特別警報",
    "36": "大雪特別警報",
    "37": "波浪特別警報",
    "38": "レベル5高潮特別警報",
    "39": "レベル5土砂災害特別警報",
    "43": "レベル4大雨危険警報",
    "48": "レベル4高潮危険警報",
    "49": "レベル4土砂災害危険警報"
}

# ────────────────────────────────
# サンプルデータの読み込み
DATA_FILE = os.path.join(APP_DIR, 'data', 'shelters.json')
SHELTER_CSV_CANDIDATES = (
    os.path.join(BASE_DIR, 'all_evacuation_sites_combined.csv'),
    os.path.join(APP_DIR, 'data', 'all_evacuation_sites_combined.csv'),
)
INSTRUCTIONS_FILE = os.path.join(APP_DIR, 'data', 'instructions.json')
UPLOAD_DIR = os.path.join(APP_DIR, 'uploads')
SHELTER_UPLOAD_DIR = os.path.join(APP_DIR, 'static', 'uploads')
POSTS_FILE = os.path.join(APP_DIR, 'data', 'damage_posts.json')
NOMINATIM_URL = 'https://nominatim.openstreetmap.org/search'
NOMINATIM_HEADERS = {'User-Agent': 'BousaiApp/1.0 (shelter registration)'}
SHELTER_MEDIA_EXTENSIONS = {'.jpg', '.jpeg', '.png', '.gif', '.webp', '.mp4', '.mov', '.webm'}

ALLOWED_UPLOAD_EXTENSIONS = {
    '.jpg', '.jpeg', '.png', '.gif', '.webp', '.bmp', '.heic',
    '.mp4', '.mov', '.avi', '.webm', '.mkv', '.m4v'
}

def load_json(path, default):
    """JSONファイルを読み込む（存在しない・壊れている場合は default を返す）"""
    try:
        with open(path, encoding='utf-8') as f:
            return json.load(f)
    except (FileNotFoundError, json.JSONDecodeError):
        return default

REGION_NAMES = {
    'hokubu': '北部',
    'chuubu': '中央(1)',
    'chuubu2': '中央(2)',
    'toubu': '東部',
    'nanbu': '南部',
    'namioka': '浪岡地区',
}
CSV_FIELDS = (
    '地域区分', 'No', '地区(大字・町名)', '施設名称', '所在地',
    '洪水', '土砂災害', '高潮', '地震', '津波', '大規模な火事',
    '内水氾濫・火山現象', '指定避難所'
)


def parse_coordinate(value):
    try:
        coordinate = float(value)
    except (TypeError, ValueError):
        return None
    return coordinate if math.isfinite(coordinate) else None


def valid_aomori_coordinate(lat, lng, region_code=None):
    """青森市と浪岡地区を含む陸域の広い許容範囲だけを通す。"""
    if lat is None or lng is None or not (40.45 <= lat <= 41.15 and 140.35 <= lng <= 141.10):
        return False
    region_bounds = {
        'hokubu': (40.82, 41.15, 140.55, 141.10),
        'chuubu': (40.72, 40.95, 140.55, 141.10),
        'chuubu2': (40.72, 40.95, 140.55, 141.10),
        'toubu': (40.65, 40.95, 140.80, 141.10),
        'nanbu': (40.45, 40.80, 140.55, 141.10),
        'namioka': (40.55, 40.85, 140.35, 140.75),
    }
    bounds = region_bounds.get(region_code)
    return not bounds or (bounds[0] <= lat <= bounds[1] and bounds[2] <= lng <= bounds[3])


def normalize_shelter(raw, fallback_id):
    region_code = str(raw.get('地域区分', raw.get('region_code', '')) or '').strip()
    district = REGION_NAMES.get(region_code, '未分類')
    lat = parse_coordinate(raw.get('lat', raw.get('latitude')))
    lng = parse_coordinate(raw.get('lng', raw.get('longitude')))
    if not valid_aomori_coordinate(lat, lng, region_code):
        lat = lng = None
    shelter = {
        'id': raw.get('id', raw.get('No', fallback_id)),
        'name': str(raw.get('施設名称', raw.get('name', '')) or '').strip(),
        'district': district,
        'region_code': region_code,
        'area': str(raw.get('地区(大字・町名)', raw.get('area', '')) or '').strip(),
        'address': str(raw.get('所在地', raw.get('address', '')) or '').strip(),
        'lat': lat,
        'lng': lng,
        'latitude': lat,
        'longitude': lng,
        'description': str(raw.get('description', '') or ''),
        'amenities': raw.get('amenities', []) if isinstance(raw.get('amenities', []), list) else [],
        'image_url': str(raw.get('image_url', '') or ''),
    }
    for field in CSV_FIELDS[5:]:
        if field in raw:
            shelter[field] = raw[field]
    for field in ('capacity', 'description'):
        if field in raw:
            shelter[field] = raw[field]
    return shelter


def load_shelters():
    csv_path = next((path for path in SHELTER_CSV_CANDIDATES if os.path.isfile(path)), None)
    if csv_path:
        with open(csv_path, encoding='utf-8-sig', newline='') as source:
            return [
                normalize_shelter(row, index)
                for index, row in enumerate(csv.DictReader(source), start=1)
                if row.get('施設名称')
            ]
    return [normalize_shelter(row, index) for index, row in enumerate(load_json(DATA_FILE, []), start=1)]


def normalize_address(address):
    """全角数字・ハイフン等をNominatimで扱いやすい表記へそろえる。"""
    normalized = unicodedata.normalize('NFKC', address).strip()
    for separator in ('−', '－', '―', 'ー', '‐', '‑', '﹣', '–', '—'):
        normalized = normalized.replace(separator, '-')
    return normalized


def geocode_shelter_address(address):
    """Nominatimで青森市の住所を検索し、安全な座標だけを返す。"""
    normalized = normalize_address(address)
    queries = [normalized]
    # 番地単位のデータがない場合は、町丁目の代表座標を使う。
    block_query = re.sub(r'(\d+丁目)\d+(?:-\d+)?$', r'\1', normalized)
    block_query = re.sub(r'([町字])\d+(?:-\d+)?$', r'\1', block_query)
    if block_query != normalized:
        queries.append(block_query)
    for query in queries:
        search_query = query if '青森市' in query else f'青森市 {query}'
        params = urllib.parse.urlencode({
            'q': search_query,
            'format': 'jsonv2',
            'limit': 5,
            'countrycodes': 'jp',
            'viewbox': '140.55,41.0,140.95,40.55',
            'bounded': 1,
        })
        geocode_request = urllib.request.Request(f'{NOMINATIM_URL}?{params}', headers=NOMINATIM_HEADERS)
        with urllib.request.urlopen(geocode_request, timeout=10) as response:
            results = json.loads(response.read())
        result = next((item for item in results if '青森市' in item.get('display_name', '')), None)
        if not result:
            continue
        lat = parse_coordinate(result.get('lat'))
        lng = parse_coordinate(result.get('lon'))
        if valid_aomori_coordinate(lat, lng):
            return lat, lng
    raise ValueError('住所を地図上で検索できませんでした。市区町村・町名・番地を確認してください。')


shelters = load_shelters()
instructions = load_json(INSTRUCTIONS_FILE, [])
damage_posts = load_json(POSTS_FILE, [])

def save_instructions():
    """指示ボードのデータをファイルに保存する"""
    try:
        with open(INSTRUCTIONS_FILE, 'w', encoding='utf-8') as f:
            json.dump(instructions, f, ensure_ascii=False, indent=2)
    except Exception:
        pass


def save_damage_posts():
    """災害投稿の記録をJSONファイルに保存する"""
    try:
        with open(POSTS_FILE, 'w', encoding='utf-8') as f:
            json.dump(damage_posts, f, ensure_ascii=False, indent=2)
    except Exception:
        pass
# ────────────────────────────────

# ────────────────────────────────
# 認証関連の設定とヘルパー関数
def is_safe_url(target):
    """リダイレクト先URLが安全かどうかチェック"""
    ref_url = urlparse(request.host_url)
    test_url = urlparse(urljoin(request.host_url, target))
    return test_url.scheme in ('http', 'https') and ref_url.netloc == test_url.netloc

def login_required(f):
    """認証が必要なページに付けるデコレータ"""
    @wraps(f)
    def decorated_function(*args, **kwargs):
        if not session.get('logged_in'):
            # 現在のURLをnextパラメータとしてログイン画面にリダイレクト
            return redirect(url_for('login', next=request.url))
        return f(*args, **kwargs)
    return decorated_function

def get_japan_time():
    """日本時間（JST）の現在時刻を取得する"""
    return datetime.now(JST).strftime("%Y年%m月%d日 %H:%M")


def format_report_time(iso_str):
    """気象庁の発表時刻（ISO形式）をJSTの表示用文字列に変換する"""
    if not iso_str:
        return "不明"
    try:
        parsed = datetime.fromisoformat(iso_str.replace('Z', '+00:00'))
        if parsed.tzinfo:
            parsed = parsed.astimezone(JST)
        return parsed.strftime("%Y年%m月%d日 %H:%M")
    except ValueError:
        return iso_str


def filter_shelters(district=None, area=None):
    """表示地域名と地区名で絞り込む。全域指定は絞り込まない。"""
    return [
        shelter for shelter in shelters
        if (not district or district == '全域' or shelter.get('district') == district)
        and (not area or area == '全域' or shelter.get('area') == area)
    ]


def fetch_jma_json(url):
    """気象庁のJSONデータを取得する"""
    request = urllib.request.Request(url, headers=JMA_HEADERS)
    with urllib.request.urlopen(request, timeout=10) as response:
        return json.loads(response.read())


def parse_area_warnings(warning_data):
    """気象庁の警報JSONから対象市区町村の発表・継続中の情報を抽出する"""
    if isinstance(warning_data, dict):
        area = next(
            (
                area for area_type in warning_data.get("areaTypes", [])
                for area in area_type.get("areas", [])
                if isinstance(area, dict) and area.get("code") == AREA_CODE
            ),
            None
        )
        warnings = [
            {
                "name": WARNING_CODES.get(
                    warning.get("code", ""),
                    f"不明な警報・注意報 (コード: {warning.get('code', '')})"
                ),
                "code": warning.get("code", ""),
                "status": warning.get("status", "")
            }
            for warning in (area.get("warnings", []) if area else [])
            if isinstance(warning, dict)
            and warning.get("status") in ("発表", "継続")
        ]
        return warnings, warning_data.get("reportDatetime", "")

    if not isinstance(warning_data, list):
        raise ValueError("気象庁の警報・注意報データの形式が不正です")

    warnings = []
    seen_codes = set()
    report_datetimes = [
        report.get("reportDatetime")
        for report in warning_data
        if isinstance(report, dict) and report.get("reportDatetime")
    ]
    latest_report_datetime = max(report_datetimes, default="")

    for report in warning_data:
        if not isinstance(report, dict):
            continue

        report_datetime = report.get("reportDatetime")
        if report_datetime != latest_report_datetime:
            continue

        warning = report.get("warning")
        if not isinstance(warning, dict):
            continue

        class20_items = warning.get("class20Items", [])
        if not isinstance(class20_items, list):
            continue

        area = next(
            (
                item for item in class20_items
                if isinstance(item, dict)
                and item.get("areaCode") == AREA_CODE
            ),
            None
        )
        if not area:
            continue

        kinds = area.get("kinds", [])
        if not isinstance(kinds, list):
            continue

        for kind in kinds:
            if not isinstance(kind, dict):
                continue

            status = kind.get("status", "")
            code = kind.get("code", "")
            if status not in ("発表", "継続") or not code or code in seen_codes:
                continue

            warnings.append({
                "name": WARNING_CODES.get(
                    code,
                    f"不明な警報・注意報 (コード: {code})"
                ),
                "code": code,
                "status": status
            })
            seen_codes.add(code)

    return warnings, latest_report_datetime


def get_weather_warnings():
    """対象市区町村の警報・注意報を取得する"""
    try:
        # 青森県の新形式（令和8年～）警報・注意報データを取得
        warning_data = fetch_jma_json(WARNING_URL)

        warnings, report_datetime = parse_area_warnings(warning_data)

        return {
            "area_name": AREA_NAME,
            "warnings": warnings,
            "report_time": format_report_time(report_datetime),
            "last_fetch_time": get_japan_time()
        }

    except Exception:
        return {
            "area_name": AREA_NAME,
            "warnings": [],
            "report_time": "取得失敗",
            "last_fetch_time": get_japan_time(),
            "error": True
        }


DISASTER_WARNING_CODES = {
    "flood": {"04", "18"},
    "landslide": {"09", "29", "33", "39", "43", "49"},
    "snow": {"02", "06", "12", "13", "17", "22", "26", "32", "36"},
}


def get_disaster_info(category):
    """選択された災害カテゴリの公開情報を返す"""
    if category == "tsunami":
        try:
            tsunami_data = fetch_jma_json(TSUNAMI_URL)
            active_items = tsunami_data if isinstance(tsunami_data, list) else []
            return {
                "category": category,
                "source": "気象庁 津波情報",
                "items": active_items,
                "available": True,
                "message": "現在、津波情報は発表されていません。" if not active_items else "津波情報が発表されています。"
            }
        except Exception:
            return {
                "category": category,
                "source": "気象庁 津波情報",
                "items": [],
                "available": False,
                "message": "津波情報を取得できませんでした。"
            }

    if category in DISASTER_WARNING_CODES:
        weather = get_weather_warnings()
        codes = DISASTER_WARNING_CODES[category]
        items = [warning for warning in weather.get("warnings", []) if warning.get("code") in codes]
        available = not weather.get("error", False)
        return {
            "category": category,
            "source": "気象庁 青森県警報・注意報",
            "items": items,
            "available": available,
            "message": (
                "気象庁の警報・注意報を取得できませんでした。"
                if not available else
                "該当する警報・注意報は発表されていません。"
                if not items else
                "該当する警報・注意報があります。"
            )
        }

    return {
        "category": category,
        "source": "公開情報未提供",
        "items": [],
        "available": False,
        "message": "全国共通の無料リアルタイムAPIが確認できないため、現在は表示できません。"
    }

# トップページ：templates/index.html を返す（住民向け指示も表示する）
@app.route('/', methods=['GET', 'POST'])
def index():
    resident_notices = [i for i in instructions if i.get('target') == '住民']
    if request.method == 'POST':
        uploaded_files = [
            uploaded_file for uploaded_file in request.files.getlist('attachment')
            if uploaded_file and uploaded_file.filename
        ]
        if not uploaded_files:
            return render_template(
                'index.html',
                resident_notices=resident_notices,
                error=True,
                message='ファイルをアップロードしてください。',
                comment=request.form.get('comment', '')
            ), 400

        if len(uploaded_files) > 3:
            return render_template(
                'index.html',
                resident_notices=resident_notices,
                error=True,
                message='選択できるファイルは最大3つまでです。',
                comment=request.form.get('comment', '')
            ), 400

        prepared_files = []
        for uploaded_file in uploaded_files:
            client_filename = uploaded_file.filename
            extension = os.path.splitext(client_filename)[1].lower()
            if extension not in ALLOWED_UPLOAD_EXTENSIONS:
                allowed_extensions = ', '.join(sorted(ALLOWED_UPLOAD_EXTENSIONS))
                return render_template(
                    'index.html',
                    resident_notices=resident_notices,
                    error=True,
                    message=f'次の拡張子のみ投稿可能です: {allowed_extensions}',
                    comment=request.form.get('comment', '')
                ), 400
            safe_stem = secure_filename(os.path.splitext(client_filename)[0]) or 'upload'
            prepared_files.append((uploaded_file, client_filename, extension, safe_stem))

        os.makedirs(UPLOAD_DIR, exist_ok=True)
        comment = request.form.get('comment', '').strip()
        for uploaded_file, client_filename, extension, safe_stem in prepared_files:
            stored_name = f'{uuid.uuid4().hex}_{safe_stem}{extension}'
            uploaded_file.save(os.path.join(UPLOAD_DIR, stored_name))
            damage_posts.append({
                'comment': comment,
                'original_filename': client_filename,
                'stored_filename': stored_name,
                'extension': extension,
                'content_type': uploaded_file.mimetype,
                'created_at': datetime.now(JST).isoformat()
            })
        save_damage_posts()
        return render_template(
            'index.html',
            resident_notices=resident_notices,
            success=True,
            message='情報提供ありがとうございます。'
        )

    return render_template('index.html', resident_notices=resident_notices)

# ログインページ
@app.route('/login', methods=['GET', 'POST'])
def login():
    # リダイレクト先を取得（デフォルトは避難所登録画面）
    next_url = request.args.get('next') or request.form.get('next')

    # 安全でないURLの場合はデフォルトページにリダイレクト
    if not next_url or not is_safe_url(next_url):
        next_url = url_for('shelter_register')

    if request.method == 'POST':
        password = request.form.get('password', '').strip()

        # 認証チェック
        username = next(
            (name for name, registered_password in ADMIN_CREDENTIALS.items()
             if registered_password == password),
            None
        )
        if username:
            session['logged_in'] = True
            session['username'] = username
            # ログイン成功後は指定されたページにリダイレクト
            return redirect(next_url)
        return render_template('login.html', error=True, message="パスワードが正しくありません。", next=next_url)

    # ログイン済みの場合は指定されたページにリダイレクト
    if session.get('logged_in'):
        return redirect(next_url)

    return render_template('login.html', next=next_url)

# ログアウト
@app.route('/logout')
def logout():
    session.clear()
    return redirect(url_for('index'))

# 避難所登録ページ
@app.route('/shelter_register', methods=['GET', 'POST'])
@login_required
def shelter_register():
    def render_register(**context):
        context.setdefault('shelters', shelters)
        context.setdefault('form_data', {})
        return render_template('shelter_register.html', **context)

    if request.method == 'POST':
        edit_id = request.form.get('edit_id', '').strip()
        name = request.form.get('name', '').strip()
        address = normalize_address(request.form.get('address', ''))
        description = request.form.get('description', '').strip()
        amenities = [item for item in ('pet', 'toilet', 'wheelchair') if request.form.get(item) == 'on']
        form_data = {
            'id': edit_id, 'name': name, 'address': address,
            'description': description, 'amenities': amenities,
        }
        if not name or not address:
            return render_register(error=True, message='避難所名と住所は必須です。', form_data=form_data)

        existing = next((item for item in shelters if str(item.get('id')) == edit_id), None) if edit_id else None
        uploaded = request.files.get('image')
        extension = os.path.splitext(uploaded.filename or '')[1].lower() if uploaded else ''
        if extension and extension not in SHELTER_MEDIA_EXTENSIONS:
            return render_register(error=True, message='画像・動画は jpg、jpeg、png、gif、webp、mp4、mov、webm のみ登録できます。', form_data=form_data)
        if not existing and (not uploaded or not uploaded.filename):
            return render_register(error=True, message='画像または動画を選択してください。', form_data=form_data)

        try:
            latitude, longitude = geocode_shelter_address(address)
        except (ValueError, urllib.error.URLError, TimeoutError, json.JSONDecodeError):
            return render_register(error=True, message='住所から地図位置を取得できませんでした。住所を確認して再度お試しください。', form_data=form_data)

        if existing:
            shelter_id = existing.get('id')
            image_url = existing.get('image_url', '')
        else:
            numeric_ids = [int(item.get('id')) for item in shelters if str(item.get('id', '')).isdigit()]
            shelter_id = max(numeric_ids, default=0) + 1
            image_url = ''
        if uploaded and uploaded.filename:
            os.makedirs(SHELTER_UPLOAD_DIR, exist_ok=True)
            stored_name = f'{shelter_id}_shelter_{uuid.uuid4().hex[:8]}{extension}'
            uploaded.save(os.path.join(SHELTER_UPLOAD_DIR, stored_name))
            image_url = url_for('static', filename=f'uploads/{stored_name}')

        shelter = {
            'id': shelter_id,
            'name': name,
            'district': existing.get('district', '未分類') if existing else '未分類',
            'region_code': existing.get('region_code', '') if existing else '',
            'area': existing.get('area', '') if existing else '',
            'address': address,
            'description': description,
            'amenities': amenities,
            'latitude': latitude,
            'longitude': longitude,
            'lat': latitude,
            'lng': longitude,
            'image_url': image_url,
        }
        if existing:
            shelter_index = shelters.index(existing)
            shelters[shelter_index] = shelter
        else:
            shelters.insert(0, shelter)
        with open(DATA_FILE, 'w', encoding='utf-8') as f:
            json.dump(shelters, f, ensure_ascii=False, indent=2)

        return render_register(success=True, message=f'「{name}」を登録しました。', registered=shelter)

    edit_id = request.args.get('edit_id', '').strip()
    editing = next((item for item in shelters if str(item.get('id')) == edit_id), None)
    return render_register(editing=editing, form_data=editing or {})

# 避難所検索ページ
@app.route('/shelter_search')
def shelter_search():
    districts = sorted({s.get('district', '未分類') for s in shelters if s.get('district') != '未分類'})
    areas = sorted({s.get('area', '') for s in shelters if s.get('area')})
    return render_template('shelter_search.html', shelters=shelters, districts=districts, areas=areas)

# 全施設一覧ページ
@app.route('/all_shelters')
def all_shelters():
    return render_template('search_results.html', results=shelters)


# 指示ボード：住民向けの指示を一覧で確認する
@app.route('/board')
@login_required
def board():
    resident_instructions = [i for i in instructions if i.get('target') == '住民']
    return render_template('board.html', instructions=resident_instructions)

# 検索結果ページ：templates/search_results.html を返す
@app.route('/search_results')
def search_results():
    results = filter_shelters(request.args.get('district'), request.args.get('area'))
    return render_template('search_results.html', results=results)

# JSON API：/shelters?district=地区名
@app.route('/shelters', methods=['GET'])
def get_shelters():
    results = filter_shelters(request.args.get('district'), request.args.get('area'))
    return jsonify(results)

# 気象警報・注意報API
@app.route('/api/weather_warnings')
def api_weather_warnings():
    """気象警報・注意報をJSON形式で返すAPI"""
    return jsonify(get_weather_warnings())


@app.route('/api/disaster_info/<category>')
def api_disaster_info(category):
    """ホーム画面の災害カテゴリ別情報API"""
    allowed_categories = {"tsunami", "flood", "road_flood", "landslide", "snow", "bear"}
    if category not in allowed_categories:
        return jsonify({"error": "Unknown disaster category"}), 404
    return jsonify(get_disaster_info(category))

if __name__ == '__main__':
    app.run(debug=True, port=5000)
