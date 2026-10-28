#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Мониторинг на новопубликувани обществени поръчки от ЦАИС ЕОП
================================================================

Проверява на всеки N секунди (по подразбиране 60) страницата
https://app.eop.bg/today („Публикувани днес“) и отпечатва в конзолата
всяка НОВА обществена поръчка със следните данни:

  * уникален номер на поръчката
  * начин на възлагане
  * обект на поръчката
  * прогнозна стойност (без ДДС)
  * дата на публикуване
  * име
  * възложител
  * лице за контакт
  * кратко описание / документация
  * връзки към прикачените файлове за сваляне
  * URL към съответната поръчка

Защо Playwright
---------------
Сайтът е SPA (Angular) и съдържанието се зарежда динамично през
JavaScript (AJAX/WCF услуги). Затова данните се извличат с помощта на
Playwright (headless Chromium):

  * списъкът с поръчките се взима от същата JSON услуга, която
    динамичната страница извиква (service.eop.bg/NX1Service.svc/...);
  * четимите от човек полета (начин на възлагане, обект, прогнозна
    стойност, дата) се разчитат от вече рендираната (динамична) страница
    на поръчката чрез DOM;
  * връзките за сваляне на файловете се получават чрез подписан URL.

Първото стартиране прави само „базова моментна снимка“ на текущите
поръчки и НЕ ги отпечатва, за да не изведе цялата дневна история.
След това се отпечатват само новопоявилите се поръчки.

Съхранение в SQLite
-------------------
Всяка НОВА поръчка се записва в базата `eop.db` (таблица `tenders`) до
скрипта. Схемата е една и съща като в `collect_history.py`, за да се трупа
всичко на едно място. Новите записи се вкарват с `enriched = 0`, за да може
по-късно `collect_history.py` да ги обогати (статус + участници).
За всеки запис се пази и `collected_at` — датата и часът, в които е
направена проверката (web query), когато поръчката е открита.

Употреба:
    python3 eop_monitor.py [интервал_в_секунди] [--db ПЪТ_ДО_БАЗАТА]
"""

import argparse
import configparser
import re
import smtplib
import sqlite3
import sys
import time
from datetime import datetime
from email.mime.multipart import MIMEMultipart
from email.mime.text import MIMEText
from pathlib import Path
from zoneinfo import ZoneInfo

from playwright.sync_api import sync_playwright

# Обща схема и номенклатури — същите като в collect_history.py, за да се
# записва в една и съща база (eop.db) без конфликти на схемата.
from collect_history import PROCEDURE_TYPE, TYPE_OF_CONTRACT, CURRENCY, DB_SCHEMA

TODAY_URL = "https://app.eop.bg/today"
SERVICE_URL = "https://service.eop.bg/NX1Service.svc"
LIST_API = SERVICE_URL + "/GetPublishedTendersBySpecified"
DETAIL_API = SERVICE_URL + "/GetPublishedTenderDetails"
SIGNED_URL_API = SERVICE_URL + "/GetSignedUrlByDocumentId"

# Път до SQLite базата, в която се трупат новите поръчки.
DB_PATH = str(Path(__file__).with_name("eop.db"))

# Конфигурационен файл с настройките за известяване по имейл (споделен с web_ui.py).
CONFIG_PATH = str(Path(__file__).with_name("web_ui.cfg"))

TZ = ZoneInfo("Europe/Sofia")

# Търсенето на списъка с „днешните“ поръчки (същото, което използва SPA-то).
TODAY_SEARCH_PARAMETERS = {
    "StartIndex": 1,
    "EndIndex": 50,
    "PropertyFilters": [],
    "SearchText": "",
    "SearchProperty": {
        "PropertyDisplayName": "str_Today_opened",
        "PropertyName": "Status",
        "PropertyValue": "1",
    },
    "OrderAscending": False,
    "OrderColumn": "PublicationDate",
    "Keywords": [],
}


def now_str():
    return datetime.now(TZ).strftime("%Y-%m-%d %H:%M:%S")


def now_iso():
    """ISO дата/час (с часова зона) за запис в базата."""
    return datetime.now(TZ).isoformat(timespec="seconds")


def load_notifications_config():
    """Чете настройките за известяване от web_ui.cfg."""
    defaults = {
        "enabled": False, "keywords": "", "organization": "",
        "object": "", "emails": "",
    }
    if not Path(CONFIG_PATH).exists():
        return defaults
    cfg = configparser.ConfigParser(interpolation=None)
    cfg.read(CONFIG_PATH, encoding="utf-8")
    if "notifications" not in cfg:
        return defaults
    sec = cfg["notifications"]
    return {
        "enabled": sec.getboolean("enabled", False),
        "keywords": sec.get("keywords", "").strip(),
        "organization": sec.get("organization", "").strip(),
        "object": sec.get("object", "").strip(),
        "emails": sec.get("emails", "").strip(),
    }


def load_smtp_config():
    """Чете SMTP настройките от web_ui.cfg."""
    defaults = {"host": "", "port": 587, "username": "", "password": "", "from": "", "use_tls": True}
    if not Path(CONFIG_PATH).exists():
        return defaults
    cfg = configparser.ConfigParser(interpolation=None)
    cfg.read(CONFIG_PATH, encoding="utf-8")
    if "smtp" not in cfg:
        return defaults
    sec = cfg["smtp"]
    return {
        "host": sec.get("host", "").strip(),
        "port": sec.getint("port", 587),
        "username": sec.get("username", "").strip(),
        "password": sec.get("password", "").strip(),
        "from": sec.get("from", "").strip(),
        "use_tls": sec.getboolean("use_tls", True),
    }


def notification_matches(notif, data):
    """Проверява дали поръчка отговаря на условията за известяване.

    Логика: И (AND) за зададените условия; празните полета се игнорират.
    """
    keywords = [k.strip().lower() for k in notif.get("keywords", "").split(",") if k.strip()]
    organization = notif.get("organization", "").strip().lower()
    object_type = notif.get("object", "").strip()

    name = (data.get("name") or "").lower()
    description = (data.get("description") or "").lower()
    org = (data.get("organization") or "").lower()
    obj = (data.get("type_of_contract_label") or data.get("contract_type") or "").strip()

    results = []
    if keywords:
        text = name + " " + description
        results.append(any(k in text for k in keywords))
    if organization:
        results.append(organization in org)
    if object_type:
        results.append(obj == object_type)

    if not results:
        return False  # без зададени условия — няма съвпадение

    return all(results)


def format_value(value, currency):
    """Форматира стойност + валута за имейла."""
    if value is None:
        return "-"
    try:
        s = f"{value:,.2f}".replace(",", " ").replace(".", ",")
    except (TypeError, ValueError):
        s = str(value)
    return f"{s} {currency}".strip() if currency else s


def build_email_body(data):
    """Изгражда текста на имейла за една поръчка."""
    attachments = data.get("attachments") or []
    lines = [
        f"Име: {data.get('name') or '-'}",
        f"Уникален номер: {data.get('special_number') or '-'}",
        f"Възложител: {data.get('organization') or '-'}",
        f"Начин на възлагане: {data.get('procedure_type_label') or data.get('procedure_type') or '-'}",
        f"Обект на поръчката: {data.get('type_of_contract_label') or data.get('contract_type') or '-'}",
        f"Прогнозна стойност: {format_value(data.get('estimated_value'), data.get('currency'))}",
        f"Дата на публикуване: {data.get('publication_date') or '-'}",
        f"Лице за контакт: {data.get('contact_person') or '-'}",
        f"Кратко описание: {(data.get('description') or '-')[:500]}",
        f"URL на поръчката: {data.get('url') or '-'}",
        "",
        "Прикачени файлове:",
    ]
    if attachments:
        for att in attachments:
            name = att.get("name") or "(без име)"
            size = att.get("size") or ""
            url = att.get("url") or ""
            size_txt = f" ({size})" if size else ""
            lines.append(f"  - {name}{size_txt}")
            if url:
                lines.append(f"      {url}")
    else:
        lines.append("  (няма прикачени файлове)")
    return "\n".join(lines)


def send_notification_email(notif, data):
    """Изпраща имейл за съвпадение, ако SMTP е настроен."""
    emails = [e.strip() for e in notif.get("emails", "").split(",") if e.strip()]
    if not emails:
        sys.stderr.write(f"[{now_str()}] Известие: съвпадение, но няма зададени имейл адреси.\n")
        return False
    smtp = load_smtp_config()
    if not smtp["host"] or not smtp["from"]:
        sys.stderr.write(f"[{now_str()}] Известие: липсва SMTP настройка в web_ui.cfg.\n")
        return False

    subject = f"Нова обществена поръчка: {data.get('special_number')} — {data.get('name')}"
    body = build_email_body(data)

    msg = MIMEMultipart()
    msg["From"] = smtp["from"]
    msg["To"] = ", ".join(emails)
    msg["Subject"] = subject
    msg.attach(MIMEText(body, "plain", "utf-8"))

    try:
        server = smtplib.SMTP(smtp["host"], smtp["port"], timeout=30)
        if smtp["use_tls"]:
            server.starttls()
        if smtp["username"]:
            server.login(smtp["username"], smtp["password"])
        server.sendmail(smtp["from"], emails, msg.as_string())
        server.quit()
        return True
    except Exception as exc:
        sys.stderr.write(f"[{now_str()}] Грешка при изпращане на имейл: {exc}\n")
        return False


def parse_wcf_date(value):
    """Разчита дата във формат на WCF: /Date(милисекунди)/."""
    if not value:
        return None
    m = re.search(r"/Date\((-?\d+)\)", value)
    if not m:
        return None
    return datetime.fromtimestamp(int(m.group(1)) / 1000.0, tz=TZ)


def strip_html(text):
    """Премахва HTML таговете и връща чист текст."""
    if not text:
        return ""
    text = re.sub(r"<[^>]+>", " ", text)
    replacements = {
        "&nbsp;": " ", "&amp;": "&", "&quot;": '"', "&ldquo;": "\u201c",
        "&rdquo;": "\u201d", "&bdquo;": "\u201e", "&lsquo;": "\u2018",
        "&rsquo;": "\u2019", "&ndash;": "\u2013", "&mdash;": "\u2014",
        "&hellip;": "\u2026", "&bull;": "\u2022", "&eacute;": "é",
    }
    for k, v in replacements.items():
        text = text.replace(k, v)
    return re.sub(r"\s+", " ", text).strip()


def human_size(num_bytes):
    if not num_bytes:
        return ""
    size = float(num_bytes)
    for unit in ("B", "KB", "MB", "GB"):
        if size < 1024 or unit == "GB":
            if unit == "B":
                return f"{int(size)} {unit}"
            return f"{size:.1f} {unit}"
        size /= 1024
    return f"{size:.1f} GB"


def field_value(page, label):
    """
    Извлича стойност от рендираната страница на поръчката по етикет.
    Структурата в DOM е:
        <div class="...nxcard__body-cell... col-md-4"><p>ЕТИКЕТ</p></div>
        <div class="...col-md-8">СТОЙНОСТ</div>
    """
    try:
        locator = page.locator(
            "xpath=//div[contains(@class,'nxcard__body-cell')]"
            "[.//p[normalize-space()='{0}']]"
            "/following-sibling::*[1]".format(label)
        )
        return re.sub(r"\s+", " ", locator.first.inner_text(timeout=8000)).strip()
    except Exception:
        return ""


def get_today_list(api):
    """Връща списъка с днешните публикувани поръчки (JSON от услугата)."""
    resp = api.post(LIST_API, data={"searchParameters": TODAY_SEARCH_PARAMETERS})
    if resp.status != 200:
        raise RuntimeError(f"HTTP {resp.status} за списъка с поръчки")
    data = resp.json()
    return data.get("CurrentPageResults") or []


def get_details(api, tender_id):
    """Връща структурираните детайли за една поръчка."""
    resp = api.post(DETAIL_API, data={"tenderId": tender_id, "ianaTimeZone": "Europe/Sofia"})
    if resp.status != 200:
        raise RuntimeError(f"HTTP {resp.status} за детайлите на поръчката")
    return resp.json()


def get_download_url(api, document_id):
    """Връща подписан URL за сваляне на документ."""
    resp = api.post(SIGNED_URL_API, data={"documentId": document_id})
    if resp.status != 200:
        return ""
    return resp.json().get("Url") or ""


def init_db(db_path=DB_PATH):
    """Отваря (и при нужда създава) SQLite базата и връща връзка."""
    conn = sqlite3.connect(db_path)
    conn.executescript(DB_SCHEMA)
    conn.commit()
    return conn


def load_existing_numbers(conn):
    """Връща множество от вече записаните уникални номера (за дедупликация)."""
    cur = conn.execute("SELECT special_number FROM tenders")
    return {row[0] for row in cur.fetchall()}


def save_tender(conn, record):
    """
    Записва поръчка в базата (схемата на eop.db). `special_number` е PRIMARY KEY,
    затова дублиращите се записи се пропускат (INSERT OR IGNORE).
    Връща True при нов запис.
    """
    cur = conn.execute(
        """
        INSERT OR IGNORE INTO tenders
            (special_number, tender_id, published_tender_id, name, organization,
             procedure_type, procedure_type_label, type_of_contract,
             type_of_contract_label, estimated_value, currency, publication_date,
             deadline, contact_person, collected_at, enriched)
        VALUES
            (:special_number, :tender_id, :published_tender_id, :name, :organization,
             :procedure_type, :procedure_type_label, :type_of_contract,
             :type_of_contract_label, :estimated_value, :currency, :publication_date,
             :deadline, :contact_person, :collected_at, :enriched)
        """,
        record,
    )
    conn.commit()
    return cur.rowcount > 0


def process_tender(page, api, item, checked_at=None):
    """Зарежда детайлите на нова поръчка, отпечатва полетата и връща dict за запис в базата."""
    tender_id = item.get("TenderId")
    special_number = item.get("SpecialNumber") or "-"
    name = (item.get("TenderName") or "").strip()
    organization = (item.get("OrganizationName") or "").strip()
    description = strip_html(item.get("TenderDescription"))
    published = parse_wcf_date(item.get("PublicationDate"))
    deadline = parse_wcf_date(item.get("Deadline"))

    details = {}
    try:
        details = get_details(api, tender_id)
    except Exception:
        details = {}

    # Лице за контакт — от структурираните данни.
    contact_parts = [
        details.get("ContactPersonDisplayName") or "",
        details.get("ContactPersonEmail") or "",
        details.get("ContactPersonPhone") or "",
    ]
    contact = " / ".join(p for p in contact_parts if p).strip()

    # Четими от човек стойности — от рендираната (динамична) страница.
    procedure_name = ""
    contract_type_name = ""
    estimated_value = ""
    published_display = ""
    try:
        page.goto(f"{TODAY_URL}/{tender_id}", wait_until="domcontentloaded", timeout=60000)
        page.wait_for_timeout(2500)
        procedure_name = field_value(page, "Начин на възлагане / пазарни консултации")
        contract_type_name = field_value(page, "Обект на поръчката")
        estimated_value = field_value(page, "Прогнозна стойност (без ДДС)")
        published_display = field_value(page, "Дата на публикуване")
        if not contact:
            contact = field_value(page, "Лице за контакт")
    except Exception as exc:
        sys.stderr.write(f"[{now_str()}] Предупреждение при зареждане на страницата: {exc}\n")

    # Прикачени файлове + подписани URL за сваляне.
    documents = details.get("TenderDescriptionDocuments") or []
    attachments = []
    for doc in documents:
        doc_id = doc.get("Id")
        file_name = doc.get("Name") or "(без име)"
        file_size = human_size(doc.get("Size"))
        url = ""
        if doc_id:
            try:
                url = get_download_url(api, doc_id)
            except Exception:
                url = ""
        attachments.append((file_name, file_size, url))

    # ---------- Запис в базата (record) ----------
    procedure_type_code = item.get("ProcedureType")
    type_of_contract_code = details.get("TypeOfContract")
    record = {
        "special_number": special_number,
        "tender_id": tender_id,
        "published_tender_id": item.get("Id"),
        "name": name,
        "organization": organization,
        "procedure_type": procedure_type_code,
        "procedure_type_label": PROCEDURE_TYPE.get(procedure_type_code, "") or procedure_name,
        "type_of_contract": type_of_contract_code,
        "type_of_contract_label": TYPE_OF_CONTRACT.get(type_of_contract_code, "") or contract_type_name,
        "estimated_value": details.get("EstimatedValue"),
        "currency": CURRENCY.get(details.get("CurrencyType"), ""),
        "publication_date": published.isoformat(timespec="seconds") if published else "",
        "deadline": deadline.isoformat(timespec="seconds") if deadline else "",
        "contact_person": contact,
        "collected_at": checked_at or now_iso(),
        "enriched": 0,
        # допълнителни полета за имейла (не се записват в базата)
        "description": description,
        "url": f"{TODAY_URL}/{tender_id}",
        "attachments": [{"name": n, "size": s, "url": u} for n, s, u in attachments],
    }

    # ---------- Отпечатване ----------
    line = "=" * 78
    print(line)
    print(f"[НОВА ПОРЪЧКА] {special_number}")
    if published:
        print(f"  Открита на: {published.strftime('%d.%m.%Y %H:%M')}")
    print("-" * 78)
    print(f"Име:                     {name}")
    print(f"Уникален номер:          {special_number}")
    print(f"Възложител:              {organization}")
    print(f"Начин на възлагане:      {procedure_name or '-'}")
    print(f"Обект на поръчката:      {contract_type_name or '-'}")
    print(f"Прогнозна стойност:      {estimated_value or '-'}")
    print(f"Дата на публикуване:     {published_display or (published.strftime('%d.%m.%Y %H:%M') if published else '-')}")
    print(f"Лице за контакт:         {contact or '-'}")
    print(f"Кратко описание:         {description[:500] or '-'}")
    print(f"URL на поръчката:        {TODAY_URL}/{tender_id}")
    print("Прикачени файлове:")
    if attachments:
        for file_name, file_size, url in attachments:
            size_txt = f" ({file_size})" if file_size else ""
            print(f"  - {file_name}{size_txt}")
            if url:
                print(f"      {url}")
    else:
        print("  (няма прикачени файлове)")
    print(line)
    print()
    sys.stdout.flush()

    return record


def main():
    # Отпечатване в реално време дори при пренасочване към файл/лог.
    try:
        sys.stdout.reconfigure(line_buffering=True)
    except Exception:
        pass

    parser = argparse.ArgumentParser(description="Мониторинг на нови обществени поръчки от ЦАИС ЕОП.")
    parser.add_argument("interval", nargs="?", type=int, default=60,
                        help="интервал на проверка в секунди (по подразбиране 60)")
    parser.add_argument("--db", "-d", default=DB_PATH,
                        help="път до SQLite базата (по подразбиране %(default)s)")
    args = parser.parse_args()

    interval = args.interval
    if interval < 5:
        interval = 5
    db_path = args.db

    conn = init_db(db_path)
    seen_numbers = load_existing_numbers(conn)
    first_run = True

    with sync_playwright() as p:
        browser = p.chromium.launch(headless=True)
        context = browser.new_context(locale="bg-BG", timezone_id="Europe/Sofia")
        page = context.new_page()
        api = context.request

        print(f"[{now_str()}] Стартира мониторинг на нови обществени поръчки от {TODAY_URL}")
        print(f"[{now_str()}] База данни: {db_path} (вече записани: {len(seen_numbers)})")
        print(f"[{now_str()}] Интервал на проверка: {interval} секунди. Натиснете Ctrl+C за край.\n")

        try:
            while True:
                try:
                    items = get_today_list(api)
                except Exception as exc:
                    sys.stderr.write(f"[{now_str()}] Грешка при извличане на списъка: {exc}\n")
                    time.sleep(interval)
                    continue

                # Дата/час на тази проверка (web query) — за справка в базата.
                query_time = now_iso()

                new_items = []
                for item in items:
                    sn = item.get("SpecialNumber")
                    if sn and sn not in seen_numbers:
                        seen_numbers.add(sn)
                        new_items.append(item)

                if first_run:
                    first_run = False
                    print(f"[{now_str()}] Базова моментна снимка: {len(items)} поръчки в /today.")
                    print(f"[{now_str()}] Очаквам нови поръчки...\n")
                else:
                    notif = load_notifications_config()
                    saved_count = 0
                    for item in new_items:
                        try:
                            record = process_tender(page, api, item, checked_at=query_time)
                            if save_tender(conn, record):
                                saved_count += 1
                            if notif.get("enabled") and notification_matches(notif, record):
                                if send_notification_email(notif, record):
                                    print(f"[{now_str()}] Изпратен имейл за съвпадение: {record.get('special_number')}.")
                        except Exception as exc:
                            sys.stderr.write(
                                f"[{now_str()}] Грешка при обработка на {item.get('SpecialNumber')}: {exc}\n"
                            )
                    if new_items:
                        print(f"[{now_str()}] Открити {len(new_items)} нови поръчки; записани в базата: {saved_count}.")
                    else:
                        print(f"[{now_str()}] Няма нови поръчки ({len(items)} в /today).")

                time.sleep(interval)

        except KeyboardInterrupt:
            print(f"\n[{now_str()}] Мониторингът е спрян.")
        finally:
            conn.close()


if __name__ == "__main__":
    main()
