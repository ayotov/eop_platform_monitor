#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Събиране на ВСИЧКИ обществени поръчки от ЦАИС ЕОП (исторически архив)
======================================================================

Този скрипт има една-единствена цел: да изтегли информация за всички
публикувани обществени поръчки („Регистър на обществените поръчки“) до
момента — без значение от техния статус — и да ги съхрани в отделна
SQLite база данни `eop_history.db`.

За разлика от `eop_monitor.py` (който следи само новите дневни поръчки),
тук се натрупва пълната история, включително вече приключили поръчки.

Събирани данни за всяка поръчка:
  * уникален номер, име, възложител
  * начин на възлагане, обект на поръчката (вид)
  * прогнозна стойност и валута
  * дата на публикуване, краен срок
  * брой получени оферти, брой обособени позиции
  * СТАТУС на поръчката (Активна / Паузирана / Прекратена / Архивирана /
    Комплексна) — ако има такъв, плюс изведено „приключване“
    (Изпълнена / Възложена / Прекратена)
  * СПИСЪК НА УЧАСТНИЦИТЕ (фирми): име, ЕИК/БУЛСТАТ, предложена цена
  * лице за контакт (име / имейл / телефон)

Как работи
----------
1. Фаза 1 (списък): обхожда регистъра чрез услугата
   `GetPublishedTendersSearchResult` (страница по страница, сортирано по
   TenderId) и записва основните полета за ~136 000 поръчки.
2. Фаза 2 (обогатяване): за всяка поръчка извиква
   `GetPublishedTenderDetails` (статус, форми за публикуване, контакт) и
   `GetPublicTenderParticipation` (участници).

Скриптът е *възобновяем* (resumable): може да се спре и пусне отново —
вече събраните/обогатените записи се пропускат.

Употреба:
    python3 collect_history.py [опции]

Опции:
    --db PATH      път до базата (по подразбиране eop_history.db до скрипта)
    --workers N    брой паралелни заявки при обогатяването (по подразбиране 8)
    --limit N      обогати само първите N поръчки (за тест)
    --skip-enrich  само фаза 1 (списък), без статус/участници
"""

import argparse
import json
import re
import sqlite3
import sys
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime
from pathlib import Path
from zoneinfo import ZoneInfo

import httpx

HOST = "https://service.eop.bg/NX1Service.svc"
SEARCH_API = HOST + "/GetPublishedTendersSearchResult"
DETAIL_API = HOST + "/GetPublishedTenderDetails"
PARTICIPATION_API = HOST + "/GetPublicTenderParticipation"

DEFAULT_DB = str(Path(__file__).with_name("eop_history.db"))
TZ = ZoneInfo("Europe/Sofia")

PAGE_SIZE = 200

# --- Номенклатури (числови кодове -> български текст) ---

# ExplicitTenderStatus (enum TenderStatus)
TENDER_STATUS = {
    0: "",
    1: "Активна",
    2: "Паузирана",
    3: "Прекратена",
    4: "Архивирана",
    5: "Комплексна",
}

# ProcedureType (начин на възлагане)
PROCEDURE_TYPE = {
    0: "Неопределен",
    1: "Частна поръчка",
    2: "Открита процедура",
    3: "Ограничена процедура",
    4: "Състезателна процедура с договаряне",
    5: "Договаряне с предварителна покана",
    6: "Състезателен диалог",
    7: "Партньорство за иновации",
    8: "Ускорена ограничена процедура",
    9: "Договаряне",
    10: "Ускорено договаряне",
    11: "Конкурс за проект",
    12: "Публично състезание",
    13: "Директно възлагане",
    14: "Събиране на оферти с обява",
    15: "Покана до определени лица",
    16: "Мини конкурс в рамково споразумение",
    17: "Квалификационна система",
    18: "Динамична система за покупки",
    25: "Извън обхвата на ЗОП",
    26: "Поръчки по чл. 20, ал. 4, 6 и 8",
}

# TypeOfContract (обект на поръчката)
TYPE_OF_CONTRACT = {
    0: "Неопределен",
    1: "Услуги",
    2: "Доставки",
    3: "Строителство",
}

# CurrencyType -> код
CURRENCY = {
    1: "EUR", 2: "USD", 3: "BGN", 4: "NOK", 5: "GBP", 6: "ISK", 8: "CHF",
    9: "SEK", 10: "JPY", 16: "RON", 17: "CZK", 18: "DKK", 19: "PLN",
    20: "HUF", 21: "MKD", 22: "TRY", 23: "HRK",
}

# Публикационни форми, указващи приключване/възлагане (наблюдавани стойности
# за националните форми по чл. 20 от ЗОП). Пълният списък на формите се пази
# в колоната publication_form_types за последващ анализ.
COMPLETION_FORM_TYPES = {30}   # "Обявление за приключване на договор"
AWARD_FORM_TYPES = {41}        # "Обявление за възлагане ... (по чл. 20)"

DB_SCHEMA = """
CREATE TABLE IF NOT EXISTS tenders (
    special_number             TEXT PRIMARY KEY,
    tender_id                  INTEGER,
    published_tender_id        INTEGER,
    name                       TEXT,
    organization               TEXT,
    procedure_type             INTEGER,
    procedure_type_label       TEXT,
    type_of_contract           INTEGER,
    type_of_contract_label     TEXT,
    estimated_value            REAL,
    currency                   TEXT,
    publication_date           TEXT,
    deadline                   TEXT,
    offer_count                INTEGER,
    lot_count                  INTEGER,
    is_joint_procurement       INTEGER,
    parent_tender_special_number TEXT,
    specialty                  TEXT,
    -- обогатяване (фаза 2)
    explicit_status            INTEGER,
    status                     TEXT,
    outcome                    TEXT,
    publication_form_types     TEXT,
    contact_person             TEXT,
    participants               TEXT,
    participants_count         INTEGER,
    enriched                   INTEGER DEFAULT 0,
    collected_at               TEXT,
    enriched_at                TEXT
);
CREATE INDEX IF NOT EXISTS idx_tenders_tender_id ON tenders(tender_id);
CREATE INDEX IF NOT EXISTS idx_tenders_enriched ON tenders(enriched);
"""


# --- Помощни функции ---

def parse_wcf_date(value):
    """/Date(милисекунди[+часово отместване])/ -> ISO низ в Europe/Sofia."""
    if not value:
        return None
    m = re.search(r"/Date\((-?\d+)", value)
    if not m:
        return None
    dt = datetime.fromtimestamp(int(m.group(1)) / 1000.0, tz=TZ)
    return dt.isoformat(timespec="seconds")


def now_iso():
    return datetime.now(TZ).isoformat(timespec="seconds")


def compute_outcome(explicit_status, form_types):
    """Извежда кратко „приключване“ на поръчката."""
    form_types = set(form_types or [])
    if COMPLETION_FORM_TYPES & form_types:
        return "Изпълнена"
    if explicit_status == 3:
        return "Прекратена"
    if AWARD_FORM_TYPES & form_types:
        return "Възложена"
    if explicit_status == 1:
        return "Активна"
    if explicit_status == 5:
        return "Комплексна"
    return TENDER_STATUS.get(explicit_status, "")


# --- База данни ---

def init_db(db_path):
    conn = sqlite3.connect(db_path)
    conn.executescript(DB_SCHEMA)
    conn.commit()
    return conn


def upsert_list_rows(conn, rows):
    """Вмъква/обновява основните полета от списъка (идемпотентно)."""
    conn.executemany(
        """
        INSERT INTO tenders
            (special_number, tender_id, published_tender_id, name, organization,
             procedure_type, procedure_type_label, type_of_contract,
             type_of_contract_label, estimated_value, currency, publication_date,
             deadline, offer_count, lot_count, is_joint_procurement,
             parent_tender_special_number, specialty, collected_at)
        VALUES
            (:special_number, :tender_id, :published_tender_id, :name, :organization,
             :procedure_type, :procedure_type_label, :type_of_contract,
             :type_of_contract_label, :estimated_value, :currency, :publication_date,
             :deadline, :offer_count, :lot_count, :is_joint_procurement,
             :parent_tender_special_number, :specialty, :collected_at)
        ON CONFLICT(special_number) DO UPDATE SET
             tender_id=excluded.tender_id,
             published_tender_id=excluded.published_tender_id,
             name=excluded.name,
             organization=excluded.organization,
             procedure_type=excluded.procedure_type,
             procedure_type_label=excluded.procedure_type_label,
             type_of_contract=excluded.type_of_contract,
             type_of_contract_label=excluded.type_of_contract_label,
             estimated_value=excluded.estimated_value,
             currency=excluded.currency,
             publication_date=excluded.publication_date,
             deadline=excluded.deadline,
             offer_count=excluded.offer_count,
             lot_count=excluded.lot_count,
             is_joint_procurement=excluded.is_joint_procurement,
             parent_tender_special_number=excluded.parent_tender_special_number,
             specialty=excluded.specialty,
             collected_at=excluded.collected_at
        """,
        rows,
    )
    conn.commit()


def get_unenriched_tender_ids(conn, limit=None):
    q = "SELECT DISTINCT tender_id FROM tenders WHERE enriched=0 AND tender_id IS NOT NULL ORDER BY tender_id"
    if limit:
        q += f" LIMIT {int(limit)}"
    return [r[0] for r in conn.execute(q).fetchall()]


def update_enrichment(conn, tender_id, data):
    conn.execute(
        """
        UPDATE tenders SET
            explicit_status=:explicit_status,
            status=:status,
            outcome=:outcome,
            publication_form_types=:publication_form_types,
            contact_person=:contact_person,
            participants=:participants,
            participants_count=:participants_count,
            enriched=1,
            enriched_at=:enriched_at
        WHERE tender_id=:tender_id
        """,
        {**data, "tender_id": tender_id},
    )
    conn.commit()


# --- API ---

def make_client():
    return httpx.Client(timeout=60, verify=False, limits=httpx.Limits(max_connections=32, max_keepalive_connections=16))


def search_page(client, start, end):
    body = {
        "request": {
            "StartDate": None,
            "EndDate": None,
            "StartIndex": start,
            "EndIndex": end,
            "OrderColumn": "TenderId",
            "OrderAscending": True,
        }
    }
    for _ in range(4):
        try:
            r = client.post(SEARCH_API, json=body)
            if r.status_code == 200:
                return r.json()
            time.sleep(1)
        except Exception:
            time.sleep(2)
    return None


def get_details(client, tender_id):
    for _ in range(3):
        try:
            r = client.post(DETAIL_API, json={"tenderId": tender_id, "ianaTimeZone": "Europe/Sofia"})
            if r.status_code == 200:
                return r.json()
            time.sleep(1)
        except Exception:
            time.sleep(2)
    return None


def get_participation(client, tender_id):
    for _ in range(3):
        try:
            r = client.post(PARTICIPATION_API, json={"tenderId": tender_id, "cultureId": 3, "ianaTimeZone": "Europe/Sofia"})
            if r.status_code == 200:
                return r.json()
            time.sleep(1)
        except Exception:
            time.sleep(2)
    return None


# --- Обработка ---

def row_from_list_item(item):
    pt = item.get("ProcedureType")
    tc = item.get("TypeOfContract")
    return {
        "special_number": item.get("SpecialNumber"),
        "tender_id": item.get("TenderId"),
        "published_tender_id": item.get("PublishedTenderId"),
        "name": (item.get("TenderName") or "").strip(),
        "organization": (item.get("OrganizationName") or "").strip(),
        "procedure_type": pt,
        "procedure_type_label": PROCEDURE_TYPE.get(pt, ""),
        "type_of_contract": tc,
        "type_of_contract_label": TYPE_OF_CONTRACT.get(tc, ""),
        "estimated_value": item.get("EstimatedValue"),
        "currency": CURRENCY.get(item.get("Currency"), ""),
        "publication_date": parse_wcf_date(item.get("PublicationDate")),
        "deadline": parse_wcf_date(item.get("OffersReceivingDeadline")),
        "offer_count": item.get("OfferCount"),
        "lot_count": item.get("LotCount"),
        "is_joint_procurement": 1 if item.get("IsJointProcurement") else 0,
        "parent_tender_special_number": item.get("ParentTenderSpecialNumber"),
        "specialty": json.dumps(item.get("Specialty") or {}, ensure_ascii=False),
        "collected_at": now_iso(),
    }


def extract_participants(participation):
    if not participation:
        return [], 0
    out = []
    seen = set()
    for round_ in participation.get("Rounds") or []:
        for offer in round_.get("Offers") or []:
            name = (offer.get("OrganizationName") or offer.get("OfferName") or "").strip()
            reg = offer.get("RegistryNumber")
            if name and name not in seen:
                seen.add(name)
                out.append({"name": name, "registry_number": reg, "price": offer.get("Price")})
            for member in offer.get("ConsortiumMembers") or []:
                mn = (member.get("OrganizationName") or member.get("RegistryNumber") or "").strip() if isinstance(member, dict) else ""
                mr = member.get("RegistryNumber") if isinstance(member, dict) else None
                if mn and mn not in seen:
                    seen.add(mn)
                    out.append({"name": mn, "registry_number": mr, "price": None, "consortium_member": True})
    return out, len(out)


def enrich_one(client, tender_id):
    details = get_details(client, tender_id)
    participation = get_participation(client, tender_id)

    participants, participants_count = extract_participants(participation)

    explicit_status = None
    status = ""
    form_types = []
    contact = ""
    if details:
        explicit_status = details.get("ExplicitTenderStatus")
        status = TENDER_STATUS.get(explicit_status, "")
        form_types = [p.get("PublicationFormType") for p in (details.get("TenderPublicationDetails") or []) if p.get("PublicationFormType") is not None]
        contact_parts = [
            details.get("ContactPersonDisplayName") or "",
            details.get("ContactPersonEmail") or "",
            details.get("ContactPersonPhone") or "",
        ]
        contact = " / ".join(x for x in contact_parts if x).strip()

    outcome = compute_outcome(explicit_status, form_types)

    return {
        "explicit_status": explicit_status,
        "status": status,
        "outcome": outcome,
        "publication_form_types": json.dumps(form_types, ensure_ascii=False),
        "contact_person": contact,
        "participants": json.dumps(participants, ensure_ascii=False),
        "participants_count": participants_count,
        "enriched_at": now_iso(),
    }


# --- Главен поток ---

def collect_list(conn, client, limit=None):
    print("[фаза 1] Събиране на списъка с всички публикувани поръчки...")
    first = search_page(client, 1, 1)
    if not first:
        print("  Грешка: не мога да получа общия брой.")
        return
    total = first.get("ResultsCount") or 0
    if limit:
        total = min(total, int(limit))
    print(f"  Общ брой поръчки в регистъра: {first.get('ResultsCount')} (събирам {total})")

    collected = 0
    start = 1
    while start <= total:
        end = min(start + PAGE_SIZE - 1, total)
        data = search_page(client, start, end)
        if not data:
            print(f"  Грешка при страница {start}-{end}; опитвам отново...")
            time.sleep(3)
            continue
        items = data.get("CurrentPageResults") or []
        rows = [row_from_list_item(it) for it in items if it.get("SpecialNumber")]
        if rows:
            upsert_list_rows(conn, rows)
            collected += len(rows)
        print(f"  ... записани {collected}/{total} (страница {start}-{end})", end="\r")
        start = end + 1
    print()
    print(f"[фаза 1] Готово. Записани {collected} поръчки.")


def enrich(conn, client, workers, limit):
    ids = get_unenriched_tender_ids(conn, limit)
    total = len(ids)
    if not total:
        print("[фаза 2] Няма поръчки за обогатяване.")
        return
    print(f"[фаза 2] Обогатяване (статус + участници) на {total} поръчки с {workers} работни процеса...")

    done = 0
    errors = 0
    with ThreadPoolExecutor(max_workers=workers) as pool:
        futures = {pool.submit(enrich_one, client, tid): tid for tid in ids}
        for fut in as_completed(futures):
            tid = futures[fut]
            try:
                data = fut.result()
                update_enrichment(conn, tid, data)
                done += 1
            except Exception:
                errors += 1
            if (done + errors) % 100 == 0:
                print(f"  ... обработени {done + errors}/{total} (грешки: {errors})", end="\r")
    print()
    print(f"[фаза 2] Готово. Обогатени {done}, грешки {errors}.")


def main():
    ap = argparse.ArgumentParser(description="Събиране на всички обществени поръчки от ЦАИС ЕОП.")
    ap.add_argument("--db", default=DEFAULT_DB, help="път до SQLite базата")
    ap.add_argument("--workers", type=int, default=8, help="брой паралелни заявки при обогатяване")
    ap.add_argument("--limit", type=int, default=None, help="обогати само първите N поръчки")
    ap.add_argument("--list-limit", type=int, default=None, help="събери само първите N поръчки от списъка (за тест)")
    ap.add_argument("--skip-enrich", action="store_true", help="само фаза 1 (списък)")
    args = ap.parse_args()

    conn = init_db(args.db)
    client = make_client()

    try:
        collect_list(conn, client, args.list_limit)
        if not args.skip_enrich:
            enrich(conn, client, args.workers, args.limit)

        n_total = conn.execute("SELECT COUNT(*) FROM tenders").fetchone()[0]
        n_enriched = conn.execute("SELECT COUNT(*) FROM tenders WHERE enriched=1").fetchone()[0]
        print(f"База данни: {args.db}")
        print(f"  Поръчки: {n_total}, обогатени (статус+участници): {n_enriched}")
    finally:
        client.close()
        conn.close()


if __name__ == "__main__":
    main()
