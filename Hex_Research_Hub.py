#!/usr/bin/env python3
"""
 Hex Research Hub

A dependency-free, terminal-first research system that coordinates specialist
teams to discover, triage, and write standalone summaries for education and
science findings.

Examples:
    python education_research_hub.py
    python education_research_hub.py --interval 6
    python education_research_hub.py build --topic "biology" --topic "algebra"

The program uses public endpoints when available:
Wikipedia's full-text search, Crossref, OpenAlex, arXiv, and the Semantic
Scholar API. It never needs an API key. Network failures are reported per
source and do not discard other results.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import collections
import dataclasses
import datetime as dt
import hashlib
import html
import http.server
import json
import os
import re
import shutil
import sqlite3
import subprocess
import sys
import textwrap
import threading
import time
import traceback
import urllib.parse
import urllib.error
import urllib.request
import webbrowser
import xml.etree.ElementTree as ET
from pathlib import Path
from typing import Any, Iterable, Sequence


APP_NAME = "Hex"
VERSION = "1.4"
SCRIPT_DIR = Path(__file__).resolve().parent
DEFAULT_OUTPUT = "Hex_Research_Library"
USER_AGENT = "HexResearchHub/1.4 (scholarly research organizer)"
WIKIPEDIA_API = "https://en.wikipedia.org/w/api.php"
WIKIPEDIA_LOGO_DATA_URI = "data:image/png;base64," + """
iVBORw0KGgoAAAANSUhEUgAAAGAAAAA2CAMAAAAPkWzgAAAAk1BMVEWtra+JiouVlpjQ0NFTUlOmpqiLjI6trrCmp6l+foCxsbOGhoiwsbOrrK6YmJpQTk+I
h4mBgYPY2dpfXl+MjI7f3+BcW1xUUlOYmZt6eXu6u73X2Nmur7GnqKnGx8m+v8CXl5mfoKOdnqHOz9Df3+DP0NGOj5Fqamp3dnjn5+i/wMK3t7nv7/Dv8PDz
8/Sgn6DAv8AxMNymAAAAG3RSTlMALxStSxiS0Sdo5qX+cPS8/vrP3M/q/fHW7+86+W8LAAAFXUlEQVRYw61Yi3KbOhCNAUOaYEduUje5elhBSKBIuP3/r+vu
CozTmTsDTnecGTsen6Pdsy9xd/cl22y+9vu7LM/z4n++2m6ysqqKdYB/2X3OubiG2H4r6cxZUVYPsnyUtSy/4MSuUqour09dcV5m210OXyh1qvdCv4vm6Vb8
Uigjd9m1R1XL1YOy1ipiOLmu75zc3YhvpPd2dgDDwj1AW26tIYYP1vfdQVb3t+Bvv/MQfZgV+OZj9FZqrVXgwBACBLDrey3k4w0Mm8oDoK3m/xTwOSrtg5QC
CE7kg+x1LaSsyrX4GeCD1VcptPU8r7z1MgTJJxVCCLUQQu5XpmuWI3xsJwdI6bIsSu5b5bnhPKnwgQR1ELJ5zlYRlADPffRVib8rnp4K1PhlL5CXoyUXTuBD
LepaSr0qlbIfgCP5EAcOv9scu+7p6WfHODhFkUOOMZHIBaF187pG6JLLIAIkTVRI8NyRMT/EC4E1ow/III/9+xoXsgcOmeKj3e9fi6Ic8bv+mmDyIcncd1qv
UKGAUHA7eHkE6y7W8/NEQD5YdUoxamRz1M2KREopFC3rPluY4U2tuAqn5AIUQ+8avbgWsgciGNTh6vRMy2AjmudQakECwSVGugMP9POKCGHRDqqHRgDNputc
4H44n70fhuh/McO0rS1XBvpFKgUJptnSxv3Np3S0J+hr3LCuN2cyIoieSduFAN+QAEQgkMAtFSGPAISdbUBU8KNz9O48tEgQOQu/eglpBOdXHxgi6BXvcrkI
eVQKJBgSgYT4K0RHbYkgmh6EbXnq2gFqGUr5vWnc42KNBTPDRBAtj4jPSXgkgPKzvuUTARqEqNFuocrZdy+0RBlSYCLnJDCyJAJKVAA3EwFpwNjLslK7/wEt
n85L+KpW2vkzfhpmAqpkZTFJT4nA9UsJoNNJZzAc6AHv/Tl28hyBo00xok7rKYumdgcEbDHB/UiQGEIPLNqdCT7yGGcCa4y59NMVBKCBCRRnJOAdBF8H1AJ1
bycJ/GUmhJSnQLC0lCuqZBQZGAYhvdXSjhLzSQIkULIehxrUATssJsipkpECCLzua8s0J4WBAOEhReFPmXCURICd4l0zt3QDy6MffUDI8NufBzx+Orpv2xbf
     qN5xdXTU7OpUBm5pJe9SSwZATMrUJCZOfmnYrrcQ908ES3vR5sc0U/yo9eCTNzMB53UHXbs7qbEVAf7r4jW4UoKntQJzFRmSM58IID4fIAL2OpkcWDwPYCsN
aiIgKQB4LgCsAMzRjqngaoyQbGChdG751N8oOBOBxan1+EsP4ilFYU64cZ7B2tVofXhbcVHIrXD8GpiydgzOuBbNfYIi9NqtuSYUJmjsBi3pHIP0OoR5n+Dz
3lVTCr03MJVXbacVJxXGriM1xvgzvlXUh+o65Shb5QC4YGGN/kTA9IR/GTVzDUAOdSvX65xP8QZzrpbuYK52unF7T/hwJXH92gvC9uGKIGghNAuc2pCh81N8
oIHSOgEEz6vvODszExi8DYbfNqWnRUMCefx5xPhDCbAbrstlUpO3/q/0UXba6ITu0vnZ6hsUyWBTySaa6c248pK+NRBgjS1uo58texQKIz6ZsaTuvC/iFCP8
W2/i2aOEvcHOZ7fT/fiUxjCG5+bzJx0kLIc2IZsxd+Y9AseY1rfFf7LiDaauwe1BaySD6GDzEQkfwqNfvva45W77GNSJLjISNixBwwVfhO8Oh6evPjACJyrc
3ZRopKy1o+YjBMGzw/MXj58s21X/4dhyTjuN8GN0/hF88qKsZHpoAPcAgt+/lv8OntwodmVV7ffs7Y1Vz+WuWPfkYKHdbzdFsdmswv4DCAo3YEpDTbEAAAAA
SUVORK5CYII=
""".replace("\n", "").replace(" ", "")
REQUIREMENTS_FILE = Path(__file__).with_name("requirements.txt")
DEFAULT_INTERVAL_HOURS = 6.0
DEFAULT_TOPIC_CONCURRENCY = 4
DEFAULT_WIKIPEDIA_BATCH = 500
WIKIPEDIA_ARTICLE_CHARS = 32000
# Scholarly APIs often return useful methods, populations, and caveats after
# the first sentence. Keep enough of each abstract for the written finding to
# teach instead of reducing it to a headline.
SCHOLARLY_SUMMARY_CHARS = 6000
# How long a cached API response stays valid before Hex re-requests it.
# Scholarly metadata barely changes day to day, so a generous cache means a
# rotating topic catalog stops re-hitting OpenAlex/Crossref/etc. for queries
# it already has a good answer for.
CACHE_TTL_SECONDS = {
    "OpenAlex": 14 * 24 * 60 * 60,
    "Crossref": 14 * 24 * 60 * 60,
    "Semantic Scholar": 14 * 24 * 60 * 60,
    "arXiv": 7 * 24 * 60 * 60,
    "Wikipedia": 3 * 24 * 60 * 60,
}
DEFAULT_CACHE_TTL_SECONDS = 7 * 24 * 60 * 60
WIKIPEDIA_PARTITIONS: tuple[tuple[str, str], ...] = (
    ("", "D"),
    ("D", "H"),
    ("H", "L"),
    ("L", "P"),
    ("P", "T"),
    ("T", "Z"),
    ("Z", ""),
)

# The autonomous catalog is intentionally broad. It gives the coordinator a
# standing mission without requiring a human to supply a topic first.
AUTONOMOUS_TOPICS: tuple[str, ...] = (
    "reading and literacy education",
    "mathematics education",
    "science education",
    "history education",
    "language learning",
    "special education",
    "early childhood education",
    "higher education",
    "adult learning",
    "educational psychology",
    "curriculum design",
    "assessment and evaluation",
    "climate science",
    "biology",
    "chemistry",
    "physics",
    "earth and environmental science",
    "astronomy and space science",
    "public health",
    "medicine",
    "psychology",
    "nutrition",
    "computer science",
    "artificial intelligence",
    "data science",
    "cybersecurity",
    "engineering",
    "renewable energy",
    "economics",
    "sociology",
    "history",
    "philosophy",
    "law and public policy",
    "communication",
    "business and management",
    "skilled trades",
    "agriculture",
    "architecture and design",
)


def resolve_output_path(value: str | os.PathLike[str]) -> Path:
    """Keep default/relative output next to the copy of Hex being run.

    This avoids accidentally writing into a similarly named folder left by an
    older ZIP or by the terminal's current working directory. Absolute paths
    supplied with --output remain fully under the user's control.
    """
    path = Path(value).expanduser()
    return path if path.is_absolute() else SCRIPT_DIR / path


def install_startup_dependencies() -> None:
    """Install local requirements before any optional features are used.

    The core hub intentionally uses only Python's standard library. If a user
    adds packages to requirements.txt for an extension, the same file remains
    runnable with one command: missing/upgraded packages are handled at start.
    """
    if os.environ.get("EDU_HUB_SKIP_INSTALL") == "1" or not REQUIREMENTS_FILE.exists():
        return
    requirements = [
        line.strip()
        for line in REQUIREMENTS_FILE.read_text(encoding="utf-8").splitlines()
        if line.strip() and not line.lstrip().startswith("#")
    ]
    if not requirements:
        return
    print(f"Installing {len(requirements)} startup dependenc{'y' if len(requirements) == 1 else 'ies'}...")
    try:
        subprocess.run(
            [
                sys.executable,
                "-m",
                "pip",
                "install",
                "--disable-pip-version-check",
                "--no-input",
                "-r",
                str(REQUIREMENTS_FILE),
            ],
            check=True,
        )
    except FileNotFoundError as exc:
        raise RuntimeError("Python could not run pip. Install pip, then start the hub again.") from exc
    except subprocess.CalledProcessError as exc:
        raise RuntimeError(
            f"Startup dependency installation failed with exit code {exc.returncode}. "
            f"Check {REQUIREMENTS_FILE.name} and run again."
        ) from exc


class Ink:
    """Small ANSI palette, with a clean no-color fallback for pipes/files."""

    RESET = "\033[0m"
    DIM = "\033[2m"
    BOLD = "\033[1m"
    CYAN = "\033[96m"
    BLUE = "\033[94m"
    GREEN = "\033[92m"
    YELLOW = "\033[93m"
    MAGENTA = "\033[95m"
    RED = "\033[91m"
    WHITE = "\033[97m"

    @classmethod
    def enabled(cls) -> bool:
        return sys.stdout.isatty() and os.environ.get("NO_COLOR") is None

    @classmethod
    def paint(cls, text: str, color: str) -> str:
        return f"{color}{text}{cls.RESET}" if cls.enabled() else text


def now_utc() -> dt.datetime:
    return dt.datetime.now(dt.timezone.utc)


def slugify(value: str) -> str:
    clean = re.sub(r"[^a-z0-9]+", "-", value.lower()).strip("-")
    return clean[:70] or "untitled-research"


def entry_filename(title: str) -> str:
    """Create a readable filename while preserving the finding's title."""
    clean = re.sub(r"[\x00-\x1f/\\]", "-", title)
    clean = re.sub(r"\s+", " ", clean).strip(" .")
    return (clean[:140].rstrip(" .") or "Untitled finding") + ".md"


def compact(value: str, length: int = 220) -> str:
    value = re.sub(r"\s+", " ", html.unescape(value or "")).strip()
    return value if len(value) <= length else value[: length - 1].rstrip() + "…"


def format_summary(
    value: str,
    title: str = "",
    source: str = "",
    record_type: str = "",
    venue: str = "",
) -> str:
    """Turn a source extract into a longer, standalone educational summary.

    Every section is built from the source text itself so the reader learns
    the actual substance of the finding here, without needing to open the
    original article. Nothing is invented beyond what the abstract states.
    """
    text = re.sub(r"\s+", " ", html.unescape(value or "")).strip()
    label = record_type or "source"
    source_label = source or venue or "the source"
    title_label = title or "this finding"
    if not text:
        return (
            "### Plain-language explanation\n\n"
            f"This {label} is titled **{title_label}**, but {source_label} did not provide enough "
            "abstract text to summarize its content here."
        )

    sentences = [
        sentence.strip()
        for sentence in re.split(r"(?<=[.!?])\s+(?=[A-Z0-9(])", text)
        if sentence.strip()
    ]
    core = " ".join(sentences[:4])
    supporting = " ".join(sentences[4:20])
    further_detail = " ".join(sentences[20:48])
    extended_detail = " ".join(sentences[48:])
    if not supporting:
        supporting = (
            "The available extract is brief, covering little beyond the plain-language explanation "
            "above."
        )

    return "\n\n".join(
        [
            "### Plain-language explanation\n\n"
            f"This {label} is about **{title_label}**. In everyday terms, {core}",
            "### What this teaches\n\n"
            f"{supporting}",
            *(
                [
                    "### Further detail from the source\n\n"
                    f"{further_detail}"
                ]
                if further_detail
                else []
            ),
            *(
                [
                    "### Extended source context\n\n"
                    f"{extended_detail}"
                ]
                if extended_detail
                else []
            ),
        ]
    )


def iso_date(value: str | None) -> str:
    if not value:
        return "n.d."
    match = re.search(r"\d{4}(?:-\d{2})?(?:-\d{2})?", value)
    return match.group(0) if match else "n.d."


def normalize_title(value: str) -> str:
    return re.sub(r"[^a-z0-9]+", " ", value.lower()).strip()


STOP_WORDS = {
    "and", "the", "for", "with", "from", "into", "about", "education",
    "science", "study", "studies", "learning", "research", "design",
}


def topic_keywords(topic: str) -> set[str]:
    return {
        word for word in re.findall(r"[a-z0-9]{3,}", topic.lower())
        if word not in STOP_WORDS
    }


def matching_topics(record: SourceRecord, topics: Sequence[str]) -> list[str]:
    """Attach a crawled article to every standing subject it genuinely fits.

    Stopword-stripping in topic_keywords() collapses phrases like "adult
    learning" or "computer science" down to a single generic leftover word
    ("adult", "computer"). A lone hit on a word that common is not evidence
    of relevance -- it just means some unrelated article happened to use
    that word once. So a single-keyword topic now requires the topic's
    actual wording to appear together (a phrase hit), not just one of its
    remaining words in isolation. Multi-keyword topics can still match on
    keyword overlap, since two or more distinct topic words showing up
    together is a much stronger signal.
    """
    searchable_title = normalize_title(record.title)
    searchable_body = normalize_title(
        " ".join((record.abstract, record.venue, *record.tags))
    )
    matches: list[str] = []
    for topic in topics:
        keywords = topic_keywords(topic)
        if not keywords:
            continue
        topic_phrase = normalize_title(topic)
        phrase_hit = bool(topic_phrase) and (
            topic_phrase in searchable_title or topic_phrase in searchable_body
        )
        title_hits = sum(int(keyword in searchable_title) for keyword in keywords)
        body_hits = sum(int(keyword in searchable_body) for keyword in keywords)
        if phrase_hit:
            matches.append(topic)
        elif len(keywords) >= 2 and (title_hits >= 2 or body_hits >= len(keywords)):
            matches.append(topic)
        # Topics that reduce to a single leftover keyword never match on
        # that one word alone anymore -- they need the full phrase hit above.
    return matches


def unique(values: Iterable[str]) -> list[str]:
    seen: set[str] = set()
    result: list[str] = []
    for value in values:
        if value and value not in seen:
            seen.add(value)
            result.append(value)
    return result


@dataclasses.dataclass(frozen=True)
class SourceRecord:
    title: str
    abstract: str
    authors: tuple[str, ...]
    year: str
    venue: str
    url: str
    doi: str
    source: str
    record_type: str
    tags: tuple[str, ...] = ()
    score: float = 0.0

    @property
    def stable_id(self) -> str:
        key = self.doi.lower().strip() or normalize_title(self.title)
        return hashlib.sha1(key.encode("utf-8")).hexdigest()[:12]

    def as_dict(self) -> dict[str, Any]:
        return {
            "id": self.stable_id,
            "title": self.title,
            "abstract": self.abstract,
            "authors": list(self.authors),
            "year": self.year,
            "venue": self.venue,
            "url": self.url,
            "doi": self.doi,
            "source": self.source,
            "type": self.record_type,
            "tags": list(self.tags),
            "score": round(self.score, 3),
        }


class ResearchCorpus:
    """Persistent, concurrent-safe corpus for millions of harvested records."""

    def __init__(self, output: Path) -> None:
        output.mkdir(parents=True, exist_ok=True)
        self.path = output / "research_corpus.sqlite3"
        self.lock = ResearchCorpus._global_lock
        self._initialize()

    _global_lock = threading.Lock()

    def _connect(self) -> sqlite3.Connection:
        connection = sqlite3.connect(self.path, timeout=30)
        connection.execute("PRAGMA journal_mode=WAL")
        connection.execute("PRAGMA synchronous=NORMAL")
        return connection

    def _initialize(self) -> None:
        with self._connect() as connection:
            connection.executescript(
                """
                CREATE TABLE IF NOT EXISTS records (
                    record_id TEXT PRIMARY KEY,
                    title TEXT NOT NULL,
                    abstract TEXT NOT NULL,
                    authors_json TEXT NOT NULL,
                    year TEXT NOT NULL,
                    venue TEXT NOT NULL,
                    url TEXT NOT NULL,
                    doi TEXT NOT NULL,
                    source TEXT NOT NULL,
                    record_type TEXT NOT NULL,
                    tags_json TEXT NOT NULL,
                    score REAL NOT NULL,
                    first_seen TEXT NOT NULL,
                    last_seen TEXT NOT NULL
                );
                CREATE TABLE IF NOT EXISTS record_topics (
                    record_id TEXT NOT NULL,
                    topic TEXT NOT NULL,
                    first_seen TEXT NOT NULL,
                    last_seen TEXT NOT NULL,
                    PRIMARY KEY (record_id, topic),
                    FOREIGN KEY (record_id) REFERENCES records(record_id)
                );
                CREATE TABLE IF NOT EXISTS wikipedia_cursors (
                    topic TEXT NOT NULL,
                    team_key TEXT NOT NULL,
                    next_cursor TEXT NOT NULL DEFAULT '',
                    next_offset INTEGER NOT NULL DEFAULT 0,
                    total_hits INTEGER NOT NULL DEFAULT 0,
                    pages_harvested INTEGER NOT NULL DEFAULT 0,
                    last_run TEXT NOT NULL,
                    PRIMARY KEY (topic, team_key)
                );
                CREATE INDEX IF NOT EXISTS records_source_idx ON records(source);
                CREATE INDEX IF NOT EXISTS record_topics_topic_idx ON record_topics(topic);
                """
            )
            columns = {
                row[1] for row in connection.execute("PRAGMA table_info(wikipedia_cursors)").fetchall()
            }
            if "next_cursor" not in columns:
                connection.execute(
                    "ALTER TABLE wikipedia_cursors ADD COLUMN next_cursor TEXT NOT NULL DEFAULT ''"
                )

    def upsert(self, records: Sequence[SourceRecord], topic: str | Sequence[str]) -> int:
        if not records:
            return 0
        topics = [topic] if isinstance(topic, str) else list(topic)
        topics = unique(topics)
        timestamp = now_utc().isoformat()
        inserted = 0
        with self.lock, self._connect() as connection:
            for record in records:
                record_id = f"{record.source}:{record.stable_id}"
                exists = connection.execute(
                    "SELECT 1 FROM records WHERE record_id = ?", (record_id,)
                ).fetchone()
                connection.execute(
                    """
                    INSERT INTO records (
                        record_id, title, abstract, authors_json, year, venue, url,
                        doi, source, record_type, tags_json, score, first_seen, last_seen
                    ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
                    ON CONFLICT(record_id) DO UPDATE SET
                        title=excluded.title,
                        abstract=excluded.abstract,
                        authors_json=excluded.authors_json,
                        year=excluded.year,
                        venue=excluded.venue,
                        url=excluded.url,
                        doi=excluded.doi,
                        record_type=excluded.record_type,
                        tags_json=excluded.tags_json,
                        score=excluded.score,
                        last_seen=excluded.last_seen
                    """,
                    (
                        record_id,
                        record.title,
                        record.abstract,
                        json.dumps(record.authors, ensure_ascii=False),
                        record.year,
                        record.venue,
                        record.url,
                        record.doi,
                        record.source,
                        record.record_type,
                        json.dumps(record.tags, ensure_ascii=False),
                        record.score,
                        timestamp,
                        timestamp,
                    ),
                )
                for topic_name in topics:
                    connection.execute(
                        """
                        INSERT INTO record_topics (record_id, topic, first_seen, last_seen)
                        VALUES (?, ?, ?, ?)
                        ON CONFLICT(record_id, topic) DO UPDATE SET last_seen=excluded.last_seen
                        """,
                        (record_id, topic_name, timestamp, timestamp),
                    )
                inserted += int(exists is None)
        return inserted

    def wikipedia_state(self, topic: str, team_key: str) -> tuple[str, int, int]:
        with self.lock, self._connect() as connection:
            row = connection.execute(
                """
                SELECT next_cursor, total_hits, pages_harvested
                FROM wikipedia_cursors WHERE topic = ? AND team_key = ?
                """,
                (topic, team_key),
            ).fetchone()
        return tuple(row) if row else ("", 0, 0)

    def save_wikipedia_state(
        self,
        topic: str,
        team_key: str,
        next_cursor: str,
        total_hits: int,
        pages_harvested: int,
    ) -> None:
        timestamp = now_utc().isoformat()
        with self.lock, self._connect() as connection:
            connection.execute(
                """
                INSERT INTO wikipedia_cursors
                    (topic, team_key, next_cursor, next_offset, total_hits, pages_harvested, last_run)
                VALUES (?, ?, ?, 0, ?, ?, ?)
                ON CONFLICT(topic, team_key) DO UPDATE SET
                    next_cursor=excluded.next_cursor,
                    next_offset=excluded.next_offset,
                    total_hits=excluded.total_hits,
                    pages_harvested=excluded.pages_harvested,
                    last_run=excluded.last_run
                """,
                (topic, team_key, next_cursor, total_hits, pages_harvested, timestamp),
            )

    def count(self, topic: str | None = None) -> int:
        with self.lock, self._connect() as connection:
            if topic:
                row = connection.execute(
                    "SELECT COUNT(*) FROM record_topics WHERE topic = ?", (topic,)
                ).fetchone()
            else:
                row = connection.execute("SELECT COUNT(*) FROM records").fetchone()
        return int(row[0] if row else 0)

    def top_records(self, topic: str, limit: int = 300) -> list[SourceRecord]:
        with self.lock, self._connect() as connection:
            rows = connection.execute(
                """
                SELECT r.title, r.abstract, r.authors_json, r.year, r.venue, r.url,
                       r.doi, r.source, r.record_type, r.tags_json, r.score
                FROM records r
                JOIN record_topics rt ON rt.record_id = r.record_id
                WHERE rt.topic = ?
                ORDER BY r.score DESC, r.year DESC, r.title ASC
                LIMIT ?
                """,
                (topic, limit),
            ).fetchall()
        return [
            SourceRecord(
                title=row[0],
                abstract=row[1],
                authors=tuple(json.loads(row[2])),
                year=row[3],
                venue=row[4],
                url=row[5],
                doi=row[6],
                source=row[7],
                record_type=row[8],
                tags=tuple(json.loads(row[9])),
                score=row[10],
            )
            for row in rows
        ]


@dataclasses.dataclass(frozen=True)
class AgentTeam:
    key: str
    name: str
    domain: str
    mission: str
    lenses: tuple[str, ...]


TEAMS: tuple[AgentTeam, ...] = (
    AgentTeam("education", "Learning Sciences", "education", "Find evidence about how people learn, teach, assess, and retain knowledge.", ("pedagogy", "learning", "assessment")),
    AgentTeam("stem", "STEM Discovery", "science", "Find foundational and current scientific work across the natural and physical sciences.", ("biology", "chemistry", "physics", "earth science")),
    AgentTeam("computing", "Computing & AI", "technology", "Find research, methods, and explainers in computing, data, and artificial intelligence.", ("computer science", "machine learning", "data science")),
    AgentTeam("health", "Health & Human Performance", "health", "Find reputable evidence about health, medicine, psychology, and human performance.", ("public health", "medicine", "psychology")),
    AgentTeam("society", "Society & Humanities", "humanities", "Find scholarship that explains people, culture, history, economics, and institutions.", ("history", "sociology", "economics", "culture")),
    AgentTeam("curriculum", "Curriculum Studio", "education", "Turn discoveries into age-appropriate teaching sequences, key terms, and questions.", ("curriculum", "explanation", "learning design")),
    AgentTeam("factcheck", "Evidence Desk", "quality", "Audit provenance, dates, study type, limitations, and citation completeness.", ("verification", "limitations", "source quality")),
)


def conversationalize(agent: str, detail: str, turn: int) -> tuple[str, str]:
    """Turn operational events into natural research-room dialogue."""
    voices = {
        "Crossref": "Maya · Evidence",
        "OpenAlex": "Jonah · Discovery",
        "Semantic Scholar": "Priya · Methods",
        "arXiv": "Noah · Frontier",
        "Wikipedia": "Lena · Context",
        "Learning Sciences": "Maya · Learning",
        "STEM Discovery": "Jonah · Science",
        "Computing & AI": "Noah · Computing",
        "Health & Human Performance": "Priya · Health",
        "Society & Humanities": "Iris · Society",
        "Curriculum Studio": "Maya · Curriculum",
        "Evidence Desk": "Priya · Evidence",
        "Queued": "Coordinator",
        "Scheduler": "Coordinator",
        "Research loop": "Coordinator",
        "Autonomous mode": "Coordinator",
    }
    speaker = voices.get(agent, agent)
    number = re.search(r"(\d[\d,]*)", detail)
    count = number.group(1) if number else ""
    source = agent.lower()
    if "candidate entr" in detail.lower():
        lines = [
            f"I've got {count} leads from {agent}. The first pass is promising, but I'm not calling them findings yet.",
            f"{count} possibilities came back through {agent}. I'm looking for signal, not just volume.",
            f"I pulled {count} relevant-looking entries from {agent}. Someone should challenge the weak ones before we keep them.",
        ]
        text = lines[turn % len(lines)]
        if turn % 3 == 0:
            text += " I suspect a few are duplicates."
    elif "unavailable" in detail.lower() or "failed" in detail.lower():
        text = f"{agent} is not answering right now. I'm keeping the room moving and treating that source as unconfirmed."
    elif "queued" in source:
        text = f"{detail}. I'll hold the thread open while the researchers compare what they find."
    elif "crawler" in source:
        text = f"{detail}. I'm widening the search, but I don't want breadth to flatten the important distinctions."
    elif "deduplicat" in detail.lower() or "evidence" in source:
        text = f"{detail}. I agree with the direction, but let's keep the original wording attached so the summary doesn't overclaim."
    else:
        text = detail.rstrip(".")
        if turn % 2:
            text += ". I'm checking whether that actually changes our understanding."
        else:
            text += ". I want another perspective before we treat it as settled."
    return speaker, text


def dialogue_reply(agent: str, detail: str, turn: int) -> tuple[str, str]:
    """Give the room a second voice that can agree, question, or redirect."""
    replies = (
        ("Priya · Methods", "I hear you, but a promising lead is not evidence by itself. What would make this trustworthy?"),
        ("Jonah · Discovery", "That's fair. I found the same thread from another angle, so I think it deserves a closer look."),
        ("Maya · Learning", "Both points matter. Let's keep the explanation human without sanding away the uncertainty."),
        ("Lena · Context", "I want to slow us down here. Context changes the meaning, and the summary should show that rather than hide it."),
        ("Noah · Frontier", "I disagree slightly. The pattern is interesting, but we should test whether it is genuinely new or just better indexed."),
    )
    speaker, response = replies[turn % len(replies)]
    if "unavailable" in detail.lower() or "failed" in detail.lower():
        response = "Then we mark that gap clearly. I would rather leave a blank than make a confident claim from a missing source."
    return speaker, response


class DashboardState:
    """Thread-safe state shared by the local browser dashboard."""

    def __init__(self) -> None:
        self.lock = threading.Lock()
        self.started_at = now_utc().isoformat()
        self.topic = "Preparing research session"
        self.sequence = 0
        self.dialogue_turn = 0
        self.messages: collections.deque[dict[str, Any]] = collections.deque(maxlen=300)
        self.files: collections.deque[dict[str, Any]] = collections.deque(maxlen=120)
        self.file_sequence = 0
        self.stats = {"messages": 0, "candidates": 0, "files": 0}
        self.agents = {
            team.name: {
                "name": team.name,
                "domain": team.domain,
                "mission": team.mission,
                "status": "standby",
                "last": "Waiting for assignment",
            }
            for team in TEAMS
        }
        self.agents["Coordinator"] = {
            "name": "Coordinator",
            "domain": "orchestration",
            "mission": "Routes research work and keeps the evidence trail organized.",
            "status": "standby",
            "last": "Waiting for assignment",
        }

    def set_topic(self, topic: str) -> None:
        with self.lock:
            if topic:
                self.topic = topic

    def publish(self, kind: str, agent: str, text: str, topic: str = "") -> None:
        with self.lock:
            original_text = text
            if kind == "agent":
                self.dialogue_turn += 1
                turn = self.dialogue_turn
                agent, text = conversationalize(agent, text, turn)
            self.sequence += 1
            if topic:
                self.topic = topic
            message = {
                "id": self.sequence,
                "kind": kind,
                "agent": agent,
                "text": text,
                "topic": topic or self.topic,
                "time": now_utc().strftime("%H:%M:%S"),
            }
            self.messages.append(message)
            self.stats["messages"] += 1
            candidate_match = re.search(r"(\d[\d,]*) candidate entries", original_text)
            file_match = re.search(r"(\d[\d,]*) files", original_text)
            if candidate_match:
                self.stats["candidates"] += int(candidate_match.group(1).replace(",", ""))
            if agent in self.agents:
                self.agents[agent]["last"] = text
                self.agents[agent]["status"] = (
                    "active" if kind in {"agent", "section"} else
                    "attention" if kind == "warn" else
                    "complete" if kind == "success" else
                    self.agents[agent]["status"]
                )
            if kind == "agent" and turn % 2 == 0:
                reply_agent, reply_text = dialogue_reply(agent, original_text, turn)
                self.sequence += 1
                self.messages.append({
                    "id": self.sequence,
                    "kind": "agent",
                    "agent": reply_agent,
                    "text": reply_text,
                    "topic": topic or self.topic,
                    "time": now_utc().strftime("%H:%M:%S"),
                })
                self.stats["messages"] += 1

    def publish_file(self, path: str, kind: str = "Research finding", topic: str = "") -> None:
        """Record a real output file for the dashboard's file activity column."""
        with self.lock:
            self.file_sequence += 1
            self.files.append({
                "id": self.file_sequence,
                "name": os.path.basename(path),
                "path": path,
                "kind": kind,
                "topic": topic or self.topic,
                "time": now_utc().strftime("%H:%M:%S"),
            })
            self.stats["files"] = len(self.files)

    def snapshot(self) -> dict[str, Any]:
        with self.lock:
            return {
                "app": APP_NAME,
                "topic": self.topic,
                "started_at": self.started_at,
                "messages": list(self.messages),
                "files": list(self.files),
                "stats": dict(self.stats),
                "agents": list(self.agents.values()),
            }


_DASHBOARD: DashboardState | None = None


def dashboard_publish(kind: str, agent: str, text: str, topic: str = "") -> None:
    if _DASHBOARD is not None:
        _DASHBOARD.publish(kind, agent, text, topic)


def dashboard_file_written(path: Path, kind: str, topic: str = "") -> None:
    if _DASHBOARD is not None:
        _DASHBOARD.publish_file(str(path), kind, topic)


DASHBOARD_HTML = r"""<!doctype html>
<html lang="en">
<head>
  <meta charset="utf-8">
  <meta name="viewport" content="width=device-width, initial-scale=1">
  <title>Hex</title>
  <style>
     :root {
       color-scheme: dark;
       --bg: #080908; --panel: rgba(255,255,255,.065); --panel-2: rgba(255,255,255,.095);
       --line: rgba(255,255,255,.15); --text: #f3f1ed; --muted: #aaa69f;
       --cyan: #a9e6d8; --violet: #d2b6ff; --green: #9ee4bd;
       --amber: #f6cc83; --red: #f19a9e;
       --glass-highlight: rgba(255,255,255,.12);
     }
    * { box-sizing: border-box; }
     body { margin: 0; background:
       radial-gradient(circle at 8% 0%, rgba(226,181,145,.15) 0, transparent 30%),
       radial-gradient(circle at 94% 9%, rgba(194,157,232,.13) 0, transparent 28%),
       radial-gradient(circle at 52% 100%, rgba(128,192,169,.08) 0, transparent 36%),
       linear-gradient(135deg, #080908 0%, #141413 52%, #070807 100%);
       color: var(--text); font: 13px/1.42 ui-sans-serif, system-ui, -apple-system, "Segoe UI", sans-serif;
       -webkit-font-smoothing: antialiased; text-rendering: optimizeLegibility; }
      body::before { content: ""; position: fixed; inset: 0; pointer-events: none;
        background: rgba(0,0,0,.18); z-index: -1; }
      #background-layer { position: fixed; inset: 0; overflow: hidden; pointer-events: none;
        z-index: 0; background: #080908; }
      #background-layer::after { content: ""; position: absolute; inset: 0;
        background: rgba(0,0,0,.22); }
      .background-image, .background-video { position: absolute; inset: 0; width: 100%; height: 100%;
        object-fit: cover; border: 0; }
      .background-video { width: 177.78vh; min-width: 100vw; height: 56.25vw; min-height: 100vh;
        left: 50%; top: 50%; transform: translate(-50%, -50%) scale(1.08); }
      .shell { position: relative; z-index: 1; }
     .shell { min-height: 100vh; max-width: 930px; margin: 0 auto; padding: 16px; }
    header { display: flex; justify-content: space-between; align-items: flex-start;
      gap: 20px; margin-bottom: 22px; }
    .eyebrow { color: var(--cyan); letter-spacing: .22em; font-size: 10px; font-weight: 800; }
     .brand-line { display: flex; align-items: center; gap: 4px; margin: 5px 0 4px; }
     h1 { margin: 0; font-size: clamp(31px, 5vw, 50px); letter-spacing: -.065em; }
     .brand-logo { width: clamp(54px, 8vw, 78px); height: clamp(38px, 5vw, 58px);
       object-fit: contain; object-position: center; display: block; filter: drop-shadow(0 5px 12px rgba(0,0,0,.35)); }
    .subtitle { color: var(--muted); margin: 0; }
    .header-actions { display: flex; align-items: center; gap: 10px; }
     .live { display: flex; align-items: center; gap: 8px; color: var(--green);
       border: 1px solid rgba(158,228,189,.3); background: rgba(158,228,189,.08);
       padding: 8px 12px; border-radius: 999px; font-size: 12px; white-space: nowrap; }
     button { border: 1px solid var(--line); color: var(--text); background: rgba(255,255,255,.07);
      border-radius: 10px; padding: 9px 12px; cursor: pointer; font: inherit; }
    button:hover { border-color: var(--cyan); color: var(--cyan); }
    .settings-icon { font-size: 16px; line-height: 1; }
    .dot { width: 8px; height: 8px; background: var(--green); border-radius: 50%;
      box-shadow: 0 0 13px var(--green); animation: pulse 1.6s infinite; }
    @keyframes pulse { 50% { opacity: .35; } }
     .layout { display: grid; grid-template-columns: minmax(0, 680px) 220px;
       gap: 12px; align-items: start; }
      .panel { border: 1px solid var(--line); background: transparent;
        box-shadow: 0 24px 80px rgba(0,0,0,.28), inset 0 1px 0 var(--glass-highlight);
       border-radius: 18px; overflow: hidden; }
    .panel-head { padding: 16px 18px; border-bottom: 1px solid var(--line);
        display: flex; align-items: center; justify-content: space-between; background: rgba(8,9,8,.16); }
    .panel-title { font-weight: 800; letter-spacing: .01em; }
    .topic { color: var(--cyan); max-width: 60%; overflow: hidden; text-overflow: ellipsis; white-space: nowrap; }
      #chat { height: min(54vh, 560px); min-height: 360px; overflow: auto; padding: 14px 16px 16px; }
     .message { display: flex; gap: 8px; margin: 0 0 8px; animation: rise .3s ease both; }
    .message.right { flex-direction: row-reverse; }
    @keyframes rise { from { opacity: 0; transform: translateY(8px); } }
     .avatar { flex: 0 0 26px; height: 26px; display: grid; place-items: center;
      align-self: flex-end; border-radius: 50%; color: #091018; font-weight: 900; font-size: 10px;
      background: linear-gradient(135deg, var(--cyan), var(--violet)); }
     .message.system .avatar { background: linear-gradient(135deg, rgba(255,255,255,.42), rgba(255,255,255,.16)); color: #111; }
    .message.success .avatar { background: var(--green); }
    .message.warn .avatar { background: var(--amber); }
     .bubble { min-width: 0; max-width: min(62%, 560px); }
    .message.right .bubble { display: flex; flex-direction: column; align-items: flex-end; }
     .meta { display: flex; gap: 8px; align-items: baseline; margin: 0 6px 3px; }
    .message.right .meta { flex-direction: row-reverse; }
     .agent { font-weight: 650; color: #f5f2ed; }
     .time { color: var(--muted); font-size: 10px; }
      .text { color: #e7e3dc; background: rgba(255,255,255,.075);
       border: 1px solid rgba(255,255,255,.13); border-radius: 18px 18px 18px 5px;
       padding: 7px 11px; white-space: pre-wrap; font-size: 12px; line-height: 1.32;
       font-weight: 450; box-shadow: inset 0 1px 0 rgba(255,255,255,.06); }
     .message.right .text { border-radius: 18px 18px 5px 18px; }
     .message.system .text { background: transparent; border-color: transparent; padding-left: 0; color: var(--muted); box-shadow: none; }
     .message.success .text { background: rgba(104,205,147,.15); border-color: rgba(104,205,147,.34); color: #d0f3db; }
     .message.warn .text { background: rgba(243,187,92,.15); border-color: rgba(243,187,92,.34); color: #ffe1aa; }
     .message.agent.team-learning .text { background: rgba(211,157,255,.2); border-color: rgba(211,157,255,.4); }
     .message.agent.team-learning .avatar { background: #d39dff; }
     .message.agent.team-science .text { background: rgba(111,221,185,.2); border-color: rgba(111,221,185,.4); }
     .message.agent.team-science .avatar { background: #6fddb9; }
     .message.agent.team-computing .text { background: rgba(255,154,116,.2); border-color: rgba(255,154,116,.4); }
     .message.agent.team-computing .avatar { background: #ff9a74; }
     .message.agent.team-health .text { background: rgba(246,204,131,.2); border-color: rgba(246,204,131,.4); }
     .message.agent.team-health .avatar { background: #f6cc83; }
     .message.agent.team-society .text { background: rgba(243,151,190,.2); border-color: rgba(243,151,190,.4); }
     .message.agent.team-society .avatar { background: #f397be; }
     .message.agent.team-curriculum .text { background: rgba(133,211,206,.2); border-color: rgba(133,211,206,.4); }
     .message.agent.team-curriculum .avatar { background: #85d3ce; }
     .message.agent.team-evidence .text { background: rgba(195,211,126,.2); border-color: rgba(195,211,126,.4); }
     .message.agent.team-evidence .avatar { background: #c3d37e; }
     .message.agent.team-discovery .text { background: rgba(244,182,222,.2); border-color: rgba(244,182,222,.4); }
     .message.agent.team-discovery .avatar { background: #f4b6de; }
     .message.agent.team-methods .text { background: rgba(240,201,153,.2); border-color: rgba(240,201,153,.4); }
     .message.agent.team-methods .avatar { background: #f0c999; }
     .message.agent.team-frontier .text { background: rgba(207,177,255,.2); border-color: rgba(207,177,255,.4); }
     .message.agent.team-frontier .avatar { background: #cfb1ff; }
     .message.agent.team-context .text { background: rgba(166,201,178,.2); border-color: rgba(166,201,178,.4); }
     .message.agent.team-context .avatar { background: #a6c9b2; }
    .empty { color: var(--muted); text-align: center; padding: 80px 20px; }
    .composer { border-top: 1px solid var(--line); color: var(--muted); padding: 13px 20px;
      font-size: 12px; display: flex; align-items: center; gap: 8px; }
     .files-panel { min-width: 0; }
     .files-head { display: block; padding: 14px 15px 12px; }
     .files-subtitle { color: var(--muted); font-size: 11px; margin-top: 3px; }
     #files { height: min(54vh, 560px); min-height: 360px; overflow: auto; padding: 8px; }
     .file-empty { color: var(--muted); padding: 30px 10px; text-align: center; font-size: 12px; }
     .file-item { display: grid; grid-template-columns: 26px minmax(0, 1fr); gap: 9px;
       padding: 9px 7px; border-bottom: 1px solid rgba(255,255,255,.09); animation: rise .3s ease both; }
     .file-item:last-child { border-bottom: 0; }
     .file-icon { width: 26px; height: 30px; display: grid; place-items: center;
       border: 1px solid rgba(169,230,216,.35); border-radius: 6px; color: var(--cyan);
       background: rgba(169,230,216,.1); font-size: 13px; }
     .file-name { color: #eeeae4; font-size: 11px; line-height: 1.3; overflow-wrap: anywhere; }
     .file-meta { color: var(--muted); font-size: 10px; margin-top: 3px; }
    .thinking { width: 7px; height: 7px; border-radius: 50%; background: var(--cyan);
      box-shadow: 12px 0 var(--cyan), 24px 0 var(--cyan); margin: 0 17px 0 3px;
      animation: typing 1.2s infinite; }
    @keyframes typing { 50% { opacity: .35; } }
    .modal-backdrop { position: fixed; inset: 0; display: none; align-items: center;
      justify-content: center; background: #0009; z-index: 10; padding: 20px; }
    .modal-backdrop.open { display: flex; }
      .modal { width: min(480px, 100%); border: 1px solid var(--line); border-radius: 18px;
        background: rgba(16,19,20,.94);
       box-shadow: 0 30px 100px rgba(0,0,0,.7), inset 0 1px 0 var(--glass-highlight); padding: 22px; }
    .modal h2 { margin: 0 0 6px; } .modal p { color: var(--muted); margin-top: 0; }
    .modal label { display: block; font-weight: 700; font-size: 12px; margin: 18px 0 7px; }
     .modal input { width: 100%; border: 1px solid var(--line); background: rgba(0,0,0,.24);
      border-radius: 10px; color: var(--text); padding: 11px 12px; font: inherit; }
    .modal-actions { display: flex; justify-content: flex-end; gap: 8px; margin-top: 18px; }
      @media (max-width: 940px) { .layout { grid-template-columns: minmax(0, 1fr) 205px; } }
      @media (max-width: 760px) { .shell { padding: 14px; } header { display: block; }
       .header-actions { margin-top: 16px; } .layout { grid-template-columns: 1fr; }
       #chat, #files { height: 52vh; min-height: 320px; padding: 14px 10px; }
       .bubble { max-width: 78%; } .text { font-size: 12px; } }
  </style>
</head>
<body>
  <div id="background-layer" aria-hidden="true"></div>
  <main class="shell">
    <header>
       <div><div class="eyebrow">A LIVING LEARNING ECOSYSTEM</div>
         <div class="brand-line"><h1>Hex</h1><img class="brand-logo" src="${WIKIPEDIA_LOGO_DATA_URI}" alt="Wikipedia logo"></div>
         <p class="subtitle">Research agents thinking together in real time.</p></div>
      <div class="header-actions">
        <button id="settings-button" class="settings-icon" aria-label="Open settings" title="Settings">⚙</button>
        <div class="live"><span class="dot"></span> LIVE</div>
      </div>
    </header>
     <div class="layout">
       <section class="panel conversation-panel">
        <div class="panel-head"><span class="panel-title">Conversation</span><span id="topic" class="topic">Preparing…</span></div>
        <div id="chat"><div class="empty">The agents are gathering around the question…</div></div>
        <div class="composer"><span class="thinking"></span><span id="composer-text">The room is thinking…</span></div>
      </section>
       <aside class="panel files-panel">
         <div class="panel-head files-head"><div class="panel-title">Files</div><div class="files-subtitle">Being sent to your library</div></div>
         <div id="files"><div class="file-empty">No files written yet.</div></div>
       </aside>
    </div>
  </main>
  <div id="settings-modal" class="modal-backdrop" role="dialog" aria-modal="true" aria-labelledby="settings-title">
    <div class="modal">
       <h2 id="settings-title">Hex settings</h2>
       <p>Give the conversation a room of its own. Your background is saved only in this browser. Use an image URL or a YouTube video URL.</p>
       <label for="background-url">Background image or YouTube URL</label>
       <input id="background-url" type="url" placeholder="https://youtube.com/watch?v=... or https://example.com/image.jpg">
       <div class="modal-actions"><button id="cancel-settings">Cancel</button><button id="save-settings">Save background</button></div>
    </div>
  </div>
  <script>
     let rendered = 0;
     let renderedFiles = 0;
    const esc = value => String(value ?? '').replace(/[&<>"']/g, c => ({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
    const initials = name => name.split(/\s+/).map(x => x[0]).join('').slice(0, 2).toUpperCase();
     const hash = name => [...name].reduce((sum, char) => sum + char.charCodeAt(0), 0);
     const teamFor = name => {
       const value = String(name ?? '').toLowerCase();
       const teams = [
         ['learning', 'learning'], ['science', 'science'], ['computing', 'computing'],
         ['health', 'health'], ['society', 'society'], ['curriculum', 'curriculum'],
         ['evidence', 'evidence'], ['discovery', 'discovery'], ['methods', 'methods'],
         ['frontier', 'frontier'], ['context', 'context']
       ];
       return (teams.find(([needle]) => value.includes(needle)) || ['coordinator', 'coordinator'])[1];
     };
    const modal = document.querySelector('#settings-modal');
    const backgroundInput = document.querySelector('#background-url');
     const backgroundLayer = document.querySelector('#background-layer');
     function youtubeVideoId(value) {
       try {
         const parsed = new URL(value);
         const host = parsed.hostname.toLowerCase().replace(/^www\./, '');
         const parts = parsed.pathname.split('/').filter(Boolean);
         let id = '';
         if (host === 'youtu.be') {
           id = parts[0] || '';
         } else if (host === 'youtube.com' || host === 'm.youtube.com' || host === 'youtube-nocookie.com') {
           if (parsed.pathname === '/watch') id = parsed.searchParams.get('v') || '';
           else if (['shorts', 'embed', 'live'].includes(parts[0])) id = parts[1] || '';
         }
         return /^[A-Za-z0-9_-]{11}$/.test(id) ? id : '';
       } catch (_) {
         return '';
       }
     }
     function applyBackground(value) {
       backgroundLayer.replaceChildren();
       const url = String(value || '').trim();
       if (!url) return;
       const videoId = youtubeVideoId(url);
       if (videoId) {
         const iframe = document.createElement('iframe');
         iframe.className = 'background-video';
         iframe.src = `https://www.youtube-nocookie.com/embed/${videoId}?autoplay=1&mute=1&controls=0&loop=1&playlist=${videoId}&playsinline=1&rel=0&modestbranding=1&iv_load_policy=3&disablekb=1`;
         iframe.title = 'YouTube background video';
         iframe.allow = 'autoplay; encrypted-media';
         iframe.tabIndex = -1;
         backgroundLayer.appendChild(iframe);
         return;
       }
       const image = document.createElement('img');
       image.className = 'background-image';
       image.src = url;
       image.alt = '';
       image.addEventListener('error', () => backgroundLayer.replaceChildren(), {once: true});
       backgroundLayer.appendChild(image);
     }
    const savedBackground = localStorage.getItem('edu-background') || '';
    backgroundInput.value = savedBackground;
    applyBackground(savedBackground);
    document.querySelector('#settings-button').onclick = () => modal.classList.add('open');
    document.querySelector('#cancel-settings').onclick = () => modal.classList.remove('open');
    document.querySelector('#save-settings').onclick = () => {
      const url = backgroundInput.value.trim();
      if (url && !/^https?:\/\//i.test(url)) { backgroundInput.focus(); return; }
      localStorage.setItem('edu-background', url);
      applyBackground(url);
      modal.classList.remove('open');
    };
    modal.onclick = event => { if (event.target === modal) modal.classList.remove('open'); };
    function render(data) {
      document.querySelector('#topic').textContent = data.topic;
      const chat = document.querySelector('#chat');
      if (rendered === 0 && data.messages.length) chat.innerHTML = '';
      for (const msg of data.messages.slice(rendered)) {
        const side = hash(msg.agent) % 2 ? 'right' : '';
         const item = document.createElement('div');
         item.className = `message ${esc(msg.kind)} ${side} team-${teamFor(msg.agent)}`;
        item.innerHTML = `<div class="avatar">${esc(initials(msg.agent))}</div><div class="bubble"><div class="meta"><span class="agent">${esc(msg.agent)}</span><span class="time">${esc(msg.time)}</span></div><div class="text">${esc(msg.text)}</div></div>`;
        chat.appendChild(item);
      }
      rendered = data.messages.length;
      chat.scrollTop = chat.scrollHeight;
      document.querySelector('#composer-text').textContent = data.messages.length ? 'The agents are listening, challenging, and building on each other…' : 'The room is thinking…';
       const files = document.querySelector('#files');
       if (renderedFiles === 0 && data.files.length) files.innerHTML = '';
       for (const file of data.files.slice(renderedFiles)) {
         const item = document.createElement('div');
         item.className = 'file-item';
         item.innerHTML = `<div class="file-icon">▤</div><div><div class="file-name" title="${esc(file.path)}">${esc(file.name)}</div><div class="file-meta">${esc(file.kind)} · ${esc(file.time)}</div></div>`;
         files.appendChild(item);
       }
       renderedFiles = data.files.length;
       files.scrollTop = files.scrollHeight;
    }
    async function refresh() { try { render(await (await fetch('/api/state', {cache: 'no-store'})).json()); } catch (_) {} }
    refresh(); setInterval(refresh, 700);
  </script>
</body>
</html>""".replace("${WIKIPEDIA_LOGO_DATA_URI}", WIKIPEDIA_LOGO_DATA_URI)


class DashboardHTTPServer(http.server.ThreadingHTTPServer):
    allow_reuse_address = True


class DashboardServer:
    """Small dependency-free local server for the live research dashboard."""

    def __init__(self, state: DashboardState, browser: str = "default") -> None:
        self.state = state
        self.browser = browser
        self.httpd: DashboardHTTPServer | None = None
        self.thread: threading.Thread | None = None

    def start(self) -> str:
        state = self.state

        class Handler(http.server.BaseHTTPRequestHandler):
            def do_GET(self) -> None:
                if self.path == "/api/state":
                    payload = json.dumps(state.snapshot(), ensure_ascii=False).encode("utf-8")
                    self.send_response(200)
                    self.send_header("Content-Type", "application/json; charset=utf-8")
                    self.send_header("Cache-Control", "no-store")
                    self.send_header("Content-Length", str(len(payload)))
                    self.end_headers()
                    self.wfile.write(payload)
                    return
                if self.path in {"/", "/index.html"}:
                    payload = DASHBOARD_HTML.encode("utf-8")
                    self.send_response(200)
                    self.send_header("Content-Type", "text/html; charset=utf-8")
                    self.send_header("Content-Length", str(len(payload)))
                    self.end_headers()
                    self.wfile.write(payload)
                    return
                self.send_error(404)

            def log_message(self, format: str, *args: Any) -> None:
                return

        self.httpd = DashboardHTTPServer(("127.0.0.1", 0), Handler)
        self.thread = threading.Thread(target=self.httpd.serve_forever, daemon=True)
        self.thread.start()
        host, port = self.httpd.server_address
        url = f"http://{host}:{port}/"
        self.open_browser(url)
        return url

    def open_browser(self, url: str) -> None:
        if self.browser == "default":
            webbrowser.open(url, new=2)
            return
        commands = {
            "chrome": ("google-chrome", "chrome", "chromium", "chromium-browser"),
            "firefox": ("firefox",),
            "edge": ("microsoft-edge", "microsoft-edge-stable"),
            "brave": ("brave-browser", "brave"),
        }
        executable = next(
            (shutil.which(candidate) for candidate in commands.get(self.browser, ()) if shutil.which(candidate)),
            None,
        )
        if executable:
            webbrowser.register(self.browser, None, webbrowser.BackgroundBrowser(executable))
            webbrowser.get(self.browser).open(url, new=2)
        else:
            dashboard_publish(
                "warn",
                "Coordinator",
                f"{self.browser.title()} was not found; opening the system default browser instead.",
            )
            webbrowser.open(url, new=2)

    def wait_forever(self) -> None:
        try:
            while True:
                time.sleep(1)
        except KeyboardInterrupt:
            return

    def stop(self) -> None:
        if self.httpd:
            self.httpd.shutdown()


class Console:
    """Terminal output adapter that also streams events to the dashboard."""

    _lock = threading.Lock()

    def __init__(self, topic: str = "") -> None:
        self.topic = topic

    def _prefix(self) -> str:
        return f"[{self.topic}] " if self.topic else ""

    @staticmethod
    def banner() -> None:
        dashboard_publish("section", "Coordinator", "Research network is online")
        if _DASHBOARD is not None and os.environ.get("EDU_HUB_TERMINAL") != "1":
            return
        line = "═" * 78
        with Console._lock:
            print(Ink.paint(line, Ink.CYAN))
            print(Ink.paint("  ◈  " + APP_NAME, Ink.BOLD + Ink.CYAN))
            print(Ink.paint("     Coordinated research teams for readable, cited findings", Ink.DIM))
            print(Ink.paint(line, Ink.CYAN))

    def section(self, title: str, detail: str = "") -> None:
        dashboard_publish(
            "section",
            "Coordinator",
            f"{title}{f' — {detail}' if detail else ''}",
            self.topic,
        )
        if _DASHBOARD is not None and os.environ.get("EDU_HUB_TERMINAL") != "1":
            return
        with Console._lock:
            print()
            print(Ink.paint(f"  {self._prefix()}{title}", Ink.BOLD + Ink.WHITE))
            if detail:
                print(Ink.paint(f"  {self._prefix()}{detail}", Ink.DIM))

    def event(self, label: str, detail: str, color: str = Ink.BLUE) -> None:
        dashboard_publish("agent", label, detail, self.topic)
        if _DASHBOARD is not None and os.environ.get("EDU_HUB_TERMINAL") != "1":
            return
        with Console._lock:
            print(f"  {Ink.paint('▸', color)} {Ink.paint(self._prefix() + label, Ink.BOLD)} {Ink.paint(detail, Ink.DIM)}")

    def success(self, detail: str) -> None:
        dashboard_publish("success", "Coordinator", detail, self.topic)
        if _DASHBOARD is not None and os.environ.get("EDU_HUB_TERMINAL") != "1":
            return
        with Console._lock:
            print(f"  {Ink.paint('✓', Ink.GREEN)} {self._prefix()}{detail}")

    def warn(self, detail: str) -> None:
        dashboard_publish("warn", "Coordinator", detail, self.topic)
        if _DASHBOARD is not None and os.environ.get("EDU_HUB_TERMINAL") != "1":
            return
        with Console._lock:
            print(f"  {Ink.paint('!', Ink.YELLOW)} {self._prefix()}{detail}")

    def error(self, detail: str) -> None:
        dashboard_publish("warn", "Coordinator", detail, self.topic)
        if _DASHBOARD is not None and os.environ.get("EDU_HUB_TERMINAL") != "1":
            return
        with Console._lock:
            print(f"  {Ink.paint('×', Ink.RED)} {self._prefix()}{detail}")

    def bar(self, label: str, amount: int, total: int) -> None:
        dashboard_publish("system", "Evidence Desk", f"{label}: {amount}/{total}", self.topic)
        if _DASHBOARD is not None and os.environ.get("EDU_HUB_TERMINAL") != "1":
            return
        width = 24
        filled = int(width * amount / total) if total else width
        track = "━" * filled + "·" * (width - filled)
        with Console._lock:
            print(f"  {Ink.paint(track, Ink.CYAN)} {self._prefix()}{label} {amount}/{total}")


class ResponseCache:
    """Small persistent HTTP response cache shared across every Hex run.

    OpenAlex, Crossref, Semantic Scholar, and arXiv all get hit repeatedly as
    the autonomous catalog rotates back through the same subjects. Caching
    each request's raw JSON body on disk (with a per-source TTL) means a
    repeated query is answered instantly and locally instead of re-hitting
    the public API, without ever going stale for long.
    """

    _lock = threading.Lock()

    def __init__(self, path: Path) -> None:
        self.path = path
        with self._lock, self._connect() as connection:
            connection.execute(
                """
                CREATE TABLE IF NOT EXISTS http_cache (
                    url TEXT PRIMARY KEY,
                    body TEXT NOT NULL,
                    fetched_at REAL NOT NULL
                )
                """
            )

    def _connect(self) -> sqlite3.Connection:
        connection = sqlite3.connect(self.path, timeout=30)
        connection.execute("PRAGMA journal_mode=WAL")
        return connection

    def get(self, url: str, ttl_seconds: int) -> str | None:
        with self._lock, self._connect() as connection:
            row = connection.execute(
                "SELECT body, fetched_at FROM http_cache WHERE url = ?", (url,)
            ).fetchone()
        if not row:
            return None
        body, fetched_at = row
        if time.time() - fetched_at > ttl_seconds:
            return None
        return body

    def set(self, url: str, body: str) -> None:
        with self._lock, self._connect() as connection:
            connection.execute(
                """
                INSERT INTO http_cache (url, body, fetched_at) VALUES (?, ?, ?)
                ON CONFLICT(url) DO UPDATE SET body = excluded.body, fetched_at = excluded.fetched_at
                """,
                (url, body, time.time()),
            )


class PublicResearchAPI:
    """HTTP helpers and source-specific adapters for public scholarly data."""

    # The Wikipedia harvest runs seven partition crawlers in parallel, all
    # sharing one PublicResearchAPI instance. With no shared pacing between
    # them, they burst dozens of concurrent requests at Wikipedia's search
    # API and quickly trip its anonymous rate limit (repeated "HTTP Error
    # 429: Too Many Requests"). This enforces a minimum gap between
    # consecutive requests to the same host, across all threads.
    MIN_REQUEST_INTERVAL = {
        "en.wikipedia.org": 0.5,
    }

    def __init__(
        self,
        timeout: int = 18,
        max_results: int = 8,
        cache: ResponseCache | None = None,
    ) -> None:
        self.timeout = timeout
        self.max_results = max_results
        self.cache = cache
        self._host_lock = threading.Lock()
        self._host_last_request: dict[str, float] = {}

    def _throttle(self, url: str) -> None:
        host = urllib.parse.urlparse(url).netloc
        interval = self.MIN_REQUEST_INTERVAL.get(host)
        if not interval:
            return
        with self._host_lock:
            now = time.monotonic()
            last = self._host_last_request.get(host, 0.0)
            wait = interval - (now - last)
            if wait > 0:
                time.sleep(wait)
            self._host_last_request[host] = time.monotonic()

    @staticmethod
    def _cache_ttl(url: str) -> int:
        host = urllib.parse.urlparse(url).netloc
        if "openalex.org" in host:
            return CACHE_TTL_SECONDS["OpenAlex"]
        if "crossref.org" in host:
            return CACHE_TTL_SECONDS["Crossref"]
        if "semanticscholar.org" in host:
            return CACHE_TTL_SECONDS["Semantic Scholar"]
        if "arxiv.org" in host:
            return CACHE_TTL_SECONDS["arXiv"]
        if "wikipedia.org" in host:
            return CACHE_TTL_SECONDS["Wikipedia"]
        return DEFAULT_CACHE_TTL_SECONDS

    @staticmethod
    def _retry_after_seconds(exc: urllib.error.HTTPError, attempt: int) -> float:
        header = exc.headers.get("Retry-After") if exc.headers else None
        if header:
            try:
                return max(float(header), 1.0)
            except ValueError:
                pass
        return float(2**attempt)

    def fetch_json(self, url: str) -> dict[str, Any]:
        ttl = self._cache_ttl(url)
        if self.cache is not None:
            cached = self.cache.get(url, ttl)
            if cached is not None:
                return json.loads(cached)
        attempts = 6
        for attempt in range(attempts):
            self._throttle(url)
            request = urllib.request.Request(url, headers={"User-Agent": USER_AGENT, "Accept": "application/json"})
            try:
                with urllib.request.urlopen(request, timeout=self.timeout) as response:
                    body = response.read().decode("utf-8")
                if self.cache is not None:
                    self.cache.set(url, body)
                return json.loads(body)
            except urllib.error.HTTPError as exc:
                if exc.code not in (429, 500, 502, 503, 504) or attempt == attempts - 1:
                    raise
                time.sleep(self._retry_after_seconds(exc, attempt))

    def fetch_text(self, url: str) -> str:
        self._throttle(url)
        request = urllib.request.Request(url, headers={"User-Agent": USER_AGENT, "Accept": "application/atom+xml,text/xml"})
        with urllib.request.urlopen(request, timeout=self.timeout) as response:
            return response.read().decode("utf-8")

    def wikipedia(self, query: str) -> list[SourceRecord]:
        """Search the full English Wikipedia article index, then fetch page leads.

        MediaWiki's `srsearch` searches article text, titles, redirects, and
        metadata—not just exact topic titles. A second batched query fetches
         readable lead extracts and page quality signals for each finding.
        """
        search_params = urllib.parse.urlencode({
            "action": "query",
            "list": "search",
            "srsearch": query,
            "srnamespace": 0,
            "srlimit": self.max_results,
            "srprop": "snippet|size|wordcount|timestamp",
            "format": "json",
            "formatversion": 2,
        })
        search_data = self.fetch_json(f"{WIKIPEDIA_API}?{search_params}")
        hits = search_data.get("query", {}).get("search", [])
        if not hits:
            return []

        page_ids = "|".join(str(hit["pageid"]) for hit in hits)
        page_params = urllib.parse.urlencode({
            "action": "query",
            "pageids": page_ids,
            "prop": "extracts|info|categories",
             "exintro": 0,
            "explaintext": 1,
             "exchars": WIKIPEDIA_ARTICLE_CHARS,
            "inprop": "url",
            "cllimit": 12,
            "format": "json",
            "formatversion": 2,
        })
        page_data = self.fetch_json(f"{WIKIPEDIA_API}?{page_params}")
        pages = {str(page.get("pageid")): page for page in page_data.get("query", {}).get("pages", [])}
        records: list[SourceRecord] = []
        for hit in hits:
            page = pages.get(str(hit.get("pageid")), {})
            title = compact(page.get("title") or hit.get("title") or "", 240)
            if not title or page.get("missing"):
                continue
            categories = tuple(
                compact(category.get("title", "").removeprefix("Category:"), 80)
                for category in page.get("categories", [])[:8]
            )
            url = page.get("fullurl") or f"https://en.wikipedia.org/wiki/{urllib.parse.quote(title.replace(' ', '_'))}"
            records.append(SourceRecord(
                title=title,
                abstract=compact(page.get("extract") or "", WIKIPEDIA_ARTICLE_CHARS),
                authors=("Wikipedia contributors",),
                year=iso_date(hit.get("timestamp")),
                venue="Wikipedia",
                url=url,
                doi="",
                source="Wikipedia",
                record_type="encyclopedia article",
                tags=categories,
            ))
        return records

    def wikipedia_batch(
        self,
        query: str,
        offset: int,
        batch_size: int = DEFAULT_WIKIPEDIA_BATCH,
    ) -> tuple[list[SourceRecord], int, int]:
        """Fetch one resumable page of full-text Wikipedia search results."""
        search_params = urllib.parse.urlencode({
            "action": "query",
            "list": "search",
            "srsearch": query,
            "srnamespace": 0,
            "srlimit": min(batch_size, 500),
            "sroffset": offset,
            "srprop": "snippet|size|wordcount|timestamp",
            "format": "json",
            "formatversion": 2,
        })
        search_data = self.fetch_json(f"{WIKIPEDIA_API}?{search_params}")
        query_data = search_data.get("query", {})
        hits = query_data.get("search", [])
        total_hits = int((query_data.get("searchinfo") or {}).get("totalhits") or 0)
        if not hits:
            return [], offset, total_hits

        page_ids = "|".join(str(hit["pageid"]) for hit in hits)
        page_params = urllib.parse.urlencode({
            "action": "query",
            "pageids": page_ids,
            "prop": "extracts|info|categories",
            "exintro": 0,
            "explaintext": 1,
             "exchars": WIKIPEDIA_ARTICLE_CHARS,
            "inprop": "url",
            "cllimit": 12,
            "format": "json",
            "formatversion": 2,
        })
        page_data = self.fetch_json(f"{WIKIPEDIA_API}?{page_params}")
        pages = {str(page.get("pageid")): page for page in page_data.get("query", {}).get("pages", [])}
        records: list[SourceRecord] = []
        for hit in hits:
            page = pages.get(str(hit.get("pageid")), {})
            title = compact(page.get("title") or hit.get("title") or "", 240)
            if not title or page.get("missing"):
                continue
            categories = tuple(
                compact(category.get("title", "").removeprefix("Category:"), 80)
                for category in page.get("categories", [])[:8]
            )
            url = page.get("fullurl") or f"https://en.wikipedia.org/wiki/{urllib.parse.quote(title.replace(' ', '_'))}"
            records.append(SourceRecord(
                title=title,
                abstract=compact(page.get("extract") or "", WIKIPEDIA_ARTICLE_CHARS),
                authors=("Wikipedia contributors",),
                year=iso_date(hit.get("timestamp")),
                venue="Wikipedia",
                url=url,
                doi="",
                source="Wikipedia",
                record_type="encyclopedia article",
                tags=categories,
            ))
        return records, offset + len(hits), total_hits

    def wikipedia_allpages_batch(
        self,
        cursor: str,
        prefix_from: str,
        prefix_to: str,
        batch_size: int = DEFAULT_WIKIPEDIA_BATCH,
    ) -> tuple[list[SourceRecord], str, int]:
        """Walk a durable alphabetical slice of all non-redirect articles.

        Unlike relevance search, MediaWiki's allpages generator can be resumed
        with its continuation token and eventually visits the whole namespace.
        Seven partitions let independent agents harvest different ranges at
        the same time without repeatedly requesting the same pages.
        """
        params: dict[str, str | int] = {
            "action": "query",
            "generator": "allpages",
            "gapnamespace": 0,
            "gaplimit": min(batch_size, 500),
            "gapfilterredir": "nonredirects",
            "prop": "extracts|info|categories",
             "exintro": 0,
            "explaintext": 1,
             "exchars": WIKIPEDIA_ARTICLE_CHARS,
            "inprop": "url",
            "cllimit": 12,
            "format": "json",
            "formatversion": 2,
        }
        if cursor:
            params["gapcontinue"] = cursor
        elif prefix_from:
            params["gapfrom"] = prefix_from
        if prefix_to:
            params["gapto"] = prefix_to
        page_data = self.fetch_json(f"{WIKIPEDIA_API}?{urllib.parse.urlencode(params)}")
        pages = page_data.get("query", {}).get("pages", [])
        records: list[SourceRecord] = []
        for page in pages:
            title = compact(page.get("title") or "", 240)
            if not title or page.get("missing"):
                continue
            categories = tuple(
                compact(category.get("title", "").removeprefix("Category:"), 80)
                for category in page.get("categories", [])[:10]
            )
            url = page.get("fullurl") or f"https://en.wikipedia.org/wiki/{urllib.parse.quote(title.replace(' ', '_'))}"
            records.append(SourceRecord(
                title=title,
                abstract=compact(page.get("extract") or "", WIKIPEDIA_ARTICLE_CHARS),
                authors=("Wikipedia contributors",),
                year=iso_date(page.get("touched")),
                venue="Wikipedia",
                url=url,
                doi="",
                source="Wikipedia",
                record_type="encyclopedia article",
                tags=categories,
            ))
        continuation = (page_data.get("continue") or {}).get("gapcontinue", "")
        return records, continuation, len(pages)

    # Crossref registers a DOI for every individual figure, table, and
    # sub-part of a report -- not just for the report itself. Those
    # "component" (and similarly non-substantive) records have a caption for
    # a title and never carry an abstract, so they were flooding topic
    # folders with a wall of identical "no abstract available" placeholder
    # files. They are not standalone findings, so skip them at the source.
    CROSSREF_EXCLUDED_TYPES = {"component", "grant", "peer-review"}

    def crossref(self, query: str) -> list[SourceRecord]:
        params = urllib.parse.urlencode({"query.bibliographic": query, "rows": self.max_results, "select": "title,author,published,container-title,URL,DOI,type,abstract"})
        data = self.fetch_json(f"https://api.crossref.org/works?{params}")
        records: list[SourceRecord] = []
        for item in data.get("message", {}).get("items", []):
            if (item.get("type") or "") in self.CROSSREF_EXCLUDED_TYPES:
                continue
            title = compact((item.get("title") or [""])[0], 240)
            if not title:
                continue
            authors = tuple(
                compact(" ".join(filter(None, [author.get("given"), author.get("family")])), 100)
                for author in item.get("author", [])
            )
            published = (item.get("published") or {}).get("date-parts", [[]])[0]
            records.append(SourceRecord(
                title=title,
                abstract=compact(
                    re.sub(r"<[^>]+>", " ", item.get("abstract", "")),
                    SCHOLARLY_SUMMARY_CHARS,
                ),
                authors=tuple(filter(None, authors)),
                year=str(published[0]) if published else "n.d.",
                venue=compact((item.get("container-title") or [""])[0], 120),
                url=item.get("URL") or "",
                doi=item.get("DOI") or "",
                source="Crossref",
                record_type=item.get("type") or "scholarly work",
            ))
        return records

    def openalex(self, query: str) -> list[SourceRecord]:
        params = urllib.parse.urlencode({"search": query, "per-page": self.max_results, "mailto": "research-hub@example.invalid"})
        data = self.fetch_json(f"https://api.openalex.org/works?{params}")
        records: list[SourceRecord] = []
        for item in data.get("results", []):
            title = compact(item.get("title", ""), 240)
            if not title:
                continue
            authors = tuple(
                compact(((author.get("author") or {}).get("display_name") or ""), 100)
                for author in item.get("authorships", [])[:6]
            )
            location = item.get("primary_location") or {}
            source = location.get("source") or {}
            records.append(SourceRecord(
                title=title,
                abstract=self._openalex_abstract(item.get("abstract_inverted_index") or {}),
                authors=tuple(filter(None, authors)),
                year=str(item.get("publication_year") or "n.d."),
                venue=compact(source.get("display_name") or "", 120),
                url=location.get("landing_page_url") or item.get("doi") or item.get("id") or "",
                doi=(item.get("doi") or "").removeprefix("https://doi.org/"),
                source="OpenAlex",
                record_type=item.get("type") or "research",
            ))
        return records

    def arxiv(self, query: str) -> list[SourceRecord]:
        params = urllib.parse.urlencode({"search_query": f"all:{query}", "start": 0, "max_results": self.max_results, "sortBy": "relevance"})
        root = ET.fromstring(self.fetch_text(f"https://export.arxiv.org/api/query?{params}"))
        ns = {"atom": "http://www.w3.org/2005/Atom"}
        records: list[SourceRecord] = []
        for entry in root.findall("atom:entry", ns):
            title = compact(entry.findtext("atom:title", "", ns), 240)
            if not title:
                continue
            link = next((link.attrib.get("href", "") for link in entry.findall("atom:link", ns) if link.attrib.get("rel") == "alternate"), "")
            authors = tuple(compact(author.findtext("atom:name", "", ns), 100) for author in entry.findall("atom:author", ns))
            records.append(SourceRecord(
                title=title,
                abstract=compact(
                    entry.findtext("atom:summary", "", ns),
                    SCHOLARLY_SUMMARY_CHARS,
                ),
                authors=tuple(filter(None, authors)),
                year=iso_date(entry.findtext("atom:published", "", ns)),
                venue="arXiv",
                url=link,
                doi="",
                source="arXiv",
                record_type="preprint",
            ))
        return records

    def semantic_scholar(self, query: str) -> list[SourceRecord]:
        params = urllib.parse.urlencode({"query": query, "limit": self.max_results, "fields": "title,abstract,authors,year,venue,url,externalIds,publicationTypes"})
        data = self.fetch_json(f"https://api.semanticscholar.org/graph/v1/paper/search?{params}")
        records: list[SourceRecord] = []
        for item in data.get("data", []):
            title = compact(item.get("title", ""), 240)
            if not title:
                continue
            ids = item.get("externalIds") or {}
            records.append(SourceRecord(
                title=title,
                abstract=compact(item.get("abstract") or "", SCHOLARLY_SUMMARY_CHARS),
                authors=tuple(compact(a.get("name", ""), 100) for a in (item.get("authors") or [])[:6]),
                year=str(item.get("year") or "n.d."),
                venue=compact(item.get("venue") or "", 120),
                url=item.get("url") or "",
                doi=ids.get("DOI") or "",
                source="Semantic Scholar",
                record_type=", ".join(item.get("publicationTypes") or []) or "paper",
            ))
        return records

    @staticmethod
    def _openalex_abstract(inverted: dict[str, list[int]]) -> str:
        words: list[tuple[int, str]] = []
        for word, positions in inverted.items():
            for position in positions:
                words.append((position, word))
        return compact(" ".join(word for _, word in sorted(words)), SCHOLARLY_SUMMARY_CHARS)

    def collect(
        self,
        query: str,
        console: Console,
        include_wikipedia: bool = True,
    ) -> tuple[list[SourceRecord], list[str]]:
        jobs = {
            "Crossref": self.crossref,
            "OpenAlex": self.openalex,
            "arXiv": self.arxiv,
            "Semantic Scholar": self.semantic_scholar,
        }
        if include_wikipedia:
            jobs["Wikipedia"] = self.wikipedia
        records: list[SourceRecord] = []
        failures: list[str] = []
        with concurrent.futures.ThreadPoolExecutor(max_workers=len(jobs)) as pool:
            futures = {pool.submit(fetcher, query): name for name, fetcher in jobs.items()}
            for future in concurrent.futures.as_completed(futures):
                source = futures[future]
                try:
                    found = future.result()
                    records.extend(found)
                    console.event(source, f"{len(found)} candidate entries", Ink.GREEN)
                except Exception as exc:
                    message = compact(str(exc), 130)
                    failures.append(f"{source}: {message}")
                    console.warn(f"{source} unavailable — continuing ({message})")
        return records, failures


_response_cache_lock = threading.Lock()
_response_caches: dict[str, ResponseCache] = {}


def get_response_cache(output: Path) -> ResponseCache:
    """Share one on-disk cache per output folder across every coordinator.

    Every ResearchCoordinator (one per topic, possibly many running in
    parallel) reuses the same cache file instead of each opening its own, so
    a query answered once for "biology" this cycle is instantly available
    the next time "biology" comes back around in the autonomous rotation.
    """
    key = str(output.resolve())
    with _response_cache_lock:
        cache = _response_caches.get(key)
        if cache is None:
            output.mkdir(parents=True, exist_ok=True)
            cache = ResponseCache(output / "hex_response_cache.sqlite3")
            _response_caches[key] = cache
        return cache


class ResearchCoordinator:
    """Coordinates role-based teams and produces an auditable research packet."""

    def __init__(
        self,
        topic: str,
        output: Path,
        max_results: int = 8,
        timeout: int = 18,
        corpus: ResearchCorpus | None = None,
        include_wikipedia: bool = True,
    ) -> None:
        self.topic = topic.strip()
        self.output = output
        self.max_results = max_results
        self.corpus = corpus
        self.include_wikipedia = include_wikipedia
        self.console = Console(self.topic)
        self.api = PublicResearchAPI(
            timeout=timeout,
            max_results=max_results,
            cache=get_response_cache(output),
        )
        self.run_time = now_utc()

    def team_queries(self) -> list[tuple[AgentTeam, str]]:
        base = self.topic
        return [
            (team, f"{base} {team.lenses[0]}") for team in TEAMS[:5]
        ]

    def harvest_wikipedia_partition(
        self,
        corpus: ResearchCorpus,
        partition_index: int,
        batch_size: int = DEFAULT_WIKIPEDIA_BATCH,
        catalog_topics: Sequence[str] | None = None,
    ) -> tuple[int, bool]:
        """Harvest one alphabetical Wikipedia slice and persist its checkpoint.

        One worker per entry in WIKIPEDIA_PARTITIONS (there are seven; a
        previous version only ever spun up five workers, so the "T"-"Z"
        slice of the whole encyclopedia was never actually crawled).
        """
        prefix_from, prefix_to = WIKIPEDIA_PARTITIONS[partition_index]
        team = TEAMS[partition_index % len(TEAMS)]
        cursor_topic = "__wikipedia__"
        team_key = f"partition_{partition_index}"
        cursor, total_hits, pages_harvested = corpus.wikipedia_state(cursor_topic, team_key)
        records, next_cursor, page_count = self.api.wikipedia_allpages_batch(
            cursor,
            prefix_from,
            prefix_to,
            batch_size=batch_size,
        )
        tagged = [dataclasses.replace(record, tags=unique((*record.tags, team.key)) ) for record in records]
        inserted = corpus.upsert(tagged, cursor_topic)
        assigned = 0
        for topic in unique(catalog_topics or [self.topic]):
            relevant = [
                dataclasses.replace(
                    record,
                    tags=unique((*record.tags, topic, *topic_keywords(topic))),
                )
                for record in records
                if topic in matching_topics(record, [topic])
            ]
            if relevant:
                corpus.upsert(relevant, topic)
                assigned += len(relevant)
        if next_cursor:
            new_cursor = next_cursor
        else:
            # A completed alphabetical partition starts from its beginning on
            # the next cycle, ensuring the forever loop keeps refreshing data.
            new_cursor = ""
        corpus.save_wikipedia_state(
            cursor_topic,
            team_key,
            new_cursor,
            total_hits,
            pages_harvested + page_count,
        )
        self.console.event(
            f"{team.name} crawler [{prefix_from or 'A'}-{prefix_to or 'Z'}]",
            f"{page_count} pages scanned · {inserted} new corpus entries · {assigned} topic matches · {pages_harvested + page_count:,} pages checkpointed",
            Ink.GREEN,
        )
        return inserted, bool(next_cursor)

    def run_harvest_once(
        self,
        corpus: ResearchCorpus,
        wikipedia_batch: int = DEFAULT_WIKIPEDIA_BATCH,
        catalog_topics: Sequence[str] | None = None,
    ) -> tuple[Path, list[Path]]:
        """Run one pass of the full-encyclopedia crawl and write matching findings."""
        self.console.section(
            "Harvest control",
            f"{len(WIKIPEDIA_PARTITIONS)} crawlers scanning all of Wikipedia A-Z in parallel · batch size {wikipedia_batch:,}",
        )
        with concurrent.futures.ThreadPoolExecutor(max_workers=len(WIKIPEDIA_PARTITIONS)) as pool:
            futures = {
                pool.submit(
                    self.harvest_wikipedia_partition,
                    corpus,
                    partition_index,
                    wikipedia_batch,
                    catalog_topics,
                ): partition_index
                for partition_index in range(len(WIKIPEDIA_PARTITIONS))
            }
            for future in concurrent.futures.as_completed(futures):
                partition_index = futures[future]
                try:
                    future.result()
                except Exception as exc:
                    self.console.warn(
                        f"partition {partition_index} crawler failed — checkpoint preserved ({compact(str(exc), 140)})"
                    )

        records = self.rank_and_dedupe(corpus.top_records(self.topic, limit=500))
        metadata = {
            "topic": self.topic,
            "generated_at": self.run_time.isoformat(),
            "mode": "autonomous_wikipedia_harvest",
            "teams": [dataclasses.asdict(team) for team in TEAMS],
            "sources_attempted": ["Wikipedia"],
            "entries_written": sum(1 for record in records if record.abstract.strip()),
            "corpus_entries_for_topic": corpus.count(self.topic),
            "corpus_entries_total": corpus.count(),
            "wikipedia_batch_size": wikipedia_batch,
        }
        discovery = self.write_discovery(records, metadata)
        entries = self.write_entry_files(records, metadata)
        self.console.success(
            f"topic corpus {corpus.count(self.topic):,} · total corpus {corpus.count():,}"
        )
        return discovery, entries

    def build_corpus_entries(self, corpus: ResearchCorpus) -> tuple[Path, list[Path]]:
        """Regenerate individual topic files from everything accumulated so far."""
        records = self.rank_and_dedupe(corpus.top_records(self.topic, limit=500))
        metadata = {
            "topic": self.topic,
            "generated_at": self.run_time.isoformat(),
            "mode": "autonomous_corpus_entries",
            "teams": [dataclasses.asdict(team) for team in TEAMS],
            "sources_attempted": ["Wikipedia"],
            "entries_written": sum(1 for record in records if record.abstract.strip()),
            "corpus_entries_for_topic": corpus.count(self.topic),
            "corpus_entries_total": corpus.count(),
        }
        discovery = self.write_discovery(records, metadata)
        entries = self.write_entry_files(records, metadata)
        return discovery, entries

    def discover(self) -> tuple[list[SourceRecord], dict[str, Any]]:
        if not self.console.topic:
            self.console.banner()
        self.console.section("Mission control", f"Topic: {Ink.paint(self.topic, Ink.CYAN)}")
        self.console.event("Coordinator", f"dispatching {len(TEAMS)} specialist teams", Ink.MAGENTA)
        for team in TEAMS:
            self.console.event(team.name, team.mission, Ink.BLUE if team.domain != "quality" else Ink.YELLOW)

        all_records: list[SourceRecord] = []
        failures: list[str] = []

        # Scholarly sources (OpenAlex, Crossref, arXiv, Semantic Scholar) are
        # queried ONCE per topic, on the plain topic string, instead of once
        # per team lens. Five near-duplicate lens queries against the same
        # topic were the main reason OpenAlex etc. were getting hit so hard;
        # one well-formed query already returns the same underlying works.
        # Wikipedia keeps its five lensed queries, since varied phrasing is
        # what actually broadens *encyclopedia* coverage.
        scholarly_jobs = {
            "Crossref": self.api.crossref,
            "OpenAlex": self.api.openalex,
            "arXiv": self.api.arxiv,
            "Semantic Scholar": self.api.semantic_scholar,
        }
        lens_teams = TEAMS[:5]
        wiki_queries = (
            {team: f"{self.topic} {team.lenses[0]}" for team in lens_teams}
            if self.include_wikipedia
            else {}
        )
        total_jobs = len(scholarly_jobs) + len(wiki_queries)
        with concurrent.futures.ThreadPoolExecutor(max_workers=max(total_jobs, 1)) as pool:
            scholarly_futures = {
                pool.submit(fetcher, self.topic): name for name, fetcher in scholarly_jobs.items()
            }
            wiki_futures = {
                pool.submit(self.api.wikipedia, query): team for team, query in wiki_queries.items()
            }
            for future in concurrent.futures.as_completed(scholarly_futures):
                name = scholarly_futures[future]
                try:
                    records = future.result()
                    all_records.extend(records)
                    self.console.event(name, f"{len(records)} candidate entries", Ink.GREEN)
                except Exception as exc:
                    message = compact(str(exc), 130)
                    failures.append(f"{name}: {message}")
                    self.console.warn(f"{name} unavailable — continuing ({message})")
            for future in concurrent.futures.as_completed(wiki_futures):
                team = wiki_futures[future]
                try:
                    records = future.result()
                    tagged = [dataclasses.replace(record, tags=unique((*record.tags, team.key))) for record in records]
                    all_records.extend(tagged)
                    self.console.event("Wikipedia", f"{len(records)} candidate entries ({team.name} lens)", Ink.GREEN)
                except Exception as exc:
                    message = compact(str(exc), 130)
                    failures.append(f"Wikipedia ({team.name}): {message}")
                    self.console.warn(f"Wikipedia ({team.name}) unavailable — continuing ({message})")

        ranked = self.rank_and_dedupe(all_records)
        metadata = {
            "topic": self.topic,
            "generated_at": self.run_time.isoformat(),
            "teams": [dataclasses.asdict(team) for team in TEAMS],
            "sources_attempted": ["Wikipedia", "Crossref", "OpenAlex", "arXiv", "Semantic Scholar"],
            "entries_found": len(ranked),
            "source_failures": unique(failures),
        }
        self.console.section("Evidence desk", "Deduplicating, scoring, and checking citation completeness")
        self.console.bar("unique records", len(ranked), max(len(all_records), 1))
        self.console.success(f"{len(ranked)} individual findings are ready to write")
        return ranked, metadata

    def rank_and_dedupe(self, records: Sequence[SourceRecord]) -> list[SourceRecord]:
        by_key: dict[str, SourceRecord] = {}
        query_terms = set(re.findall(r"[a-z0-9]{3,}", self.topic.lower()))
        current_year = self.run_time.year
        for record in records:
            title_terms = set(re.findall(r"[a-z0-9]{3,}", record.title.lower()))
            overlap = len(query_terms & title_terms) / max(len(query_terms), 1)
            recency = max(0, min(1, (int(record.year) - (current_year - 8)) / 8)) if record.year.isdigit() else 0.35
            provenance = {
                "OpenAlex": 0.92,
                "Crossref": 0.9,
                "Semantic Scholar": 0.84,
                "Wikipedia": 0.8,
                "arXiv": 0.72,
            }.get(record.source, 0.5)
            completeness = 0.1 * bool(record.abstract) + 0.1 * bool(record.authors) + 0.1 * bool(record.url)
            article_quality = 0.08 if record.source == "Wikipedia" and len(record.abstract) >= 500 else 0
            scored = dataclasses.replace(
                record,
                score=0.42 * overlap + 0.24 * recency + 0.2 * provenance + completeness + article_quality,
            )
            key = record.doi.lower().strip() or normalize_title(record.title)
            prior = by_key.get(key)
            if prior is None or scored.score > prior.score:
                by_key[key] = scored
        return sorted(by_key.values(), key=lambda record: (-record.score, record.year, record.title))

    def write_discovery(self, records: Sequence[SourceRecord], metadata: dict[str, Any]) -> Path | None:
        if not records:
            # Nothing genuinely matched this topic yet -- don't leave behind
            # an empty folder with just a discovery.json in it.
            return None
        folder = self.output / slugify(self.topic)
        folder.mkdir(parents=True, exist_ok=True)
        payload = {"metadata": metadata, "entries": [record.as_dict() for record in records]}
        path = folder / "discovery.json"
        path.write_text(json.dumps(payload, indent=2, ensure_ascii=False), encoding="utf-8")
        dashboard_file_written(path, "Discovery data", self.topic)
        return path

    def write_entry_files(self, records: Sequence[SourceRecord], metadata: dict[str, Any]) -> list[Path]:
        """Write one standalone Markdown summary for every research finding.

        A record with no abstract has nothing for format_summary() to teach
        from beyond a placeholder ("did not provide enough abstract text..."),
        so those records are skipped here rather than turned into a file.
        """
        records = [record for record in records if record.abstract.strip()]
        if not records:
            return []
        folder = self.output / slugify(self.topic)
        folder.mkdir(parents=True, exist_ok=True)
        legacy_book = folder / "quick_book.md"
        if legacy_book.exists():
            legacy_book.unlink()
        paths: list[Path] = []
        used_names: set[str] = set()
        for record in records:
            file_name = entry_filename(record.title)
            if file_name in used_names:
                file_name = f"{Path(file_name).stem}-{record.stable_id}.md"
            used_names.add(file_name)
            path = folder / file_name
            path.write_text(
                "\n".join(self._entry_markdown(record, metadata)) + "\n",
                encoding="utf-8",
            )
            dashboard_file_written(path, "Research finding", self.topic)
            paths.append(path)
        return paths

    def write_index(self) -> Path:
        self.output.mkdir(parents=True, exist_ok=True)
        for legacy_book in self.output.glob("*/quick_book.md"):
            legacy_book.unlink()
        entries = sorted(
            path for path in self.output.glob("*/*.md")
            if path.name != "discovery.md"
        )
        lines = [
            "# Research Library",
            "",
            "Individual research findings assembled by **Hex**.",
            "",
            "| Topic | Finding | Summary | Last updated |",
            "| --- | --- | --- | --- |",
        ]
        for entry in entries:
            topic = entry.parent.name.replace("-", " ").title()
            title = entry.stem
            updated = dt.datetime.fromtimestamp(entry.stat().st_mtime).date().isoformat()
            content = entry.read_text(encoding="utf-8")
            summary_match = re.search(
                r"## Summary\s*\n\n(.+?)(?:\n\n## |\Z)",
                content,
                flags=re.DOTALL,
            )
            summary = compact(summary_match.group(1), 180) if summary_match else ""
            relative_path = entry.relative_to(self.output).as_posix()
            safe_summary = summary.replace("|", "\\|").replace("\n", " ")
            lines.append(
                f"| {topic} | [{title}]({relative_path}) | "
                f"{safe_summary} | {updated} |"
            )
        if not entries:
            lines.append("| — | No individual findings yet | — | — |")
        index = self.output / "INDEX.md"
        index.write_text("\n".join(lines) + "\n", encoding="utf-8")
        dashboard_file_written(index, "Library index", self.topic)
        return index

    @staticmethod
    def _orientation(records: Sequence[SourceRecord]) -> str:
        if not records:
            return "No scholarly entries were available in this run. Re-run later or check the source failure notes."
        venues = unique(record.venue for record in records[:8])
        newest = next((record.year for record in records if record.year.isdigit()), "n.d.")
        return (
            f"This volume contains **{len(records)}** ranked entries, with the newest surfaced work dated **{newest}**. "
            f"Early source venues include {', '.join(venues[:4]) or 'multiple scholarly indexes'}. "
            "Read the abstracts as short orientation notes, then open the original links for full methods, results, and limitations."
        )

    @staticmethod
    def _entry_markdown(record: SourceRecord, metadata: dict[str, Any]) -> list[str]:
        authors = ", ".join(record.authors[:6]) or "Author information unavailable"
        citation = f"{authors}. ({record.year}). [{record.title}]({record.url or '#'})"
        if record.venue:
            citation += f". *{record.venue}*."
        if record.doi:
            citation += f" DOI: `{record.doi}`."
        summary = format_summary(
            record.abstract,
            title=record.title,
            source=record.source,
            record_type=record.record_type,
            venue=record.venue,
        )
        return [
            f"# {record.title}",
            "",
            "## Summary",
            "",
            summary,
            "",
            "## Source & citation",
            "",
            citation,
        ]

    def run_once(self, update_index: bool = True) -> None:
        records, metadata = self.discover()
        if self.corpus:
            self.corpus.upsert(records, self.topic)
            records = self.corpus.top_records(self.topic, limit=300)
            records = self.rank_and_dedupe(records)
            metadata["corpus_entries_for_topic"] = self.corpus.count(self.topic)
            metadata["corpus_entries_total"] = self.corpus.count()
        discovery = self.write_discovery(records, metadata)
        entries = self.write_entry_files(records, metadata)
        index = self.write_index() if update_index else None
        self.console.section("Library update")
        if entries:
            self.console.success(f"individual findings  {len(entries)} files in {self.output / slugify(self.topic)}")
            self.console.success(f"raw records {discovery}")
        else:
            self.console.warn(f"no genuine matches for '{self.topic}' this run — nothing written")
        if index:
            self.console.success(f"index       {index}")


def run_topics(
    topics: Sequence[str],
    command: str,
    output: Path,
    max_results: int,
    timeout: int,
    console: Console,
    max_concurrent: int = DEFAULT_TOPIC_CONCURRENCY,
) -> None:
    """Run separate topic coordinators concurrently, then rebuild one index."""
    clean_topics = unique(topic.strip() for topic in topics if topic.strip())
    if not clean_topics:
        raise ValueError("At least one non-empty topic is required.")

    console.section(
        "Parallel launch",
        f"{len(clean_topics)} topics running simultaneously with independent agent teams",
    )
    for topic in clean_topics:
        console.event("Queued", topic, Ink.MAGENTA)

    def work(topic: str) -> str:
        coordinator = ResearchCoordinator(topic, output, max_results, timeout)
        coordinator.run_once(update_index=False)
        return topic

    completed = 0
    worker_count = max(1, min(max_concurrent, len(clean_topics)))
    with concurrent.futures.ThreadPoolExecutor(max_workers=worker_count) as pool:
        futures = {pool.submit(work, topic): topic for topic in clean_topics}
        for future in concurrent.futures.as_completed(futures):
            topic = futures[future]
            try:
                future.result()
                completed += 1
                console.success(f"Completed {topic} ({completed}/{len(clean_topics)})")
            except Exception as exc:
                console.error(f"{topic} failed: {compact(str(exc), 150)}")

    index = ResearchCoordinator(clean_topics[0], output, max_results, timeout).write_index()
    console.section("Parallel run complete")
    console.success(f"{completed}/{len(clean_topics)} topics finished")
    console.success(f"combined index  {index}")


def run_wikipedia_harvest_forever(
    output: Path,
    timeout: int,
    batch_size: int,
    catalog_topics: Sequence[str],
    console: Console,
    pause_seconds: float = 2.0,
    stop_event: threading.Event | None = None,
) -> None:
    """Continuously crawl the entire English Wikipedia in the background.

    This walks every non-redirect article A-Z using all seven
    WIKIPEDIA_PARTITIONS in parallel, checkpointed in the shared corpus so
    the crawl always resumes where it left off — and loops back to "A" once
    it reaches the end, to pick up new and edited articles. It runs on its
    own tight loop rather than the topic-rotation --interval, so coverage of
    "the whole Wikipedia" is not throttled to one small batch every few
    hours. Every page is matched against the full standing topic catalog as
    it's crawled, so all subjects benefit from the same pass.
    """
    corpus = ResearchCorpus(output)
    harvester = ResearchCoordinator("__wikipedia_harvest__", output, timeout=timeout, corpus=corpus)
    harvester.console = console
    cycle = 0
    while not (stop_event and stop_event.is_set()):
        cycle += 1
        with concurrent.futures.ThreadPoolExecutor(max_workers=len(WIKIPEDIA_PARTITIONS)) as pool:
            futures = [
                pool.submit(harvester.harvest_wikipedia_partition, corpus, index, batch_size, catalog_topics)
                for index in range(len(WIKIPEDIA_PARTITIONS))
            ]
            for future in concurrent.futures.as_completed(futures):
                try:
                    future.result()
                except Exception as exc:
                    console.warn(f"Wikipedia harvest partition failed — checkpoint preserved ({compact(str(exc), 140)})")
        if cycle % 10 == 0:
            console.event(
                "Wikipedia harvest",
                f"{corpus.count():,} corpus entries after {cycle} crawl cycles across {len(catalog_topics)} topics",
                Ink.CYAN,
            )
            for topic in catalog_topics:
                try:
                    ResearchCoordinator(topic, output, timeout=timeout, corpus=corpus).build_corpus_entries(corpus)
                except Exception as exc:
                    console.warn(f"Rebuilding {topic} from the corpus failed ({compact(str(exc), 120)})")
        time.sleep(pause_seconds)


def start_wikipedia_harvest_thread(
    output: Path,
    timeout: int,
    batch_size: int,
    catalog_topics: Sequence[str],
    console: Console,
) -> threading.Thread:
    """Launch the full-Wikipedia crawl as a daemon thread and return it."""
    thread = threading.Thread(
        target=run_wikipedia_harvest_forever,
        args=(output, timeout, batch_size, catalog_topics, console),
        daemon=True,
        name="wikipedia-harvest",
    )
    thread.start()
    return thread


def run_autonomous(
    output: Path,
    max_results: int,
    timeout: int,
    interval: float,
    max_concurrent: int,
    console: Console,
    wikipedia_batch: int = DEFAULT_WIKIPEDIA_BATCH,
    harvest_wikipedia: bool = True,
) -> None:
    """Run the standing catalog forever, rotating topics through worker slots."""
    catalog = list(AUTONOMOUS_TOPICS)
    cursor = 0
    cycle = 1
    console.banner()
    console.event(
        "Autonomous mode",
        f"{len(catalog)} subjects queued; {max_concurrent} topics work in parallel; runs forever",
        Ink.MAGENTA,
    )
    console.event(
        "Research loop",
        "Wikipedia and scholarly sources are searched continuously; press Ctrl+C to stop",
        Ink.CYAN,
    )
    if harvest_wikipedia:
        start_wikipedia_harvest_thread(output, timeout, wikipedia_batch, catalog, console)
        console.event(
            "Wikipedia harvest",
            f"background crawl started · all {len(WIKIPEDIA_PARTITIONS)} A-Z partitions · batch size {wikipedia_batch:,}",
            Ink.MAGENTA,
        )
    try:
        while True:
            batch = catalog[cursor : cursor + max_concurrent]
            if len(batch) < max_concurrent:
                batch += catalog[: max_concurrent - len(batch)]
            console.section(
                f"Autonomous cycle {cycle}",
                f"working on batch {cursor + 1}-{min(cursor + max_concurrent, len(catalog))} of {len(catalog)}",
            )
            run_topics(
                batch,
                "build",
                output,
                max_results,
                timeout,
                console,
                max_concurrent=max_concurrent,
            )
            cursor = (cursor + max_concurrent) % len(catalog)
            if cursor == 0:
                console.success("The full subject catalog has been refreshed; starting the next rotation.")
            console.event("Scheduler", f"next batch in {interval:g} hour(s)", Ink.DIM)
            cycle += 1
            time.sleep(interval * 60 * 60)
    except KeyboardInterrupt:
        console.success("Autonomous mode stopped. Everything already written to the library is preserved.")


def parse_args(argv: Sequence[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Coordinate scholarly research teams and write cited individual research findings.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=textwrap.dedent(
            """
            Examples:
              %(prog)s
              %(prog)s --interval 6
              %(prog)s build --topic "biology" --topic "algebra" --topic "history"
              %(prog)s discover --topic "linear algebra" --output books --max-results 12
              %(prog)s watch --topic "educational psychology" --interval 12
              %(prog)s build --topic "biology" --browser chrome
            """
        ),
    )
    parser.add_argument(
        "command",
        nargs="?",
        choices=("discover", "build", "watch", "harvest"),
        help="run one collection, keep a topic under watch, or crawl all of Wikipedia (harvest)",
    )
    parser.add_argument(
        "--topic",
        action="append",
        default=[],
        help="topic to research; repeat this option to run multiple topics simultaneously",
    )
    parser.add_argument(
        "--output",
        default=DEFAULT_OUTPUT,
        help=(
            f"folder for findings and records; relative paths are created beside "
            f"this script (default: {DEFAULT_OUTPUT})"
        ),
    )
    parser.add_argument("--max-results", type=int, default=8, help="results per source and team (default: 8)")
    parser.add_argument("--timeout", type=int, default=18, help="network timeout in seconds (default: 18)")
    parser.add_argument("--interval", type=float, default=DEFAULT_INTERVAL_HOURS, help="autonomous/watch interval in hours (default: 6)")
    parser.add_argument(
        "--topic-concurrency",
        type=int,
        default=DEFAULT_TOPIC_CONCURRENCY,
        help=f"number of subjects worked on at once in autonomous mode (default: {DEFAULT_TOPIC_CONCURRENCY})",
    )
    parser.add_argument(
        "--browser",
        choices=("default", "chrome", "firefox", "edge", "brave"),
        default="default",
        help="browser for the live dashboard (default: system browser)",
    )
    parser.add_argument(
        "--terminal-only",
        action="store_true",
        help="disable the live dashboard and use terminal output only",
    )
    parser.add_argument(
        "--wikipedia-batch",
        type=int,
        default=DEFAULT_WIKIPEDIA_BATCH,
        help=f"pages fetched per crawler per cycle while harvesting all of Wikipedia (default: {DEFAULT_WIKIPEDIA_BATCH})",
    )
    parser.add_argument(
        "--no-wikipedia-harvest",
        action="store_true",
        help="disable the background full-Wikipedia crawl during autonomous mode",
    )
    parser.add_argument("--version", action="version", version=f"%(prog)s {VERSION}")
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    raw_argv = list(argv) if argv is not None else sys.argv[1:]
    global _DASHBOARD
    dashboard_server: DashboardServer | None = None
    try:
        install_startup_dependencies()
        args = parse_args(raw_argv)
        if args.max_results < 1 or args.max_results > 50:
            print("--max-results must be between 1 and 50.", file=sys.stderr)
            return 2
        if args.interval <= 0:
            print("--interval must be greater than zero.", file=sys.stderr)
            return 2
        if args.topic_concurrency < 1 or args.topic_concurrency > len(AUTONOMOUS_TOPICS):
            print(
                f"--topic-concurrency must be between 1 and {len(AUTONOMOUS_TOPICS)}.",
                file=sys.stderr,
            )
            return 2

        if not args.terminal_only:
            state = DashboardState()
            _DASHBOARD = state
            if args.topic:
                state.set_topic(" · ".join(args.topic))
            dashboard_server = DashboardServer(state, args.browser)
            dashboard_url = dashboard_server.start()
            dashboard_publish(
                "system",
                "Coordinator",
                f"Dashboard open at {dashboard_url} — research agents are ready.",
            )

        console = Console()
        if args.command in ("discover", "build") and args.topic:
            run_topics(
                args.topic,
                args.command,
                resolve_output_path(args.output),
                args.max_results,
                args.timeout,
                console,
                max_concurrent=args.topic_concurrency,
            )
            if dashboard_server:
                dashboard_server.wait_forever()
            return 0

        if args.command == "watch" and args.topic:
            console.banner()
            console.event("Watch mode", f"refreshing {len(args.topic)} topic(s) every {args.interval:g} hour(s); press Ctrl+C to stop", Ink.MAGENTA)
            while True:
                run_topics(
                    args.topic,
                    "build",
                    resolve_output_path(args.output),
                    args.max_results,
                    args.timeout,
                    console,
                    max_concurrent=args.topic_concurrency,
                )
                console.event("Scheduler", f"next parallel run in {args.interval:g} hour(s)", Ink.DIM)
                time.sleep(args.interval * 60 * 60)

        if args.command == "harvest":
            console.banner()
            console.event(
                "Harvest mode",
                f"crawling the entire English Wikipedia across all {len(WIKIPEDIA_PARTITIONS)} A-Z partitions; "
                "press Ctrl+C to stop",
                Ink.MAGENTA,
            )
            run_wikipedia_harvest_forever(
                resolve_output_path(args.output),
                args.timeout,
                args.wikipedia_batch,
                list(AUTONOMOUS_TOPICS),
                console,
            )
            return 0

        run_autonomous(
            resolve_output_path(args.output),
            args.max_results,
            args.timeout,
            args.interval,
            args.topic_concurrency,
            console,
            wikipedia_batch=args.wikipedia_batch,
            harvest_wikipedia=not args.no_wikipedia_harvest,
        )
        return 0
    except KeyboardInterrupt:
        print("\nStopped before the run completed.")
        return 130
    except Exception as exc:
        print(f"\nHex could not start: {exc}", file=sys.stderr)
        if "--debug" in raw_argv:
            traceback.print_exc()
        else:
            print("Run again with --debug to see the technical traceback.", file=sys.stderr)
        return 1
    finally:
        if dashboard_server:
            dashboard_server.stop()
        _DASHBOARD = None


if __name__ == "__main__":
    raise SystemExit(main())