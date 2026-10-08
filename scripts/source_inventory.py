#!/usr/bin/env python3
"""Index candidate numbered statement labels in a local pdftotext extraction.

These are navigation candidates, not proof-coverage claims. A label can occur in
running prose or a proof reference. Keep reviewed coverage in the accompanying
Markdown audit rather than editing this generated file.
"""
import argparse
import hashlib
import json
import re
from pathlib import Path


def inventory(source: Path) -> dict:
    raw = source.read_bytes()
    text = raw.decode("utf-8")
    pattern = re.compile(
        r"(?m)^\s*(Theorem|Lemma|Proposition|Corollary)\s+((?:\d+|[A-I])\.\d+)\b"
    )
    labels = {}
    for match in pattern.finditer(text):
        key = (match[1], match[2])
        position = match.start(1)
        labels.setdefault(key, []).append({
            "line": text.count("\n", 0, position) + 1,
            "text_page": text.count("\f", 0, position) + 1,
        })

    def order(item):
        kind, number = item[0]
        section, index = number.split(".")
        return (0, int(section), int(index), kind) if section.isdigit() else (
            1, section, int(index), kind
        )

    return {
        "source_url": "https://janbernloehr.de/Download/fs16/diss.pdf",
        "extracted_text_sha256": hashlib.sha256(raw).hexdigest(),
        "scope": "Candidate labels only; occurrences require manual statement verification.",
        "page_convention": "One-based count of form-feed-separated pages in the input text.",
        "candidates": [
            {"kind": kind, "number": number, "occurrences": occurrences}
            for (kind, number), occurrences in sorted(labels.items(), key=order)
        ],
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path, help="Local dissertation text extraction")
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--check", action="store_true", help="Verify the saved inventory without editing")
    args = parser.parse_args()
    data = inventory(args.source)
    rendered = json.dumps(data, ensure_ascii=False, indent=2) + "\n"
    if args.check:
        if args.output.read_text(encoding="utf-8") != rendered:
            raise SystemExit("Saved statement inventory differs from the supplied extraction.")
    else:
        args.output.write_text(rendered, encoding="utf-8")
    print(f"{'Verified' if args.check else 'Indexed'} {len(data['candidates'])} candidate statement labels.")


if __name__ == "__main__":
    main()
