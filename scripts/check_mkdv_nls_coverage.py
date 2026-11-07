#!/usr/bin/env python3
"""Check the whole-paper inventory; optionally require every obligation closed.

This checks inventory integrity, not the mathematical correspondence of a Lean
statement with the source. Correspondence review and Lean validation remain
separate requirements. The private pinned text can verify passage locators.
"""
import argparse
import hashlib
import json
from pathlib import Path

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--source-text', type=Path)
parser.add_argument('--require-complete', action='store_true')
args = parser.parse_args()
root = Path(__file__).resolve().parent.parent
ledger = json.loads((root / 'coverage/articles/mkdv-nls-hierarchies/full-paper-coverage.json').read_text())
assertions = ledger['assertions']
passages = ledger['passages']
ids = [a['id'] for a in assertions]
assert len(ids) == len(set(ids)) == ledger['assertion_count']
named = [a for a in assertions if a['kind'] == 'named_statement']
expected = ({f'Theorem {n}' for n in range(1, 7)} |
            {f'Lemma {n}' for n in [2, 3, 4, 5, 7, 10, 13, 14]} |
            {'Proposition 6', 'Proposition 11', 'Corollary 8', 'Corollary 9'})
assert {a['label'] for a in named} == expected
assert len(named) == ledger['named_statement_count'] == 18
numbered = [a for a in assertions if a['kind'] == 'numbered_equation']
assert {a['label'] for a in numbered} == {f'({n})' for n in range(1, 26)}
assert len(numbered) == ledger['numbered_equation_count'] == 25
for a in assertions:
    assert ledger['scope_first_line'] <= a['line'] <= ledger['scope_last_line']
    assert 1 <= a['page'] <= 19
    if a['status'].startswith('proved'):
        assert a['declarations'], f"Missing checked correspondence: {a['id']}"
assert len(passages) == ledger['passage_count']
assert len({p['id'] for p in passages}) == len(passages)
last = ledger['scope_first_line'] - 1
for p in passages:
    assert last < p['first_line'] <= p['last_line'] <= ledger['scope_last_line']
    assert set(p['assertion_ids']) <= set(ids)
    last = p['last_line']
if args.source_text:
    raw = args.source_text.read_bytes()
    assert hashlib.sha256(raw).hexdigest() == ledger['source_text_sha256']
    lines = raw.decode().split('\n')
    actual = set()
    for p in passages:
        first, last = p['first_line'], p['last_line']
        source = '\n'.join(lines[first - 1:last])
        assert hashlib.sha256(source.encode()).hexdigest() == p['source_sha256']
        assert 1 + '\n'.join(lines[:first]).count('\f') == p['page']
        actual.update(i for i in range(first, last + 1) if lines[i - 1].strip())
    expected_lines = {i for i in range(ledger['scope_first_line'], ledger['scope_last_line'] + 1)
                      if lines[i - 1].strip()}
    assert actual == expected_lines, 'Mathematical-body passages omitted or duplicated'
closed = lambda status: status.startswith('proved') or status == 'nonmathematical_metadata'
pending_assertions = sum(not closed(a['status']) for a in assertions)
pending_passages = sum(not closed(p['status']) for p in passages)
complete = (ledger['semantic_inventory_complete'] and pending_assertions == 0 and pending_passages == 0)
if ledger['status'] == 'complete' or args.require_complete:
    if not complete:
        parser.error(f'Whole-paper verification incomplete: {pending_assertions} assertion records and '
                     f'{pending_passages} passages remain open; semantic inventory complete = '
                     f"{ledger['semantic_inventory_complete']}")
print(f'Inventory valid: {len(named)} named statements, {len(numbered)} numbered equations, '
      f'{len(assertions)} assertion records, {len(passages)} source passages. '
      f'Whole-paper status: {ledger["status"]}.')
