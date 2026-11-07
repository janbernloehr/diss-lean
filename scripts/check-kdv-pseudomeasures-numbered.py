#!/usr/bin/env python3
"""Check the paper's complete numbered-result ledger against its source and Lean API.

This checks coverage-record integrity; it does not turn partial source matches
into full proofs. Run the strict Lean/axiom checker for proof validation.
"""
from pathlib import Path
import argparse,collections,hashlib,json,re
p=argparse.ArgumentParser()
p.add_argument('--paper-text',type=Path,required=True)
p.add_argument('--paper-pdf',type=Path)
a=p.parse_args()
root=Path('coverage/articles/kdv-pseudomeasures')
d=json.loads((root/'numbered-results.json').read_text())
expected={
 'Theorem':['1.1','1.3','1.4','2.1','2.2','3.1','3.2','5.1','5.2','5.3','5.9'],
 'Lemma':['2.4','2.7','2.9','2.10','2.11','2.12','2.13','2.14','2.15','2.16','2.17','2.20','2.21',
          '3.3','3.4','3.5','3.6','3.7','3.9','5.4','5.5','5.6','5.7','5.8','A.1','A.2','A.3','A.4','B.1','C.1','C.2','C.3','C.4'],
 'Proposition':['2.18','2.19'], 'Corollary':['2.5','3.8'],
 'Remark':['1.2','1.5','2.3','2.6','2.8','C.5']}
labels={f'{kind} {n}' for kind,ns in expected.items() for n in ns}
rows=d['results'];assert len(rows)==len(labels)==54
assert {r['label'] for r in rows}==labels
assert d['formal_results']==48 and d['remarks']==6 and d['total_numbered_results']==54
actual_counts = collections.Counter(r['status'] for r in rows)
assert all(d['status_counts'].get(k, 0) == actual_counts.get(k, 0)
           for k in set(d['status_counts']) | set(actual_counts))
assert not d['complete_numbered_result_proof_coverage'] or all(r['status'] in {'proved','proved_corrected'} for r in rows)
pages=a.paper_text.read_text().split('\f')
api=set(re.findall(r'^#print axioms (\S+)',Path('NLS/Articles/KdVPseudomeasures/Audit.lean').read_text(),re.M))
for r in rows:
 assert r['status'] in {'proved','proved_corrected','partial','not_found','false_as_printed','in_progress'},r['label']
 assert hashlib.sha256(r['statement'].encode()).hexdigest()==r['statement_sha256'],r['label']
 assert r['statement'].splitlines()[0] in pages[r['source_page']-1],r['label']
 assert r['comparison'] and r['statement'].startswith(r['label']),r['label']
 for f in r['providers']:
  assert Path(f).is_file(),f
  assert hashlib.sha256(Path(f).read_bytes()).hexdigest()==r['provider_sha256'][f],f
 for name in r.get('declarations',[])+r.get('counterexample_declarations',[]):
  assert name in api,(r['label'],name)
for label in ['Theorem 1.1','Theorem 1.3','Theorem 1.4','Theorem 5.1','Theorem 5.9','Lemma 5.7']:
 assert next(r['status'] for r in rows if r['label']==label) in {'proved','proved_corrected'}
a4=next(r for r in rows if r['label']=='Lemma A.4')
assert a4['printed_statement_status']=='false_as_printed' and a4['replacement_authorized_by_user']
assert 'NLS.Articles.KdVPseudomeasures.sourceLemmaA_4_innerBall' in a4['declarations']
l15=next(r for r in rows if r['label']=='Lemma 2.15')
assert l15['status']=='proved' and 'already' in l15['comparison']
if a.paper_pdf:
 assert hashlib.sha256(a.paper_pdf.read_bytes()).hexdigest()==d['source_pdf_sha256']
print(json.dumps({'numbered_results':54,'formal_results':48,'remarks':6,
 'status_counts':d['status_counts'],'complete_numbered_result_proof_coverage':d['complete_numbered_result_proof_coverage'],
 'source_labels_pages_hashes_and_declarations':'passed'},indent=2))
