#!/usr/bin/env python3
"""Check the merged library aggregate, KdV main statements and all relevant article axiom audits.

Run from the repository root. Cached imports are read-only; all outputs and
source-fingerprint-checked resume state live under .lake/pr5-merge-check.
The optional premerge snapshot/inventory permit reuse of validated local
objects. Without those options, only source-identical canonical dependencies
are reused. Compilation uses the pinned toolchain and warnings as errors.
"""
from pathlib import Path
import argparse,ast,asyncio,hashlib,json,os,re,subprocess,time

parser=argparse.ArgumentParser()
parser.add_argument('--jobs',type=int,default=3)
parser.set_defaults(plan_only=False)
parser.add_argument('--reference',type=Path,required=True,help='Read-only checkout with pinned mathlib and cached imports')
parser.add_argument('--lean',type=Path,required=True,help='Pinned Lean4.33.1 executable')
parser.add_argument('--prior-cache',type=Path,help='Previously validated private lib/lean directory')
parser.add_argument('--premerge-snapshot',type=Path,help='JSON with premerge Lean_sources SHA256 mapping')
parser.add_argument('--baseline-inventory',type=Path,help='Validated baseline JSON with source_sha256 mapping')
args=parser.parse_args()
if args.jobs < 1:parser.error('--jobs must be positive')
root=Path.cwd().resolve()
reference=args.reference.resolve()
prior=args.prior_cache.resolve() if args.prior_cache else reference/'.lake/build/lib/lean'
build=root/'.lake/pr5-merge-check';view=build/'lib/lean';logs=build/'logs'
assert build.resolve().is_relative_to(root),build
for p in [view,logs]:p.mkdir(parents=True,exist_ok=True)
lean=args.lean.resolve()
assert lean.is_file()
version=subprocess.check_output([str(lean),'--version'],text=True).strip()
assert version.startswith('Lean (version 4.33.1,'),version
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def save(p,d):p.write_text(json.dumps(d,indent=2)+'\n')
snapshot=json.loads(args.premerge_snapshot.read_text()) if args.premerge_snapshot else {'Lean_sources':{}}
inventory=json.loads(args.baseline_inventory.read_text()) if args.baseline_inventory else {'source_sha256':{}}
cache_hashes=inventory['source_sha256']
sources={'.'.join(p.with_suffix('').parts):p for p in Path('NLS').rglob('*.lean')}
sources['NLS']=Path('NLS.lean')
audit_script='scripts.CheckMKdVNLSHierarchiesAxioms'
sources[audit_script]=Path('scripts/CheckMKdVNLSHierarchiesAxioms.lean')
estimates_audit='coverage.articles.kdv-estimates.CheckPrivateAxioms'
sources[estimates_audit]=Path('coverage/articles/kdv-estimates/CheckPrivateAxioms.lean')
imports={m:re.findall(r'^(?:public )?import (\S+)',p.read_text(),re.M) for m,p in sources.items()}
own_deps={m:[d for d in ds if d in sources] for m,ds in imports.items()}
roots=['NLS','NLS.Articles.KdVPseudomeasures.Audit',audit_script,
       'NLS.Articles.MKdVBelowL2.AxiomAudit','NLS.MKdV.JointlySmoothClassicalTrajectory',
       'NLS.Articles.MKdVBelowL2.FourthClassicalUniqueness',estimates_audit,
       'NLS.Articles.KdVEstimates.MainBirkhoffEstimates']
selected=[];seen=set();active=[]
def visit(m):
 if m in seen:return
 assert m not in active,(m,active)
 active.append(m)
 for d in own_deps[m]:visit(d)
 active.pop();seen.add(m);selected.append(m)
for m in roots:visit(m)
hashes={m:digest(sources[m]) for m in selected}
changed={m for m in selected if str(sources[m]) in snapshot['Lean_sources'] and
 hashes[m]!=snapshot['Lean_sources'][str(sources[m])]}
affected={}
def is_affected(m):
 if m not in affected:affected[m]=m in changed or any(is_affected(d) for d in own_deps[m])
 return affected[m]
safe_canonical={}
def canonical_safe(m):
 if m in safe_canonical:return safe_canonical[m]
 p=reference/sources[m]
 safe_canonical[m]=p.is_file() and digest(p)==hashes[m] and all(canonical_safe(d) for d in own_deps[m])
 return safe_canonical[m]
fingerprints={}
def fingerprint(m):
 if m not in fingerprints:
  text=hashes[m]+''.join(fingerprint(d) for d in own_deps[m])+'Lean4.33.1:autoImplicit=false:warningAsError=true'
  fingerprints[m]=hashlib.sha256(text.encode()).hexdigest()
 return fingerprints[m]
checkpoint_path=build/'checkpoint.json'
checkpoint=json.loads(checkpoint_path.read_text()) if checkpoint_path.is_file() else {}
def output(m):return (view/Path(*m.split('.'))).with_suffix('.olean')
def cache_output(base,m):return (base/Path(*m.split('.'))).with_suffix('.olean')
conflicts=set(['NLS', 'NLS.ComplexAnalysis.QuadraticEnergySheet', 'NLS.ComplexAnalysis.TwoEndpointRoot', 'NLS.ComplexAnalysis.TwoRootCircleMoments', 'NLS.ComplexAnalysis.ZeroCountContinuousFamily', 'NLS.Fourier.UnitIntervalWeakDerivative', 'NLS.KdV.ClassicalHillTraceFamily', 'NLS.KdV.HillContinuousPrimitiveComparison', 'NLS.KdV.HillDiscriminantGardnerCommutation', 'NLS.KdV.HillFullPeriodKernelInjectivity', 'NLS.KdV.HillHminusOneMiuraAllLabels', 'NLS.KdV.HillHminusOneMiuraContour', 'NLS.KdV.HillHminusOneMiuraSheets', 'NLS.KdV.HillL2Dirichlet', 'NLS.KdV.HillL2DirichletTerminal', 'NLS.KdV.HillMiuraL2Discriminant', 'NLS.KdV.HillMiuraPositiveGaps', 'NLS.KdV.HillMiuraSquaredEnumeration', 'NLS.KdV.HminusOneMiuraHighPairs', 'NLS.KdV.MiuraHillPsiNumerators', 'NLS.KdV.MiuraL2DirichletAuxiliary', 'NLS.KdV.MiuraPeriodicReflection', 'NLS.MKdV.QuasiHillEnergyEmbedding', 'NLS.MKdV.QuasiHillL2Sobolev', 'NLS.Poisson.GardnerBivector', 'NLS.Poisson.GardnerBracketJacobi', 'NLS.Poisson.GardnerHamiltonianDirection', 'NLS.Poisson.GardnerHamiltonianZeroMode', 'NLS.Poisson.HminusGardnerBracket'])
forced=set(roots)|conflicts|{f'NLS.Articles.KdVPseudomeasures.MainTheorem{x}' for x in ['11','13','14','51','59']}
reuse={};pending=set()
for m in selected:
 o=output(m);fp=fingerprint(m)
 if (checkpoint.get(m,{}).get('fingerprint')==fp and
     checkpoint[m].get('source_sha256')==hashes[m] and o.is_file() and not o.is_symlink()):
  reuse[m]='freshly compiled in this merge validation';continue
 if m not in forced and not is_affected(m):
  p=prior/Path(*m.split('.'));p=p.with_suffix('.olean')
  if cache_hashes.get(str(sources[m]))==hashes[m] and p.is_file() and p.resolve()!=o.absolute():
   reuse[m]=str(p.resolve());continue
  p=cache_output(reference/'.lake/build/lib/lean',m)
  if p.is_file() and canonical_safe(m):reuse[m]=str(p);continue
 pending.add(m)
for m,src in reuse.items():
 if src=='freshly compiled in this merge validation':continue
 o=output(m);o.parent.mkdir(parents=True,exist_ok=True)
 if o.is_symlink() or o.exists():o.unlink()
 o.symlink_to(Path(src).resolve())
for m in pending:
 o=output(m);o.parent.mkdir(parents=True,exist_ok=True)
 if o.is_symlink() or o.exists():o.unlink()
 assert o.parent.resolve().is_relative_to(build.resolve())
# Mathlib reference objects stay read-only; create private slots only for absent objects.
def local_directory(p):
 if p.is_symlink():
  base=p.resolve();p.unlink();p.mkdir()
  for q in base.iterdir():(p/q.name).symlink_to(q.resolve(),target_is_directory=q.is_dir())
 else:p.mkdir(parents=True,exist_ok=True)
local_directory(view/'Mathlib')
mathlib=reference/'.lake/packages/mathlib'
mathlib_cache=prior/'Mathlib'
if not mathlib_cache.is_dir():mathlib_cache=mathlib/'.lake/build/lib/lean/Mathlib'
for p in mathlib_cache.iterdir():
 q=view/'Mathlib'/p.name
 if not q.exists() and not q.is_symlink():q.symlink_to(p.resolve(),target_is_directory=p.is_dir())
mathlib_pending=[];mathlib_seen=set()
def ensure_mathlib(m):
 if not m.startswith('Mathlib.') or m in mathlib_seen:return
 mathlib_seen.add(m)
 rel=Path(*m.split('.'));o=(view/rel).with_suffix('.olean')
 if o.is_file() or (mathlib/'.lake/build/lib/lean'/rel).with_suffix('.olean').is_file():return
 p=(mathlib/rel).with_suffix('.lean');assert p.is_file(),m
 for d in re.findall(r'^(?:public )?import (\S+)',p.read_text(),re.M):ensure_mathlib(d)
 for parent in reversed(rel.parents):local_directory(view/parent)
 if o.is_symlink():o.unlink()
 mathlib_pending.append(m)
for m in selected:
 for d in imports[m]:ensure_mathlib(d)
paths=[view]+sorted((reference/'.lake/packages').glob('*/.lake/build/lib/lean'))
env=dict(os.environ,LEAN_PATH=':'.join(map(str,paths)))
plan=dict(roots=roots,modules=len(selected),compile_now=len(pending),reused=len(reuse),
 affected_sources=len(changed),affected_closure=sum(is_affected(m) for m in selected),
 forced=sorted(forced),mathlib_missing=mathlib_pending,selected=selected,
 source_sha256={str(sources[m]):hashes[m] for m in selected},fingerprints=fingerprints,
 compiled_module_names=[m for m in selected if m in pending],reused_modules=reuse)
save(build/'plan.json',plan)
print(json.dumps({k:plan[k] for k in ['modules','compile_now','reused','affected_sources','affected_closure','mathlib_missing']},indent=2),flush=True)
if args.plan_only:raise SystemExit(0)

async def compile_module(m,*,upstream=False):
 start=time.monotonic();o=output(m);o.parent.mkdir(parents=True,exist_ok=True)
 assert not o.is_symlink() and o.parent.resolve().is_relative_to(build.resolve())
 source=(mathlib/Path(*m.split('.'))).with_suffix('.lean') if upstream else root/sources[m]
 command=[str(lean),'-DwarningAsError=true']
 if not upstream:command+=['-DautoImplicit=false']
 command+=['--root',str(mathlib if upstream else root),'-o',str(o),str(source)]
 proc=await asyncio.create_subprocess_exec(*command,cwd=root,env=env,stdout=asyncio.subprocess.PIPE,stderr=asyncio.subprocess.STDOUT)
 out,_=await proc.communicate();data=out.decode(errors='replace')
 log=logs/(m+'.log');log.write_text(data)
 row=dict(exit_code=proc.returncode,seconds=round(time.monotonic()-start,2),source_sha256=digest(source),log_sha256=hashlib.sha256(out).hexdigest())
 if not upstream:row['fingerprint']=fingerprint(m)
 if proc.returncode==0:
  checkpoint[m]=row;save(checkpoint_path,checkpoint)
 print(f'{m} exit: {proc.returncode} ({row["seconds"]}s)',flush=True)
 if proc.returncode:print(data[-14000:],flush=True)
 return proc.returncode

def exact_axiom_audit(module):
 audit=sources[module].read_text()
 expected=re.findall(r'^#print axioms (\S+)',audit,re.M)
 text=(logs/(module+'.log')).read_text()
 reports=re.findall(r"'([^']+)' depends on axioms: \[(.*?)\]",text,re.S)
 reports += [(name,'') for name in re.findall(r"'([^']+)' does not depend on any axioms",text)]
 assert len(expected)==len(set(expected))==len(reports), 'Axiom audit inventory mismatch'
 assert set(expected)=={name for name,_ in reports}, 'Missing or unexpected axiom reports'
 allowed={'propext','Classical.choice','Quot.sound'}
 for name,axioms in reports:
  assert {a.strip() for a in axioms.split(',') if a.strip()} <= allowed, (name,axioms)
 return len(reports)

def validate_axiom_logs():
 article=exact_axiom_audit('NLS.Articles.KdVPseudomeasures.Audit')
 below_l2=exact_axiom_audit('NLS.Articles.MKdVBelowL2.AxiomAudit')
 estimates=(logs/(estimates_audit+'.log')).read_text()
 estimates_match=re.search(r'KdV foundation: transitive axiom audit passed for (\d+) declarations',estimates)
 assert estimates_match, 'KdV estimates foundation audit did not report success'
 hierarchy=(logs/(audit_script+'.log')).read_text()
 match=re.search(r'mKdV/NLS article axiom audit passed for (\d+) declarations',hierarchy)
 assert match, 'Hierarchy axiom audit did not report success'
 return dict(article_public_declarations=article,below_l2_declarations=below_l2,
             hierarchy_declarations=int(match.group(1)),estimates_foundation_declarations=int(estimates_match.group(1)),
             allowed_axioms=['Classical.choice','Quot.sound','propext'])

async def main():
 for m in mathlib_pending:
  if await compile_module(m,upstream=True):return 1
 done=set(reuse);running={};failed=False;todo=set(pending);order={m:j for j,m in enumerate(selected)}
 while todo or running:
  if not failed:
   ready=sorted((m for m in todo if all(d in done for d in own_deps[m])),key=order.get)
   for m in ready[:max(0,args.jobs-len(running))]:
    todo.remove(m);running[asyncio.create_task(compile_module(m))]=m
  if not running:
   if failed:break
   raise RuntimeError('No build progress; unresolved dependency graph')
  finished,_=await asyncio.wait(running,return_when=asyncio.FIRST_COMPLETED)
  for t in finished:
   m=running.pop(t)
   if t.result():failed=True
   else:done.add(m)
 if failed:
  print('Validation stopped after compiler failure; successful outputs retained for source-fingerprint-checked resume.',flush=True)
  return 1
 assert len(done)==len(selected)
 for m in selected:
  assert digest(sources[m])==hashes[m], ('Source changed during build; resume required',m)
 axiom_audits=validate_axiom_logs()
 hints={}
 for m in selected:
  if output(m).is_symlink():continue
  data=(logs/(m+'.log')).read_text()
  assert not re.search(r'warning:|error:',data),m
  if count:=data.count('Try this:'):hints[m]=count
 save(build/'result.json',dict(informational_tactic_hints=hints,axiom_audits=axiom_audits,result='passed',modules=len(selected),compiled=len(pending),reused=len(reuse),roots=roots,source_sha256=plan['source_sha256'],warnings=0))
 print('All merged-tree compilation and requested axiom checks passed.',flush=True)
 return 0
raise SystemExit(asyncio.run(main()))
