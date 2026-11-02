from pathlib import Path
import os, subprocess, sys
root=Path(__file__).resolve().parent.parent
repo=Path('/home/janbernloehr/Documents/Codex/2026-09-11/test-01-5-2-test-02/outputs/dnls')
lean=Path('/home/janbernloehr/Documents/Codex/2026-09-11/test-01-5-2-test-02/work/tooling/elan/toolchains/leanprover--lean4---v4.33.1/bin/lean')
# Lean selects one root per module prefix. Make a private read-only import view.
view=root/'.lake/article-check/lib/lean'
(view/'NLS/Articles/KdVPseudomeasures').mkdir(parents=True,exist_ok=True)
(root/'.lake/article-check/logs').mkdir(parents=True,exist_ok=True)
for child in (repo/'.lake/build/lib/lean/NLS').iterdir():
    target=view/'NLS'/child.name
    if not target.exists(): target.symlink_to(child, target_is_directory=child.is_dir())
paths=[view]+list((repo/'.lake/packages').glob('*/.lake/build/lib/lean'))
elan=repo.parent.parent/'work/tooling/elan'
env=dict(os.environ, LEAN_PATH=':'.join(map(str,paths)), ELAN_HOME=str(elan),
    PATH=str(elan/'bin')+os.pathsep+os.environ.get('PATH',''),
    MATHLIB_CACHE_DIR=str(repo.parent.parent/'work/cache/mathlib'))
modules=sys.argv[1:] or ['WeakStarEndpoint','WeightedWeakStarEndpoint','PeriodicWeakStarEndpoint','AppendixBWeakStar','AppendixBLowerTopology','Audit']
for module in modules:
    source=root/'NLS/Articles/KdVPseudomeasures'/f'{module}.lean'
    output=view/'NLS/Articles/KdVPseudomeasures'/f'{module}.olean'
    p=subprocess.run([str(lean),'-DautoImplicit=false','-R',str(root),'-o',str(output),str(source)],env=env,capture_output=True,text=True)
    (root/'.lake/article-check/logs'/f'check-{module}.log').write_text(p.stdout+p.stderr)
    print(module, 'exit:',p.returncode)
    print(p.stdout+p.stderr,end='')
    if p.returncode: sys.exit(p.returncode)
    if module == 'Audit':
        import re
        reports=re.findall(r"'([^']+)' depends on axioms: \[(.*?)\]",p.stdout,re.S)
        expected=re.findall(r'^#print axioms (\S+)',source.read_text(),re.M)
        assert {d for d,_ in reports}==set(expected), reports
        allowed={'propext','Classical.choice','Quot.sound'}
        for declaration, axioms in reports:
            assert {a.strip() for a in axioms.split(',')} <= allowed, (declaration,axioms)
print('All requested private checks passed.')
