import audit_p0_axioms as a
from pathlib import Path
import subprocess,sys
checks=0
for targets in (a.UPSTREAM,a.ADAPTER,a.CLAY,a.ROOT,a.XI):
    good='\n'.join(f"Proof.lean:10:1: info: '{n}' depends on axioms: [propext,\n Classical.choice, Quot.sound]" for n in targets)
    empty='\n'.join(f"'{n}' does not depend on any axioms" for n in targets)
    for txt in (good,empty,good.replace('\n','\r\n')):
        if set(a.audit(txt,targets))!=set(targets): raise RuntimeError('missing targets')
        checks+=1
    for txt in ('',good+'\n'+good,good.replace('Quot.sound','sorryAx'),good.replace('propext','propext, propext'),good.replace('propext',''),good.replace('info:','warning:'),good.replace(targets[0], 'wrong.target')):
        try: a.audit(txt,targets)
        except ValueError: checks+=1;continue
        raise RuntimeError('bad evidence accepted')
    if targets in (a.ROOT,a.XI):
        mode='root' if targets==a.ROOT else 'xi'
        path=mode+'-fixture.log'
        Path(path).write_text(good)
        subprocess.run([sys.executable,'audit_p0_axioms.py',mode,path],check=True)
        checks+=1
print(f'{checks}/{checks} parser fixtures PASS')
