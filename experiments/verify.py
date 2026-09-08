"""Build and replay the pinned proof; reject corrupt production certificates."""
from pathlib import Path
import subprocess, json, hashlib, time
root=Path(__file__).resolve().parents[1]
modules=['PinwheelWords','PinwheelCover','PinwheelPeriodic','PinwheelTable','PinwheelTables','PinwheelBalanced','PinwheelGroups','PinwheelFour','PinwheelSchedule','PinwheelPeriods']
def run(args):
    p=subprocess.run(args,cwd=root,text=True,capture_output=True)
    return {'command':args,'exit_code':p.returncode,'stdout':p.stdout,'stderr':p.stderr}
start=time.monotonic()
build=run(['lake','build'])
assert build['exit_code']==0,build
checks=[]
for name in modules:
    result=run(['lake','env','leanchecker','CertifiedDiscovery.'+name])
    assert result['exit_code']==0,result
    checks.append(result)
    print('Kernel replay accepted',name,flush=True)
fresh=run(['lake','env','leanchecker','--fresh','CertifiedDiscovery.PinwheelPeriods'])
assert fresh['exit_code']==0,fresh
controls=[]
for src in sorted((root/'tests').glob('Reject*.lean')):
    result=run(['lake','env','lean',str(src.relative_to(root))])
    assert result['exit_code']!=0 and 'Tactic `decide` proved' in result['stdout'],result
    controls.append(result)
assert len(controls)==3
report={'verified':True,'build':build,'module_replays':checks,'fresh_replay':fresh,'negative_controls':controls,'seconds':time.monotonic()-start,'source_sha256':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in (root/'CertifiedDiscovery').glob('*.lean')}}
(root/'results/standalone-verification.json').write_text(json.dumps(report,indent=2))
print('All proof and rejection checks passed.',flush=True)
