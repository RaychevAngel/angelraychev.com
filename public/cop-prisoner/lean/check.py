#!/usr/bin/env python3
"""Sequential, source-pinned replay; only the Lean standard library is needed."""
import argparse
from datetime import datetime,timezone
import hashlib,json,os
from pathlib import Path
import shutil,subprocess,time

HERE=Path(__file__).resolve().parent
parser=argparse.ArgumentParser()
parser.add_argument('--lean',default=shutil.which('lean'))
args=parser.parse_args()
if not args.lean:
    parser.error('Lean 4.33.1 is required on PATH, or supply --lean /path/to/lean')
lean=str(Path(args.lean).resolve())
version=subprocess.check_output([lean,'--version'],text=True).strip()
if 'version 4.33.1' not in version:
    raise SystemExit(f'Wrong toolchain: {version}')
modules=['DeliveryGame','SafeBranching','CampingObstruction','TwelveVertexCertificate','DenseCounting','Audit']
env=dict(os.environ)
env['LEAN_PATH']=str(HERE)+(os.pathsep+env['LEAN_PATH'] if env.get('LEAN_PATH') else '')
records=[]
for name in modules:
    started=time.monotonic()
    result=subprocess.run([lean,'-o',str(HERE/f'{name}.olean'),str(HERE/f'{name}.lean')],
                          cwd=HERE,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    rec=dict(module=name,seconds=round(time.monotonic()-started,3),exit_code=result.returncode,
             output=result.stdout)
    records.append(rec)
    print(name,rec['seconds'],'seconds',flush=True)
    if result.returncode or 'sorryAx' in result.stdout or 'declaration uses `sorry`' in result.stdout:
        print(result.stdout)
        raise SystemExit('Formal verification failed; no successful receipt written.')
files=sorted(HERE.glob('*.lean'))+[HERE/'lean-toolchain',HERE/'check.py',HERE/'README.md',HERE/'generate_finite_certificate.py']
receipt=dict(verified_at=datetime.now(timezone.utc).isoformat(),toolchain=version,
             source_sha256={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in files},
             modules=records,all_passed=True,
             note='Kernel-checked proofs; the certificate generator and external solver are not proof assumptions.')
(HERE/'verification.json').write_text(json.dumps(receipt,indent=2)+'\n')
print('All formal modules passed. Receipt: lean/verification.json',flush=True)
