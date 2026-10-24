#!/usr/bin/env python3
"""Sequential, source-pinned kernel replay of every distributed Lean module."""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import time

HERE = Path(__file__).resolve().parent
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def without_comments(source):
    """Strip Lean's nested block comments and line comments for source checks."""
    out = []
    i = depth = 0
    while i < len(source):
        if source.startswith('/-', i):
            depth += 1
            i += 2
        elif depth and source.startswith('-/', i):
            depth -= 1
            i += 2
        elif depth:
            if source[i] == '\n':
                out.append('\n')
            i += 1
        elif source.startswith('--', i):
            end = source.find('\n', i)
            i = len(source) if end < 0 else end
        else:
            out.append(source[i])
            i += 1
    if depth:
        raise RuntimeError('Unterminated Lean comment')
    return ''.join(out)

def build_order(sources):
    local = {p.stem: p for p in sources}
    seen, active, ordered, external = set(), set(), [], set()
    def visit(name):
        if name in seen:
            return
        if name not in local:
            external.add(name)
            return
        if name in active:
            raise RuntimeError('Cyclic local import: ' + name)
        active.add(name)
        text = without_comments(local[name].read_text())
        if re.search(r'\b(?:sorry|admit|axiom|native_decide)\b', text):
            raise RuntimeError('Forbidden proof escape in ' + name)
        for line in text.splitlines():
            if line.startswith('import '):
                for dependency in line[7:].split():
                    visit(dependency)
        active.remove(name)
        seen.add(name)
        ordered.append(name)
    for name in sorted(local):
        if name != 'Audit':
            visit(name)
    if 'Audit' in local:
        visit('Audit')
    return ordered, sorted(external)

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lean', default=shutil.which('lean'))
    parser.add_argument('--timeout', type=int, default=900,
                        help='Maximum seconds per module; default 900.')
    args = parser.parse_args()
    if not args.lean:
        parser.error('Lean 4.33.1 is required on PATH, or supply --lean /path/to/lean')
    lean = str(Path(args.lean).resolve())
    version = subprocess.check_output([lean, '--version'], text=True).strip()
    if not re.search(r'\bversion 4\.33\.1\b', version):
        raise SystemExit('Wrong toolchain: ' + version)
    sources = sorted(HERE.glob('*.lean'))
    files = sources + sorted(HERE.glob('*.py')) + [HERE/'lean-toolchain', HERE/'README.md']
    pins = {p.name: sha(p) for p in files}
    modules, external = build_order(sources)
    if any(name != 'Std' and not name.startswith(('Std.', 'Init.')) for name in external):
        raise SystemExit('Unexpected external proof import: ' + repr(external))
    compiler_sha = sha(Path(lean))
    env = dict(os.environ, LEAN_PATH=str(HERE))
    records = []
    for name in modules:
        started = time.monotonic()
        result = subprocess.run([lean, '-j', '2', '-o', str(HERE/f'{name}.olean'),
                                 str(HERE/f'{name}.lean')], cwd=HERE, env=env,
                                text=True, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT, timeout=args.timeout)
        reported = set()
        for block in re.findall(r'depends on axioms:\s*\[([^]]*)\]', result.stdout):
            reported.update(x.strip() for x in block.split(',') if x.strip())
        record = dict(module=name, seconds=round(time.monotonic()-started, 3),
                      exit_code=result.returncode, output=result.stdout,
                      axioms=sorted(reported))
        records.append(record)
        print(name, record['seconds'], 'seconds', flush=True)
        if (result.returncode or not reported <= ALLOWED_AXIOMS or
                'sorryAx' in result.stdout or 'declaration uses `sorry`' in result.stdout):
            print(result.stdout)
            raise SystemExit('Formal verification failed; no successful receipt written.')
    current_files = sorted(HERE.glob('*.lean')) + sorted(HERE.glob('*.py')) + [HERE/'lean-toolchain', HERE/'README.md']
    if files != current_files or pins != {p.name: sha(p) for p in current_files}:
        raise SystemExit('Sources changed during replay; no successful receipt written.')
    if compiler_sha != sha(Path(lean)):
        raise SystemExit('Compiler changed during replay.')
    receipt = dict(verified_at=datetime.now(timezone.utc).isoformat(), toolchain=version,
                   compiler_sha256=compiler_sha, external_imports=external,
                   source_sha256=pins, modules=records, all_passed=True,
                   note='Every distributed module rebuilt sequentially with two workers. '
                        'Kernel-checked proofs; producers and external solvers are not assumptions. '
                        'Formal coverage is stated in README.md; no full-classification claim follows from the module count.')
    tmp = HERE/'verification.json.tmp'
    tmp.write_text(json.dumps(receipt, indent=2)+'\n')
    tmp.replace(HERE/'verification.json')
    print('All formal modules passed. Receipt: lean/verification.json', flush=True)

if __name__ == '__main__':
    main()
