#!/usr/bin/env python3
"""Build the `Collatz` library one module (one Lean process) at a time, in dependency order.

`lake build Collatz` compiles in parallel, which on a small machine can exhaust memory because some generated
modules are large. This script walks the `import Collatz.*` graph from Collatz.lean, orders it topologically and
calls `lake build <module>` for each module in turn. Each call only has already-built dependencies, so exactly
one Lean process runs at a time. Re-running skips nothing by itself, but lake itself skips up-to-date modules.

usage: python scripts/build_serial.py [--list]      (run from the repository root)
"""
import re, subprocess, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


def imports(mod):
    p = ROOT / (mod.replace('.', '/') + '.lean')
    return [m for m in re.findall(r'^import\s+(Collatz(?:\.\w+)*)\s*$', p.read_text(encoding='utf8'), re.M)]


def order(root='Collatz'):
    seen, out = set(), []
    stack = [(root, iter(imports(root)))]
    seen.add(root)
    while stack:  # iterative DFS post-order (the import graph is deep)
        mod, it = stack[-1]
        for dep in it:
            if dep not in seen:
                seen.add(dep)
                stack.append((dep, iter(imports(dep))))
                break
        else:
            out.append(mod)
            stack.pop()
    return out


if __name__ == '__main__':
    mods = order()
    if '--list' in sys.argv:
        print('\n'.join(mods))
        print(f'# {len(mods)} modules', file=sys.stderr)
        sys.exit(0)
    for i, m in enumerate(mods, 1):
        print(f'[{i}/{len(mods)}] lake build {m}', flush=True)
        if subprocess.call(['lake', 'build', m], cwd=ROOT) != 0:
            sys.exit(f'FAILED: {m}')
