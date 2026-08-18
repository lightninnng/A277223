#!/usr/bin/env python3
"""Static, non-elaborating audit of the local Lean project structure.

This script is intentionally not called a compiler.  It checks the local module
DAG, version pins, and forbidden placeholders so that environment failures are
separated cleanly from Lean elaboration failures.
"""
from __future__ import annotations
from pathlib import Path
import re
import sys

ROOT=Path(__file__).resolve().parents[1]
LEAN_ROOT=ROOT/'A277223'

files=[ROOT/'A277223.lean'] + sorted(LEAN_ROOT.rglob('*.lean'))
module_to_file={}
for f in files:
    rel=f.relative_to(ROOT).with_suffix('')
    module='.'.join(rel.parts)
    module_to_file[module]=f

pat=re.compile(r'^\s*import\s+([A-Za-z0-9_.]+)\s*$',re.M)
edges={m:[] for m in module_to_file}
missing=[]
for m,f in module_to_file.items():
    text=f.read_text()
    for imp in pat.findall(text):
        if imp.startswith('A277223'):
            if imp not in module_to_file:
                missing.append((m,imp))
            else:
                edges[m].append(imp)

# Cycle check.
WHITE,GRAY,BLACK=0,1,2
color={m:WHITE for m in edges}
stack=[]
cycles=[]
def dfs(u):
    color[u]=GRAY; stack.append(u)
    for v in edges[u]:
        if color[v]==WHITE: dfs(v)
        elif color[v]==GRAY:
            i=stack.index(v); cycles.append(stack[i:]+[v])
    stack.pop(); color[u]=BLACK
for u in edges:
    if color[u]==WHITE: dfs(u)

forbidden=[]
fp=re.compile(r'(^|[^A-Za-z])(sorry|admit|axiom)([^A-Za-z]|$)')
# These constructs would enlarge the trust boundary or bypass the intended
# kernel-reduction discipline.  None is needed by this project.
trust_bypass=re.compile(
    r'\b(native_decide|run_tac|unsafe|implemented_by|addDeclWithoutChecking|ofReduceBool)\b'
)
trust_bypass_hits=[]
kernel_decide_count=0
for f in files:
    for lineno,line in enumerate(f.read_text().splitlines(),1):
        # Ignore prose inside comments only for reporting?  Project source is
        # intentionally written without these tokens even in comments.
        if fp.search(line): forbidden.append((f.relative_to(ROOT),lineno,line.strip()))
        if trust_bypass.search(line):
            trust_bypass_hits.append((f.relative_to(ROOT),lineno,line.strip()))
        if 'decide +kernel' in line:
            kernel_decide_count += 1

assert (ROOT/'lean-toolchain').read_text().strip()=='leanprover/lean4:v4.32.2'
lake=(ROOT/'lakefile.toml').read_text()
assert 'rev = "v4.32.2"' in lake
assert not missing, missing
assert not cycles, cycles
assert not forbidden, forbidden
assert not trust_bypass_hits, trust_bypass_hits
assert edges['A277223']==['A277223.Main'], edges['A277223']

print(f'LEAN_MODULES={len(files)}')
print(f'LOCAL_IMPORT_EDGES={sum(map(len,edges.values()))}')
print('MISSING_LOCAL_IMPORTS=0')
print('IMPORT_CYCLES=0')
print('FORBIDDEN_PLACEHOLDERS_OR_AXIOMS=0')
print('TRUST_BYPASS_CONSTRUCTS=0')
print(f'KERNEL_DECIDE_SITES={kernel_decide_count}')
print('TOOLCHAIN_PIN=leanprover/lean4:v4.32.2')
print('MATHLIB_PIN=v4.32.2')
print('STATIC_LEAN_AUDIT_OK')
