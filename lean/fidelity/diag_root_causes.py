import sys, json
import os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from compare_exports import Export, Normalizer, is_aux
sys.setrecursionlimit(1000000)
A = Export('export_dbn.ndjson'); B = Export('export_oai.ndjson')
NA, NB = Normalizer(A), Normalizer(B)
def show(X, e, depth=0, lim=[0]):
    # compact printer
    o = X.raw[e]; t = o[0]
    if t == 'const': return o[1] + ('.{%s}' % ','.join(o[2]) if o[2] else '')
    if t == 'bvar': return '#%d' % o[1]
    if t == 'sort': return 'Sort ' + o[1]
    if t == 'app': return '(' + show(X, o[1]) + ' ' + show(X, o[2]) + ')'
    if t in ('lam', 'forallE'): return ('fun' if t == 'lam' else 'Pi') + ' ' + show(X, o[1]) + ', ' + show(X, o[2])
    if t == 'proj': return show(X, o[3]) + '.' + o[1] + '#' + str(o[2])
    if t == 'lit': return o[1]
    if t == 'let': return 'let ' + ' ; '.join(show(X, x) for x in o[1:])
    return t
for root in ['QRHFidelity.stmt', 'QRHFidelity.stmtMathlib']:
    for X in (A,):
        d = X.decls[root]; print(root, show(X, d['val'])[:1500]); print()
causes = json.load(open('fidelity_stmt.json'))['normalized']['root_causes']
for n in causes:
    da, db = A.decls[n], B.decls[n]
    ta, tb = NA.expr(da['ty'], {p: i for i, p in enumerate(da['lp'])}, {}), NB.expr(db['ty'], {p: i for i, p in enumerate(db['lp'])}, {})
    va = NA.expr(da['val'], {p: i for i, p in enumerate(da['lp'])}, {}) if da['val'] is not None else None
    vb = NB.expr(db['val'], {p: i for i, p in enumerate(db['lp'])}, {}) if db['val'] is not None else None
    print('==', n, da['kind'], 'type', 'same' if ta == tb else 'DIFF', 'value', 'same' if va == vb else 'DIFF', 'extra', 'same' if da['extra'] == db['extra'] else 'DIFF')
    if ta != tb:
        print('  A ty:', show(A, da['ty'])[:600]); print('  B ty:', show(B, db['ty'])[:600])
    elif va != vb:
        print('  A val:', show(A, da['val'])[:700]); print('  B val:', show(B, db['val'])[:700])
    elif da['extra'] != db['extra']:
        print('  A:', da['extra'][:500]); print('  B:', db['extra'][:500])
