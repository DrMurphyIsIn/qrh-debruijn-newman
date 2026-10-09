#!/usr/bin/env python3
"""Cross-pin fidelity check for the QRH bridge.

Compares two lean4export NDJSON exports (format 3.x) of the same root constant taken from two
environments (here: the dbn island, Mathlib de5ce8a9 / Lean v4.34.0-rc1, and OpenAI's workspace,
Mathlib d13f23b / Lean v4.34.1).

Every expression gets a structural Merkle digest: constants are hashed BY NAME plus universe
levels; binder names, binder info and mdata are ignored (they do not change the kernel term up to
alpha-equivalence).  Per declaration we compare kind, universe parameters, type and (for defs,
opaques, inductive/ctor/recursor data) value.

MEANING CLOSURE: starting from the root, follow references through every declaration's TYPE, and
through VALUES of definitions/opaques and recursor rules, and constructor/inductive structure, but
NOT through theorem proofs (proof irrelevance: a theorem contributes only its statement).  If every
declaration of the meaning closure is identical in both exports, the root denotes the same closed
term in both environments, modulo proofs of the same propositions.

Usage: compare_exports.py A.ndjson B.ndjson ROOT_NAME [--json out.json]
"""
import sys, json, hashlib
from array import array

def H(*parts):
    h = hashlib.blake2b(digest_size=16)
    for p in parts:
        if isinstance(p, str):
            p = p.encode()
        h.update(len(p).to_bytes(4, 'little')); h.update(p)
    return h.digest()

class Export:
    def __init__(self, path):
        self.names = {0: ''}   # id -> str (0 = anonymous, implicit)
        self.levels = {0: '0'} # id -> canonical str (0 = Level.zero, implicit)
        self.edig = {}         # id -> digest (dict: ids may be sparse)
        self.econst = {}       # id -> const name (only const nodes)
        self.ekids = {}        # id -> tuple of child ids
        self.decls = {}        # name -> dict
        self.meta = None
        self.raw = {}
        with open(path) as f:
            for line in f:
                o = json.loads(line)
                self._one(o)

    def lv(self, i):
        return self.levels[i]

    def _one(self, o):
        if 'meta' in o:
            self.meta = o['meta']; return
        if 'in' in o:
            i = o['in']
            if 'str' in o:
                pre = o['str']['pre']; self.names[i] = (self.names.get(pre, '') + '.' if pre else '') + o['str']['str']
            elif 'num' in o:
                pre = o['num']['pre']; self.names[i] = (self.names.get(pre, '') + '.' if pre else '') + str(o['num']['i'])
            return
        if 'il' in o:
            i = o['il']
            if 'succ' in o: s = 'S(' + self.lv(o['succ']) + ')'
            elif 'max' in o: s = 'max(' + self.lv(o['max'][0]) + ',' + self.lv(o['max'][1]) + ')'
            elif 'imax' in o: s = 'imax(' + self.lv(o['imax'][0]) + ',' + self.lv(o['imax'][1]) + ')'
            elif 'param' in o: s = 'P' + self.names[o['param']]
            else: raise ValueError(o)
            self.levels[i] = s; return
        if 'ie' in o:
            i = o['ie']; d = self.edig; k = ()
            if 'bvar' in o: dg = H('bvar', str(o['bvar'])); self.raw[i] = ('bvar', o['bvar'])
            elif 'sort' in o: dg = H('sort', self.lv(o['sort'])); self.raw[i] = ('sort', self.lv(o['sort']))
            elif 'const' in o:
                n = self.names[o['const']['name']]; us = [self.lv(u) for u in o['const']['us']]
                dg = H('const', n, *us); self.econst[i] = n; self.raw[i] = ('const', n, us)
            elif 'app' in o:
                a, b = o['app']['fn'], o['app']['arg']; dg = H('app', d[a], d[b]); k = (a, b); self.raw[i] = ('app', a, b)
            elif 'lam' in o or 'forallE' in o:
                t = 'lam' if 'lam' in o else 'forallE'; x = o[t]
                dg = H(t, d[x['type']], d[x['body']]); k = (x['type'], x['body']); self.raw[i] = (t, x['type'], x['body'])
            elif 'letE' in o:
                x = o['letE']; dg = H('let', d[x['type']], d[x['value']], d[x['body']])
                k = (x['type'], x['value'], x['body']); self.raw[i] = ('let',) + k
            elif 'proj' in o:
                x = o['proj']; dg = H('proj', self.names[x['typeName']], str(x['idx']), d[x['struct']])
                k = (x['struct'],); self.econst[i] = self.names[x['typeName']]; self.raw[i] = ('proj', self.names[x['typeName']], x['idx'], x['struct'])
            elif 'natVal' in o: dg = H('nat', o['natVal']); self.raw[i] = ('lit', 'n' + o['natVal'])
            elif 'strVal' in o: dg = H('str', o['strVal']); self.raw[i] = ('lit', 's' + o['strVal'])
            elif 'mdata' in o: dg = d[o['mdata']['expr']]; k = (o['mdata']['expr'],); self.raw[i] = ('mdata', o['mdata']['expr'])
            else: raise ValueError(o)
            d[i] = dg
            if k: self.ekids[i] = k
            return
        # declarations
        N = self.names; E = self.edig
        def lps(x): return [N[p] for p in x.get('levelParams', [])]
        if 'axiom' in o:
            x = o['axiom']; self._decl(N[x['name']], 'axiom', lps(x), x['type'], None, [])
        elif 'def' in o:
            x = o['def']; self._decl(N[x['name']], 'def', lps(x), x['type'], x['value'], [],
                                     extra=json.dumps([x['safety']]))
        elif 'opaque' in o:
            x = o['opaque']; self._decl(N[x['name']], 'opaque', lps(x), x['type'], x['value'], [])
        elif 'thm' in o:
            x = o['thm']; self._decl(N[x['name']], 'thm', lps(x), x['type'], x['value'], [], proof=True)
        elif 'quot' in o:
            x = o['quot']; self._decl(N[x['name']], 'quot', lps(x), x['type'], None, [], extra=x['kind'])
        elif 'inductive' in o:
            x = o['inductive']
            for t in x['types']:
                self._decl(N[t['name']], 'inductive', lps(t), t['type'], None,
                           [N[c] for c in t['ctors']] + [N[a] for a in t['all']],
                           extra=json.dumps([t['numParams'], t['numIndices'], [N[c] for c in t['ctors']],
                                             [N[a] for a in t['all']], t['numNested'], t['isRec'],
                                             t['isReflexive'], t['isUnsafe']]))
            for c in x['ctors']:
                self._decl(N[c['name']], 'ctor', lps(c), c['type'], None, [N[c['induct']]],
                           extra=json.dumps([N[c['induct']], c['cidx'], c['numParams'], c['numFields'], c['isUnsafe']]))
            for r in x['recs']:
                rules = [(N[q['ctor']], q['nfields'], q['rhs']) for q in r['rules']]
                self._decl(N[r['name']], 'rec', lps(r), r['type'], None,
                           [N[a] for a in r['all']] + [q[0] for q in rules],
                           extra=json.dumps([[N[a] for a in r['all']], r['numParams'], r['numIndices'],
                                             r['numMotives'], r['numMinors'], r['k'], r['isUnsafe'],
                                             [(q[0], q[1], E[q[2]].hex()) for q in rules]]),
                           more_exprs=[q[2] for q in rules])
        else:
            raise ValueError(list(o)[:3])

    def _decl(self, name, kind, lp, ty, val, refs, extra='', proof=False, more_exprs=()):
        self.decls[name] = dict(kind=kind, lp=lp, ty=ty, val=val, refs=refs, extra=extra,
                                proof=proof, more=list(more_exprs),
                                tyd=self.edig[ty].hex(), vald=(self.edig[val].hex() if val is not None else None))

    def consts_of(self, roots):
        out = set(); seen = set(); stack = list(roots)
        while stack:
            e = stack.pop()
            if e in seen: continue
            seen.add(e)
            c = self.econst.get(e)
            if c is not None: out.add(c)
            stack.extend(self.ekids.get(e, ()))
        return out

    def meaning_closure(self, root):
        todo = [root]; done = set(); missing = set()
        while todo:
            n = todo.pop()
            if n in done: continue
            done.add(n)
            dcl = self.decls.get(n)
            if dcl is None:
                missing.add(n); continue
            ex = [dcl['ty']] + dcl['more']
            if dcl['val'] is not None and not dcl['proof']:
                ex.append(dcl['val'])
            todo.extend(self.consts_of(ex)); todo.extend(dcl['refs'])
        return done, missing


import re as _re
_AUX = _re.compile(r"(_@|\._hyg|\._proof_\d+|\.match_\d+|\._aux|\.proof_\d+|_private\.)")

def is_aux(name):
    return bool(_AUX.search(name))

class Normalizer:
    """Normalized constant digests ND(c), invariant under (i) renaming universe parameters,
    (ii) renaming auxiliary/hygienic constants (compared by content), (iii) replacing a
    referenced theorem by any theorem with the same statement (proof irrelevance)."""
    def __init__(self, ex):
        self.ex = ex; self.memo = {}; self.inprog = set()
        self.lraw = {}   # level id -> raw object kept for renaming
    def lvl(self, s, ren):
        for k, v in ren.items():
            s = s.replace('P' + k + ')', 'Q' + str(v) + ')').replace('P' + k + ',', 'Q' + str(v) + ',')
            if s == 'P' + k: s = 'Q' + str(v)
        return s
    def ref(self, n):
        d = self.ex.decls.get(n)
        if d is None: return 'name:' + n
        if d['kind'] == 'thm': return 'thm:' + self.nd(n, type_only=True)
        if is_aux(n): return 'aux:' + self.nd(n)
        return 'name:' + n
    def expr(self, e, ren, cache):
        if e in cache: return cache[e]
        X = self.ex; o = X.raw[e]
        t = o[0]
        if t == 'bvar': r = H('bvar', str(o[1]))
        elif t == 'sort': r = H('sort', self.lvl(o[1], ren))
        elif t == 'const': r = H('const', self.ref(o[1]), *[self.lvl(u, ren) for u in o[2]])
        elif t == 'app': r = H('app', self.expr(o[1], ren, cache), self.expr(o[2], ren, cache))
        elif t in ('lam', 'forallE'): r = H(t, self.expr(o[1], ren, cache), self.expr(o[2], ren, cache))
        elif t == 'let': r = H('let', *[self.expr(x, ren, cache) for x in o[1:]])
        elif t == 'proj': r = H('proj', self.ref(o[1]), str(o[2]), self.expr(o[3], ren, cache))
        elif t == 'lit': r = H('lit', o[1])
        elif t == 'mdata': r = self.expr(o[1], ren, cache)
        cache[e] = r; return r
    def nd(self, n, type_only=False):
        key = (n, type_only)
        if key in self.memo: return self.memo[key]
        if key in self.inprog: return H('cycle').hex()
        self.inprog.add(key)
        d = self.ex.decls[n]; ren = {p: i for i, p in enumerate(d['lp'])}; cache = {}
        parts = [d['kind'], str(len(d['lp'])), self.expr(d['ty'], ren, cache)]
        if not type_only and d['kind'] != 'thm':
            if d['val'] is not None: parts.append(self.expr(d['val'], ren, cache))
            for m in d['more']: parts.append(self.expr(m, ren, cache))
            ex = d['extra']
            for r in d['refs']:
                ex = ex.replace('"' + r + '"', '"' + (self.ref(r) if is_aux(r) else r) + '"')
            parts.append(ex)
        out = H(*parts).hex()
        self.inprog.discard(key); self.memo[key] = out
        return out

def main():
    a_path, b_path, root = sys.argv[1:4]
    out_json = sys.argv[sys.argv.index('--json') + 1] if '--json' in sys.argv else None
    A = Export(a_path); B = Export(b_path)
    ca, ma = A.meaning_closure(root); cb, mb = B.meaning_closure(root)
    def sig(d): return (d['kind'], d['lp'], d['tyd'], None if d['proof'] else d['vald'], d['extra'])
    only_a = sorted(ca - cb); only_b = sorted(cb - ca)
    differ = []
    for n in sorted(ca & cb):
        da, db = A.decls.get(n), B.decls.get(n)
        if da is None or db is None: continue
        if sig(da) != sig(db):
            what = [k for k, x, y in zip(('kind', 'levelParams', 'type', 'value', 'structure'), sig(da), sig(db)) if x != y]
            differ.append((n, da['kind'], what))
    NA, NB = Normalizer(A), Normalizer(B)
    sys.setrecursionlimit(1000000)
    root_nd = (NA.nd(root), NB.nd(root))
    alt_root = sys.argv[sys.argv.index('--also') + 1] if '--also' in sys.argv else None
    # normalized closure comparison over NON-aux names present in either closure
    def named(c, X): return {n for n in c if n in X.decls and not is_aux(n) and X.decls[n]['kind'] != 'thm'}
    nA, nB = named(ca, A), named(cb, B)
    norm_only_a = sorted(nA - set(B.decls)); norm_only_b = sorted(nB - set(A.decls))
    norm_differ = sorted(n for n in nA & nB if NA.nd(n) != NB.nd(n))
    thm_stmt_differ = sorted(n for n in ca & cb if n in A.decls and n in B.decls and A.decls[n]['kind'] == 'thm'
                             and not is_aux(n) and NA.nd(n, True) != NB.nd(n, True))
    # root causes: differing named defs whose referenced named non-aux defs all agree
    def direct_refs(X, n):
        d = X.decls[n]; ex = [d['ty']] + d['more'] + ([d['val']] if d['val'] is not None and not d['proof'] else [])
        return X.consts_of(ex) | set(d['refs'])
    dset = set(norm_differ)
    causes = [n for n in norm_differ if not (direct_refs(A, n) & dset - {n})]
    # informational: theorem proofs that differ inside the closure (irrelevant to meaning)
    proof_diff = sum(1 for n in ca & cb if A.decls.get(n) and B.decls.get(n) and A.decls[n]['proof']
                     and A.decls[n]['vald'] != B.decls[n]['vald'])
    kinds = {}
    for n in ca:
        if n in A.decls: kinds[A.decls[n]['kind']] = kinds.get(A.decls[n]['kind'], 0) + 1
    rep = dict(root=root, A=dict(file=a_path, meta=A.meta, exported=len(A.decls), closure=len(ca), missing=sorted(ma)),
               B=dict(file=b_path, meta=B.meta, exported=len(B.decls), closure=len(cb), missing=sorted(mb)),
               closure_kinds_A=kinds, only_in_A=only_a, only_in_B=only_b, differing=differ,
               theorem_proofs_differing_informational=proof_diff,
               identical=(not only_a and not only_b and not differ and not ma and not mb),
               normalized=dict(root_digest_A=root_nd[0], root_digest_B=root_nd[1],
                               root_equal=root_nd[0] == root_nd[1],
                               alt_root=(alt_root, NA.nd(alt_root) if alt_root else None, NB.nd(alt_root) if alt_root else None),
                               root_vs_alt_A=(NA.nd(root) == NA.nd(alt_root)) if alt_root else None,
                               root_vs_alt_B=(NB.nd(root) == NB.nd(alt_root)) if alt_root else None,
                               named_defs_A=len(nA), named_defs_B=len(nB),
                               named_only_in_A=norm_only_a, named_only_in_B=norm_only_b,
                               named_differing=norm_differ, root_causes=causes,
                               theorem_statements_differing=thm_stmt_differ))
    print(json.dumps({k: (v if not isinstance(v, list) or len(v) < 60 else v[:60] + ['...%d more' % (len(v) - 60)])
                      for k, v in rep.items()}, indent=1))
    if out_json:
        json.dump(rep, open(out_json, 'w'), indent=1)

if __name__ == '__main__':
    main()
