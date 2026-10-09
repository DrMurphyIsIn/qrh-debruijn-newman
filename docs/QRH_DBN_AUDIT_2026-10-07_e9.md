# Independent audit of PR #662: Lambda <= 9/32 from OpenAI's quasi-Riemann hypothesis

Date: 2026-10-07. Auditor: Claude Code session `peterwmurphy-e9` (Remote Control), a different
session from the author (`session_013hB6k9ssUSET4joVJgNy51`, "Riemann"). Git identity is the
SAME account on both sides (Dr. Murphy), so the `mission audit` tool's identity test would
refuse this read-back; see "Independence" below. conjecture1_proved = False.

Audited commit: `d6d581ff5` on `rh/qrh-dbn-9-32` (three commits over `790d67dec`), read from a
fresh worktree `~/arda-e9-audit` (branch `audit/qrh-9-32-e9`) created from `origin` after the
push. No file under the author's directories (`~/arda-qrh`, `~/oai-*`) was modified; reads
from them are listed under "Caches reused".

## Verdict

Every claim in `telperion/docs/QRH_DBN_BRIDGE_2026-10-07.md` that this audit could test was
reproduced. The theorem

```lean
theorem dbn_real_zeros_of_qrh_unconditional :
    ∀ t : ℝ, 9 / 32 ≤ t → ∀ z : ℂ, DBN.H t z = 0 → z.im = 0
```

compiles in one environment (Lean v4.34.1, Mathlib d13f23b, inside openai/math adc7f124) with
axioms `[propext, Classical.choice, Quot.sound]`, and Comparator (nanoda ON, my own fresh Comparator/nanoda builds) accepts it against a Mathlib-only challenge while rejecting a tampered challenge, exactly as the author reported.

It is not RH, and it is weaker than the numerical bounds (0.22, 0.2). Nothing is registered or
granted; the bridge island has no CI job, so the grant gate refuses its artifacts.

## What was checked, and how

### A. Statements (read before any build)

| Claim | Check | Result |
|---|---|---|
| Hypothesis of `dbn_real_zeros_of_qrh` is OpenAI's theorem with `{s}` closed | `lean/OAI/NumberTheory/DirichletL/Nonvanishing.lean` fetched from GitHub at adc7f124 (not from any local copy): `{s : ℂ} (hs : (7 / 8 : ℝ) < s.re) : riemannZeta s ≠ 0` | matches |
| OpenAI's pins | `lean-toolchain` = v4.34.1, `lake-manifest.json` mathlib rev d13f23b…, `lean/LICENSE` = Apache-2.0, all fetched from GitHub | match `OAI_PIN` |
| OpenAI's own Comparator challenge for QRH imports only Mathlib and states the same theorem | `lean/ComparatorChallenges/QuasiRiemannHypothesis.lean` from GitHub | yes |
| `DBN.H` in the challenge is DBNDefs' `H` | `diff` of the transcribed `thetaMoment`, `Φ`, `HIntegrand`, `H` against `DBNDefs.lean` lines 38-41, 207-214, 405-413 | identical up to doc-comments; same `open` line and namespace |
| Registry mirror of `DBN.H` (`missions/rh/lean/Statements/RHDefs.lean`) matches | text comparison | identical |
| `Φ` and `H_t` are the Polymath15 / Rodgers-Tao objects, `H_0 = ξ(1/2+iz/2)/8` | by inspection; `dbn_H0_eq_xi` is kernel-checked on the island | yes |
| "every zero of `H_t` is real for all `t ≥ 9/32`" is the sInf-free form of Λ ≤ 9/32 | by definition of Λ | yes |
| Arithmetic: θ = 7/8 gives strip `|Im z| ≤ 2θ−1 = 3/4`, de Bruijn time `(3/4)²/2 = 9/32` | hand check against `m1_H_real_zeros_of_im_sq_le` (`hY : Y ≤ 2 (t − t0)`, `Y = (2θ−1)²`, `t0 = 0`) | correct |
| Lemmas used by `DBNZeroFreeHalfplane` exist with the stated signatures | `m1_H_real_zeros_of_im_sq_le`, `H_zero_eq_zero_iff_of_H0_eq_xi`, `riemannXi_eq_zero_iff_strip_zero`, `xiArg_re`, `H_neg`, `dbn_H0_eq_xi`, `dbn_debruijn_parametric` grepped on the island | all present |

### B. Sources

| Claim | Check | Result |
|---|---|---|
| No `sorry`/`axiom` in the new Lean files other than the two challenge bodies | grep | confirmed |
| 19-module closure | import closure of `DBNZeroFreeHalfplane` recomputed from the island sources | exactly the 19 listed; external imports `Lc.LiCriterion.Basic`, `Mathlib` |
| 17 of 19 ported modules byte-identical, 2 differ only by the recorded one-line patches | `cmp`/`diff` of `work/oai/*.lean` against `dbn/lean/*.lean` after materialize | confirmed; the two diffs are exactly patches 0001 and 0002 |
| `Lc/XiZeros.lean` unmodified from LiCriterion @ 35df682f | diff against GitHub at that commit | identical |
| `Lc/LiCriterion/Basic.lean` = three verbatim declarations (upstream lines 100-101, 1236-1237, 1559-1564) | sed of the upstream file from GitHub | verbatim; upstream has no `axiom` declarations; upstream LICENSE is Apache-2.0 |
| OpenAI's tree in the materialized workspace is unmodified | `diff -rq` against `~/oai-math` at adc7f124 (the pinned checkout) | only `lakefile.lean` differs, by the appended stanza; 30 files only-in-work are the Arda additions |
| No private material or secrets in the three commits | grep over the full diff | none found; no binaries |

### C. Builds (all through `ARDA_LEAN_SLOTS=1 ~/hodge-engine/leanlock.sh`)

| Build | Result |
|---|---|
| `materialize.sh --from-local ~/oai-replay` into my worktree | 84 s |
| `lake build ArdaQRHBridge AxiomGuardQRHBridge ArdaDBNUnconditional ArdaDBNChallenge ArdaDBNNegativeControl` | green, 11,900 jobs, 0 errors, 0 `sorryAx`. The 27 Arda modules (19 DBN, 2 Lc, bridge, unconditional, 2 guards, 2 challenges) were COMPILED here, not replayed. The 25 warnings are Lake's "repository has local changes" for OpenAI's own dependency patches. |
| Axioms (from the build, `AxiomGuardQRHBridge` + `AxiomGuardDBNUnconditional`) | all 10 guarded theorems `[propext, Classical.choice, Quot.sound]`, including `dbn_real_zeros_of_qrh_unconditional`, `qrh_seven_eighths`, `OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re` |
| dbn island (v4.34.0-rc1): `lake build` + `lake env lean AxiomGuardDBN.lean` | green, 8,809 jobs; guard 654 lines, 0 `sorryAx`, 5 new theorems standard axioms. Then `DBNZeroFreeHalfplane` and `AxiomGuardDBN` were deleted from the reflinked cache and rebuilt from source (`Built DBNZeroFreeHalfplane (36s)`, `Built AxiomGuardDBN`, 8,765 jobs, exit 0), so the new module's olean here is mine, not the author's. |

### D. Comparator (independent judge), nanoda ON

All three runs were done in my materialized workspace with the Comparator and nanoda binaries
described under "Caches reused", `COMPARATOR_LANDRUN` pointing at the pass-through shim (macOS,
NOT sandboxed), one at a time under the lock. Swap stayed at about 0.8 GB throughout.

| Config | Challenge / solution | Output | Wall | Peak RSS |
|---|---|---|---|---|
| `dbn_real_zeros_of_qrh_unconditional.comparator.json` | `ArdaDBNChallenge` (imports only Mathlib) / `ArdaDBNUnconditional` | `nanoda kernel accepts the solution`, `Lean default kernel accepts the solution`, `Your solution is okay!` | 760 s | 9.1 GB |
| `tampered.comparator.json` (negative control, `e^{9u}` -> `e^{8u}` in `Φ`) | `ArdaDBNChallengeTampered` / `ArdaDBNUnconditional` | `uncaught exception: Const does not match between challenge and target 'DBN.Φ'` (rejected) | 257 s | 9.1 GB |
| `qrh_seven_eighths.comparator.json` (self-check, as the missions judge does) | `ArdaQRHBridge` / `ArdaQRHBridge` | `nanoda kernel accepts the solution`, `Lean default kernel accepts the solution`, `Your solution is okay!` | 758 s | 9.4 GB |

The exported constant set printed by Comparator for the unconditional run names exactly
`dbn_real_zeros_of_qrh_unconditional` plus the three permitted axioms and Lean's primitive
constants. Process exit codes were not captured by my wrapper (shell quirk); the verdict lines
above are the evidence, and they match the author's `logs/comparator_2026-10-07.txt` line for line.

## Caches reused (disclosed per the author's request)

- `~/oai-replay/.lake` (OpenAI closure + Mathlib oleans at d13f23b), via `materialize.sh --from-local` (APFS reflink, read-only). None of the Arda modules existed there; all 27 were compiled fresh.
- `~/arda-qrh/telperion/examples/dbn/lean/.lake` (dbn island oleans), reflinked read-only; the new module and guard were deleted from the copy and recompiled from source (see C).
- `~/oai-math` was read only for `materialize.sh`'s pin check and one `diff -rq`.
- Comparator and nanoda were NOT borrowed: `~/e9-tools/comparator` is a fresh clone of leanprover/comparator at tag v4.34.0 with `lean-toolchain` set to v4.34.1 (there is no v4.34.1 tag; this mirrors the author's setup, which I inspected read-only), lean4export at manifest rev 076e8e5; `~/e9-tools/nanoda` is a fresh clone of ammkrn/nanoda_lib built with cargo. landrun is a pass-through shim copied from `missions-comparator.yml` (macOS; not sandboxed).

## Independence

- Different session: yes (`peterwmurphy-e9` vs `session_013hB6k9ssUSET4joVJgNy51`).
- Different git identity: NO. Both sessions commit as the same account. `telperion mission audit` compares `git_identity` as well as session id and would refuse. Under `MISSIONS_DESIGN_2026-09-11.md` §8 and `AUDIT_INDEPENDENCE_2026-09-23.md`, independence can instead come from a recorded `missions-comparator` CI run. That requires (a) registering the nodes (author side, not done) and (b) a CI job covering `oai_qrh_bridge` (not active). So this document is testimony from a different session under the same account, plus a local Comparator replay; it is not a registry grant and does not claim to be.
- Read-backs below were written AFTER reading the artifacts (I reviewed the sources before writing them), which departs from the "written before reading" protocol in doc §5. They are offered as material for the registry, not as protocol-compliant read-backs.

## Prepared read-backs (>= 120 chars each, formal statement rendered in my own words)

- `RH_dbn_real_zeros_of_zeta_halfplane`: For every real theta, if riemannZeta s is nonzero whenever theta < Re s, then for every real t with 2 (theta - 1/2)^2 <= t and every complex z with DBN.H t z = 0, the imaginary part of z is zero. Conditional on the half-plane; not RH.
- `RH_dbn_real_zeros_of_qrh`: If riemannZeta s is nonzero for every complex s with 7/8 < Re s, then for every real t >= 9/32 and every complex z with DBN.H t z = 0, Im z = 0. The hypothesis is OpenAI's QRH theorem with its implicit binder closed; conditional; not RH.
- `RH_zeta_zero_free_seven_eighths`: For every complex s with 7/8 < Re s, riemannZeta s is nonzero. Proof entirely OpenAI's (openai/math adc7f124, Apache-2.0), re-exported inside OpenAI's own workspace at Lean v4.34.1 / Mathlib d13f23b; the dbn island is on a different Mathlib pin (de5ce8a9) and `riemannZeta` is not the same closed term across the pins (267 differing definitions), so pairing the rc1 dbn artifact with this one is a mathematical identification, not a kernel check.
- `RH_dbn_real_zeros_nine_thirtyseconds`: For every real t >= 9/32 and every complex z, if DBN.H t z = 0 then Im z = 0, where DBN.H t z is the integral over u > 0 of exp(t u^2) Phi(u) cos(z u) and Phi is the Polymath15 series. Unconditional, one environment (OpenAI's pin), no cross-pin step. Classically Lambda <= 9/32. Not RH.

## Notes for the author (non-blocking)

1. Doc §7 says "Nothing has been pushed"; stale as of PR #662.
2. The CI draft builds `ArdaDBNUnconditional ArdaDBNChallenge` but not `ArdaDBNNegativeControl`; if the negative control is meant to be part of the judge, add it and a `comparator` step that asserts EXIT 1 on `tampered.comparator.json`.
3. `git_identity` is shared across all local sessions on this machine, so no local session can satisfy the identity half of `mission audit`; the Comparator-record path is the only one open until a second principal exists.

conjecture1_proved = False.
