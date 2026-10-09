# Λ ≤ 9/32 from OpenAI's quasi-Riemann hypothesis: the dbn corollary, the bridge, and the cross-pin seam

Date: 2026-10-07. Branch `rh/qrh-dbn-9-32`, worktree `~/arda-qrh`, local commits only. The authoring
session did not run `mission add`, `mission audit` or `mission grant`, and changed no registry file.
conjecture1_proved = False.

## The short version

OpenAI's `openai/math` release of 2026-10-06 proves in Lean that ζ(s) ≠ 0 for Re s > 7/8.
Earlier today we replayed that proof through Comparator with nanoda switched on, and both kernels
accepted it. Combined with de Bruijn's heat-flow theorem, which the dbn island already proves in
parametric form, it says that every zero of H_t is real once t ≥ 9/32. Classically that is
Λ ≤ 9/32 = 0.28125. That is weaker than the numerical bounds (Polymath15 0.22, Platt-Trudgian 0.2).
As far as we know it would be the first machine-checked bound below de Bruijn's 1/2.

Three pieces now exist.

1. **The corollary, on the dbn island, conditional.** If ζ has no zero in Re s > θ, then every zero
   of H_t is real for every t ≥ 2(θ − 1/2)². At θ = 7/8 the hypothesis is written exactly as
   OpenAI's theorem. Kernel-checked, standard axioms only.
2. **The bridge, a new island pinned to OpenAI's toolchain.** It re-exports OpenAI's theorem in
   exactly that form. Kernel-checked, and Comparator-accepted with nanoda on (locally).
3. **The seam between them.** The two islands use different Mathlib pins, and `riemannZeta`
   is *not* the same closed term at the two pins. The statement expression is identical. 267
   definitions underneath it differ, because of six weeks of Mathlib refactoring. Plugging
   piece 2 into piece 1 is therefore a mathematical identification, not a kernel check. Details
   are in section 3.

A zero-free half-plane is not RH. RH is θ = 1/2, which would give Λ ≤ 0.

**Update, later on 2026-10-07: the seam is closed for this theorem.** The dbn closure of the
corollary (19 modules) is now ported to OpenAI's exact pin, inside the same materialized
workspace. Two one-line patches were needed. The unconditional theorem is one kernel term in one
environment:

```lean
theorem dbn_real_zeros_of_qrh_unconditional :
    ∀ t : ℝ, 9 / 32 ≤ t → ∀ z : ℂ, DBN.H t z = 0 → z.im = 0 :=
  dbn_real_zeros_of_qrh qrh_seven_eighths
```

Its axioms are `[propext, Classical.choice, Quot.sound]`. Comparator, run locally with nanoda on,
accepts it against a challenge that imports only Mathlib. A tampered challenge is rejected. See
section 6. **Section 6 supersedes the seam caveat of section 3 for this theorem.** Section 3
still applies to the original v4.34.0-rc1 dbn-island artifacts, which pair with the bridge only
across pins.

## 1. The corollary (dbn island)

File: `telperion/examples/dbn/lean/DBNZeroFreeHalfplane.lean`. The island is on Lean v4.34.0-rc1 and
Mathlib de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11, which we verified in `lean-toolchain` and
`lake-manifest.json`.

```lean
theorem dbn_real_zeros_of_zeta_halfplane (θ : ℝ)
    (hfree : ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0) :
    ∀ t : ℝ, 2 * (θ - 1 / 2) ^ 2 ≤ t → ∀ z : ℂ, DBN.H t z = 0 → z.im = 0

theorem dbn_real_zeros_of_qrh
    (hqrh : ∀ s : ℂ, (7 / 8 : ℝ) < s.re → riemannZeta s ≠ 0) :
    ∀ t : ℝ, 9 / 32 ≤ t → ∀ z : ℂ, DBN.H t z = 0 → z.im = 0

theorem dbn_H0_im_sq_le_of_qrh
    (hqrh : ∀ s : ℂ, (7 / 8 : ℝ) < s.re → riemannZeta s ≠ 0) :
    ∀ z : ℂ, DBN.H 0 z = 0 → z.im ^ 2 ≤ 9 / 16
```

The helpers are `DBN.H0_neg_im_le_of_zeta_halfplane` and `DBN.H0_im_sq_le_of_zeta_halfplane`.

How the proof goes. A zero z of H_0 gives a zero s = 1/2 + iz/2 of ξ, because H_0 = ξ(1/2 + iz/2)/8
(`dbn_H0_eq_xi`). That s is a strip zero of ζ (`riemannXi_eq_zero_iff_strip_zero`), with
Re s = 1/2 − Im z/2 (`xiArg_re`). The half-plane hypothesis gives Re s ≤ θ, so −Im z ≤ 2θ − 1.
Evenness (`H_neg`) gives the same bound for −z, hence (Im z)² ≤ (2θ − 1)². Then
`m1_H_real_zeros_of_im_sq_le`, the machinery behind `dbn_debruijn_parametric` (heat-flow
contraction plus Hurwitz), closes the strip at t = (2θ − 1)²/2 = 2(θ − 1/2)². No side condition
on θ is needed. For θ < 1/2 the two one-sided bounds contradict each other, so the conclusion is
vacuous there.

**Λ is not defined on the island.** That is deliberate: DBNDefs avoids the `sInf` trap. So the
bound is stated in sInf-free form: "every zero of H_t is real for every t ≥ 9/32".

**The hypothesis matches OpenAI's statement.** `OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re`
is stated as `{s : ℂ} (hs : (7 / 8 : ℝ) < s.re) : riemannZeta s ≠ 0`. Our hypothesis closes that
implicit binder: `∀ s : ℂ, (7 / 8 : ℝ) < s.re → riemannZeta s ≠ 0`.

**Axioms.** All five theorems give `[propext, Classical.choice, Quot.sound]`. They were added to
`AxiomGuardDBN.lean`. The full island build of 8,809 jobs is green locally, the guard has 654
entries, and there are 0 `sorryAx`.

## 2. The bridge island (`telperion/examples/oai_qrh_bridge`)

```lean
-- lean/ArdaQRHBridge.lean, built inside openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- (Lean v4.34.1, Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612)
import OAI.NumberTheory.DirichletL.Nonvanishing
theorem qrh_seven_eighths : ∀ s : ℂ, (7 / 8 : ℝ) < s.re → riemannZeta s ≠ 0 :=
  fun _ hs ↦ OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re hs
```

The proof is entirely OpenAI's, from https://github.com/openai/math under the Apache License 2.0.
The README and the file headers say so.

**Why it is a recipe and not a Lake dependency.** We tried
`require OAI from git "https://github.com/openai/math.git" @ "adc7f124…" / "lean"`. `lake update`
ran for 5 min 51 s and then failed with
`error: iut: Lake resolved an unexpected checkout at …/.lake/packages/iut`. OpenAI's lakefile
patches 23 of its dependencies. It does this in a `run_cmd` during lakefile elaboration and in a
`post_update` hook, and both assume OpenAI's package is the workspace root. Vendoring the closure
is the other option: about 2,924 modules and 486k lines, plus PNT+ Wiener and one Rellich file.
We rejected it as a maintenance burden.

What we built instead: `materialize.sh` checks out OpenAI's `lean/` directory, unmodified, at the
pinned commit into `work/oai` (gitignored). It copies in our two `.lean` files and the Comparator
configs, and appends two `lean_lib` lines to OpenAI's lakefile. OpenAI stays the root.
`--from-local DIR` reflinks an already-built copy, after a file-by-file diff against the pinned
git checkout. That is how we built locally from `~/oai-replay`, whose sources diff clean against
adc7f124.

| Measurement (this Mac, 2026-10-07) | Value |
|---|---|
| Materialize from the replay build (APFS reflink) | 81 s, 21 GB apparent, about 0 GB new disk |
| `lake build ArdaQRHBridge AxiomGuardQRHBridge` | 45 s, 7,065 jobs, only the 2 new modules compiled |
| `#print axioms qrh_seven_eighths` | `[propext, Classical.choice, Quot.sound]` |
| Comparator on `qrh_seven_eighths`, nanoda ON | "nanoda kernel accepts", "Lean default kernel accepts", "Your solution is okay!", EXIT 0 |
| Comparator wall time and peak RSS | 516 s, 9.4 GB |
| From-scratch build, extrapolated from the replay | about 11.9k jobs for the closure, `.lake` about 19 GB, several CPU-hours |

The Comparator run was local and not sandboxed. landrun is Linux-only, so we used a pass-through
shim, as in our BG replays. The config was self-check (challenge module = solution module =
`ArdaQRHBridge`), as the missions judge does. The statement's Mathlib-only reading was already
checked by the replay of OpenAI's own challenge
(`ComparatorChallenges/QuasiRiemannHypothesis.lean`, `import Mathlib` only). The bridge adds
only the closure over `{s}`. `lean/QuasiRiemannHypothesis.comparator.json` re-runs that replay
inside the materialized workspace.

**CI.** No workflow builds this island yet. We wrote a draft at
`oai_qrh_bridge/ci/oai-qrh-bridge.yml.draft`. It is inactive: it is not under `.github/workflows`.
Until something like it runs, `mission verify` lists `oai_qrh_bridge` as an orphan island. That
is a warning. The grant gate (`verify.py:581`, `artifact_coverage_error`) refuses any node whose
artifact lives there. Turning the workflow on is the owner's call, because a cold build costs
hours of runner time.

## 3. Cross-pin fidelity: is `riemannZeta` the same at both pins?

**Verdict: no, not as a closed term.** The two statements are syntactically identical at the top
level. They use the same constants, the same instance terms, and the same numerals. But the
definitions those constants unfold to differ between Mathlib de5ce8a9 and d13f23b, and the
Lean cores (v4.34.0-rc1 and v4.34.1) differ too.

**Method** (`oai_qrh_bridge/fidelity/`, reproducible with `run_fidelity.sh`):
- In each environment we copy the *elaborated* statement into a definition `QRHFidelity.stmt`. On
  the dbn side it is the hypothesis of `dbn_real_zeros_of_qrh`. On the bridge side it is the type
  of `qrh_seven_eighths`.
- We export each with lean4export (format 3.1.0). The dbn side used lean4export at tag
  v4.34.0-rc1, which we built for this job. The bridge side used Comparator's copy on v4.34.1.
- `compare_exports.py` hashes every constant structurally and walks the *meaning closure*: types
  everywhere, values of definitions, opaques and recursor rules, but not theorem proofs, which
  are irrelevant by proof irrelevance.
- It then normalizes three kinds of noise:
  - universe-parameter renaming;
  - hygienic, private and auxiliary names, which are compared by content because they embed module
    paths (`Mathlib/Data/Real/Basic` moved to `Mathlib/Basic/Real/Basic`);
  - references to theorems, which are compared by statement.

| | dbn side | bridge side |
|---|---|---|
| Lean | v4.34.0-rc1 (3447a668) | v4.34.1 (5045d005) |
| constants exported | 53,251 | 53,309 |
| meaning closure | 4,978 | 4,982 |

Normalized results (`fidelity/RESULT_2026-10-07.json`):

- **The statement itself is identical.** The normalized root digest is
  `a8dc112e9afc62ef99b1f82e87e196e7` on both sides.
- **267 named definitions in the closure differ, and 87 theorem statements differ.** Six named
  definitions appear only on the dbn side and twenty only on the bridge side.
- **27 root causes** are differing definitions whose own named dependencies agree. They are listed
  with term excerpts in `fidelity/root_causes_2026-10-07.txt`. They fall into these groups:
  - The algebraic hierarchy refactor. `AddMonoid.mk`, `Monoid.mk`, `AddZeroClass.mk` and
    `MulOneClass.mk` have different parents and field orders, for example `AddMonoid` now takes
    `Zero`, `Add` and `add_assoc` directly instead of `AddSemigroup`. Their projections
    (`toZero`, `toNSMul`, `toAddSemigroup`, `toOne`, `toNPow`, …) change accordingly.
  - `WellFoundedLT` is `IsWellFounded` at de5ce8a9 and `WellFounded` at d13f23b.
  - `MeasureTheory.eLpNorm` gained a `[TopologicalSpace]` argument. ζ is defined through
    Mellin-transform integrals, so measure theory is in the closure.
  - Core `Bool.and` is defined through `match_1` in rc1 and directly through `Bool.rec` in v4.34.1.
  - Content changes behind private or auxiliary constants: `Real.instMax`/`instMin` (private
    `Real.sup`/`inf`), `Nat.findX`, `instLEENat`, `instLTENat`, `ENNReal.instLE`,
    `WithTop.instLE`/`instLT`, `NNReal.instSemilatticeSup`, `Semiring.toModule`,
    `StrictMono.orderIsoOfSurjective`.
  - One normalizer artifact: `Finsupp` differs only by `max u v` against `max v u` in its universe.
- **The fresh elaboration differs from the theorem-derived statement only in a proof.** In both
  environments, `QRHFidelity.stmtMathlib` (the text re-elaborated) differs from `QRHFidelity.stmt`
  only in how the `Nat.AtLeastTwo` instance proofs for the numerals 7 and 8 are given: an
  auxiliary `_proof_N` constant or an inline term. That is a proof-level difference with no
  effect on meaning.

**What this means.** No single kernel run checks "OpenAI's ζ is our ζ", and with these pins none
can. The identification rests on mathematics:
- ζ is pinned down by its Dirichlet series on Re s > 1, together with its holomorphy on ℂ \ {1}
  and the identity theorem.
- ℝ, ℂ and the integrals are pinned down by their characterizing properties.
- The refactors above are meant to preserve all of those.

That argument is standard. It is not machine-checked across the pins. A grant ledger entry must
say so in words.

**Closing the seam completely** requires a single pin. Two options:
1. Port the dbn Λ closure to d13f23b and v4.34.1, building it inside the materialized OpenAI
   workspace. The closure is DBNDefs, Step, Hurwitz, HeatApprox, Hadamard*, M1Approx,
   M1Parametric, the DBNXi* modules, DBNRealZerosIff* and LiCriterion. This is moderate work,
   because six weeks of Mathlib renames apply.
2. Wait for both to meet on a later common Mathlib.

Either way, `dbn_real_zeros_of_qrh qrh_seven_eighths` becomes a one-line, single-kernel term.

## 4. Feasibility of reusing OpenAI's LogarithmicControl.lean

`OAI/NumberTheory/DirichletL/LogarithmicControl.lean` has 547 lines, imports only Mathlib, and
lives in `namespace OAI.SevenEighths.LogarithmicControl`. We compiled it **unmodified**:
- On the rvm_bridge pin (Lean v4.33.0-rc2, Mathlib 51e6992e): 0 errors, 0 warnings, about 20 s.
- On the dbn pin (v4.34.0-rc1, Mathlib de5ce8a9): 0 errors.

`#print axioms` for `logarithmic_control`, `zero_free_disk_logarithm` and `three_circles` gives
the three standard axioms. All eight imports exist at both pins, and so do the key lemmas
`Complex.exists_continuousOn_eqOn_exp_comp`, `contractibleSpace_ball` and `borelCaratheodory`.

So the port costs nothing beyond copying the file with its Apache-2.0 header and NOTICE
attribution. The real work is deciding what consumes it on rvm_bridge: its holomorphic-logarithm,
Borel-Carathéodory-on-closed-balls and three-circles lemmas, and the log-derivative bound in a
zero-free disk. We did not add it to any island.

## 5. Registration: prepared, NOT executed

Repo convention (`MISSIONS_DESIGN_2026-09-11.md` §2, and node `RH_dlvp_zero_free_region`):
- A proved artifact on another island discharges a node through a *syntactic* statement match.
- It is recorded `via = "direct"`, and `closure_clean` is computed by the gate.
- Independence comes either from an audit by a different session and identity, or from a passing
  `missions-comparator` run that has been recorded (`AUDIT_INDEPENDENCE_2026-09-23.md`).
- No campaign has a `via = "reduction"` node yet, so the reduction path below would be its first
  use.

Proposed nodes, all in campaign `rh` (statement package on v4.34.0-rc1, de5ce8a9, `import Statements.RHDefs`):

| Slug | Statement (registered text) | Artifact | Notes |
|---|---|---|---|
| `RH_dbn_real_zeros_of_zeta_halfplane` | `theorem dbn_real_zeros_of_zeta_halfplane (θ : ℝ) (hfree : ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0) : ∀ t : ℝ, 2 * (θ - 1 / 2) ^ 2 ≤ t → ∀ z : ℂ, DBN.H t z = 0 → z.im = 0` | `../../examples/dbn/lean/DBNZeroFreeHalfplane.lean`, direct | dbn island, CI-built, judge-able. deps: `RH_dbn_debruijn_parametric`, `RH_dbn_H0_eq_xi` |
| `RH_dbn_real_zeros_of_qrh` | `theorem dbn_real_zeros_of_qrh (hqrh : ∀ s : ℂ, (7 / 8 : ℝ) < s.re → riemannZeta s ≠ 0) : ∀ t : ℝ, 9 / 32 ≤ t → ∀ z : ℂ, DBN.H t z = 0 → z.im = 0` | same file, direct | conditional 9/32 |
| `RH_zeta_zero_free_seven_eighths` | `theorem qrh_seven_eighths : ∀ s : ℂ, (7 / 8 : ℝ) < s.re → riemannZeta s ≠ 0` | `../../examples/oai_qrh_bridge/lean/ArdaQRHBridge.lean`, direct | BLOCKED: no CI covers it, so the gate refuses. Cross-pin. OpenAI authorship must be in the readback |
| `RH_dbn_real_zeros_nine_thirtyseconds` (milestone) | `theorem dbn_real_zeros_nine_thirtyseconds : ∀ t : ℝ, 9 / 32 ≤ t → ∀ z : ℂ, DBN.H t z = 0 → z.im = 0` | reduction proof `dbn_real_zeros_of_qrh qrh_seven_eighths` in the rh statement package | needs both deps proved first. The first reduction node in the repo |

Commands. The **author side** may be run by this session or by the parent, since adding a node
is authoring:

```sh
cd ~/arda-qrh/telperion
telperion mission add rh RH.dbn_real_zeros_of_zeta_halfplane --kind lemma \
  --title "Zero-free half-plane theta => every zero of H_t real for t >= 2(theta-1/2)^2 (conditional; not RH). conjecture1_proved = False" \
  --deps RH_dbn_debruijn_parametric,RH_dbn_H0_eq_xi --statement-file <file with the statement above>
telperion mission add rh RH.dbn_real_zeros_of_qrh --kind lemma \
  --title "QRH hypothesis (zeta != 0 on Re s > 7/8) => every zero of H_t real for t >= 9/32 (conditional; not RH). conjecture1_proved = False" \
  --deps RH_dbn_real_zeros_of_zeta_halfplane --statement-file <...>
telperion mission add rh RH.zeta_zero_free_seven_eighths --kind lemma \
  --title "zeta != 0 on Re s > 7/8 (OpenAI openai/math family 003, Apache-2.0; cross-pin bridge). Not RH. conjecture1_proved = False" \
  --statement-file <...>
telperion mission link RH_dbn_real_zeros_of_zeta_halfplane --artifact ../../examples/dbn/lean/DBNZeroFreeHalfplane.lean --kind lean_module --via direct
telperion mission link RH_dbn_real_zeros_of_qrh --artifact ../../examples/dbn/lean/DBNZeroFreeHalfplane.lean --kind lean_module --via direct
telperion mission link RH_zeta_zero_free_seven_eighths --artifact ../../examples/oai_qrh_bridge/lean/ArdaQRHBridge.lean --kind lean_module --via direct
python -m telperion.missions.judge --island dbn      # regenerates telperion/missions/judge/dbn with the 2 new bridges
```

The **independent session** must have a different session id and a different git identity from
the author:

```sh
# 1. read-backs (each >= 120 chars, rendering the FORMAL statement, written before reading the artifact)
telperion mission audit RH_dbn_real_zeros_of_zeta_halfplane --text "<own rendering>"
telperion mission audit RH_dbn_real_zeros_of_qrh --text "<own rendering>"
telperion mission audit RH_zeta_zero_free_seven_eighths --text "<own rendering; must state the cross-pin seam and OpenAI authorship>"
# 2. grants (dbn nodes now; the QRH node only after an oai-qrh-bridge workflow covers its artifact)
telperion mission grant RH_dbn_real_zeros_of_zeta_halfplane
telperion mission grant RH_dbn_real_zeros_of_qrh
telperion mission grant RH_zeta_zero_free_seven_eighths      # refused until CI covers oai_qrh_bridge
# 3. after missions-comparator passes on the pushed, GRANTED registry (record refuses a non-proved node):
telperion mission comparator-record RH_dbn_real_zeros_of_zeta_halfplane --run-id <run> --theorem dbn_real_zeros_of_zeta_halfplane
telperion mission comparator-record RH_dbn_real_zeros_of_qrh --run-id <run> --theorem dbn_real_zeros_of_qrh
telperion mission verify rh
```

(Corrected 2026-10-08: an earlier version of this block put `comparator-record` before the
grant. `comparator-record` refuses a node that is not proved, so the order is the one in
section 8.)

Open governance questions for the owner. The tooling does not decide these.
1. Should a node whose kernel authority is a different Mathlib pin be grantable at all, given that
   section 3 shows the terms are not identical? The precedent `RH_dlvp_zero_free_region` was
   cross-*island*, not demonstrably cross-*meaning*.
2. Should the oai-qrh-bridge CI job be activated, given its hours-long cold build?
3. Should the unconditional 9/32 milestone wait for a single-pin port (section 3, option 1)?

## 6. Single-pin port: the unconditional theorem in one environment

**Where.** The port lives in `telperion/examples/oai_qrh_bridge`. `materialize.sh` puts it into the
same unmodified openai/math checkout (adc7f124, Lean v4.34.1, Mathlib d13f23b):
- It copies the 19 dbn modules **from the dbn island sources**. Nothing is duplicated in git.
- It applies `dbn_port/patches/*.patch`.
- It adds `dbn_port/Lc/` and the new `lean/` files.
- New lean_libs: `ArdaDBNPort`, `ArdaLiCriterionShim`, `ArdaDBNUnconditional`
  (with `AxiomGuardDBNUnconditional`), `ArdaDBNChallenge` and `ArdaDBNNegativeControl`.
- The dbn island itself is untouched. Its corollary commit stays as it is.

**The closure that was ported.** It is the import closure of `DBNZeroFreeHalfplane` on the dbn
island: 19 modules, 5,512 lines (DBNZeroFreeHalfplane, DBNRealZerosIffFinal, DBNRealZerosIff,
DBNDefs, DBNXi, DBNXiIBP, DBNGKernel, DBNXiCos, DBNXiRiemann, DBNM1Parametric, DBNM1Approx,
DBNHadamard, DBNHadamardLinear, DBNHadamardMean, DBNHadamardProduct, DBNHadamardCount, DBNStep,
DBNHeatApprox, DBNHurwitz). Two LiCriterion modules come with it.

**Byte identity, with every change and its reason.**

| File | Change | Reason (Mathlib d13f23b vs de5ce8a9) |
|---|---|---|
| 17 of the 19 DBN modules | none, byte-identical (checked with `cmp`) | |
| `DBNHadamardProduct.lean:207` | `Finset.prod_le_prod` becomes `Finset.prod_le_prod₀` | Mathlib renamed the nonnegative-factor lemma to `prod_le_prod₀` on 2026-09-01. The old name now denotes the ordered-monoid lemma (former `prod_le_prod'`), which takes one argument. |
| `DBNHadamardMean.lean:116` | `(norm_nonneg _)` becomes `(neg_one_lt_zero.le.trans (norm_nonneg _))` | `Real.posLog_le_posLog` now assumes `-1 ≤ x` instead of `0 ≤ x`. The weaker hypothesis is derived from the old one. |
| `Lc/XiZeros.lean` (LiCriterion @ 35df682f) | none, byte-identical | |
| `Lc/LiCriterion/Basic.lean` (LiCriterion @ 35df682f) | trimmed to 3 declarations copied verbatim (`NontrivialZero`, `riemannXi`, `xi_zeros_are_nontrivial_zeros`), with upstream's `open` lines and namespace | The closure uses only these three. Upstream's 5,159-line file pulls in a 23k-line Hadamard/genus-one stack that is not needed. Keeping the module name lets `DBNDefs` port byte-identically. The trimmed file also leaves out upstream's literature axioms, which no dbn theorem used anyway (the dbn guard was already clean). Apache-2.0 modification notice in the header. |
| build options | `ArdaDBNPort` sets `autoImplicit := true`. The LiCriterion shim sets `autoImplicit := false, maxSynthPendingDepth := 3` | These restore each source package's own options. OpenAI's package default is `autoImplicit := false`. |

The two patches are the whole diff. Both are proof-term repairs inside proofs. No statement, and
no definition, changed.

**Results.** All of these were run locally on 2026-10-07.

| Check | Result |
|---|---|
| `lake build ArdaLiCriterionShim ArdaDBNPort` after a fresh materialize | green, no warnings |
| full rebuild, fresh materialize: `ArdaQRHBridge AxiomGuardQRHBridge ArdaDBNUnconditional ArdaDBNChallenge ArdaDBNNegativeControl` | green, 11,900 jobs, 94 s wall (port compiled, OpenAI closure replayed) |
| `#print axioms dbn_real_zeros_of_qrh_unconditional` | `[propext, Classical.choice, Quot.sound]` |
| `#print axioms` for `dbn_real_zeros_of_qrh`, `dbn_real_zeros_of_zeta_halfplane`, `qrh_seven_eighths`, `dbn_debruijn_parametric`, `dbn_H0_eq_xi`, `LiCriterion.xi_zeros_are_nontrivial_zeros`, `DBN.H_neg` | all `[propext, Classical.choice, Quot.sound]` |
| Comparator, nanoda ON, challenge `ArdaDBNChallenge` (imports only Mathlib) vs solution `ArdaDBNUnconditional` | "nanoda kernel accepts", "Lean default kernel accepts", "Your solution is okay!", EXIT 0. 473 s, 9.1 GB |
| Negative control: the same challenge with `Φ`'s `e^{9u}` changed to `e^{8u}` | rejected: `Const does not match between challenge and target 'DBN.Φ'`, EXIT 1 |

The trimmed log is at `oai_qrh_bridge/logs/comparator_2026-10-07.txt`. Not sandboxed: landrun is
Linux-only, so a pass-through shim was used.

**The challenge.** `lean/ArdaDBNChallenge.lean` imports only `Mathlib`. It transcribes `DBN.Φ`,
`DBN.HIntegrand` and `DBN.H` verbatim from DBNDefs, under DBNDefs' `open` line and namespace.
Comparator's export comparison therefore forces the solution's `DBN.H` to be exactly this term.
The theorem body is `sorry`, by the Comparator challenge convention.

One footgun is worth recording. The first run was rejected with `Const does not match … 'DBN.Φ'`.
Under `pp.all`, the only difference was the auxiliary proof of the `Nat.AtLeastTwo 4` instance
inside `Φ`. DBNDefs elaborates `thetaMoment` first. Lean abstracts that instance proof into
`DBN.thetaMoment._proof_1` and *reuses* it in `Φ`. The challenge, without `thetaMoment`,
generated `DBN.Φ._proof_5` instead. Transcribing `thetaMoment` verbatim as well fixed it, and the
`pp.all` dumps are then identical. So a transcribed challenge must also reproduce the earlier
definitions whose auxiliary lemmas the target reuses, not only the definitions the statement
mentions.

**What this does and does not establish.** One Lean environment now contains, at once:
- the de Bruijn-Newman machinery, ported with the two patches above;
- the representation H_0 = ξ/8;
- OpenAI's ζ ≠ 0 on Re s > 7/8;
- the composition of all three.

So "every zero of H_t is real for t ≥ 9/32", which is classically Λ ≤ 9/32, is a single
kernel-checked theorem on Mathlib's `riemannZeta`. Nanoda independently re-checked it, and no
cross-pin identification is involved. It is still not RH. 9/32 is weaker than the numerical
bounds 0.22 and 0.2.

**What remains.**
- The rc1 dbn-island artifacts still pair with the bridge only across pins (section 3).
- The single-pin artifacts are not built by CI. The section 2 draft workflow would need the
  `ArdaDBNUnconditional ArdaDBNChallenge` targets added.
- Nothing is registered.

**Registration option this enables** (prepared, NOT executed). Add one node,
`RH_dbn_real_zeros_nine_thirtyseconds`, with this statement:
`theorem dbn_real_zeros_of_qrh_unconditional : ∀ t : ℝ, 9 / 32 ≤ t → ∀ z : ℂ, DBN.H t z = 0 → z.im = 0`.
- Its artifact is `../../examples/oai_qrh_bridge/lean/ArdaDBNUnconditional.lean`, `--via direct`.
- That replaces the reduction route in the section 5 table. No reduction node and no cross-pin
  grant are needed.
- It needs the same CI coverage before the gate will grant.
- `RH.dbn_H0_eq_xi`'s mirror of `DBN.H` in `Statements/RHDefs.lean` is on de5ce8a9. The registry
  statement match is syntactic, so it matches. The independent judge for this node is the
  single-pin Comparator run above, re-run by the independent session:
  `lake env comparator dbn_real_zeros_of_qrh_unconditional.comparator.json` inside the
  materialized workspace.

## 7. Commits on `rh/qrh-dbn-9-32`

The commit hashes are in `git log`. The branch was pushed on 2026-10-07 at the owner's request and is draft PR #662 (no grant). An independent session audited it (commit 4f4588fae, `QRH_DBN_AUDIT_2026-10-07_e9.md`): every result reproduced, including Comparator with nanoda on (unconditional theorem accepted, tampered control rejected, `qrh_seven_eighths` accepted). Registry independence still needs the operator's read-back and the missions-comparator CI path, because both sessions share one git identity (section 8).

## 8. The missions judge on `oai_qrh_bridge` (2026-10-08)

**What was added.** The independent missions judge (`telperion/src/telperion/missions/judge.py`)
now covers the materialized island. Two of the four nodes registered in 12009b447 have their
artifact here. The other two are on the dbn island and use the dbn bundle.

| Node | Island | Artifact theorem | Bridge theorem |
|---|---|---|---|
| `RH_zeta_zero_free_seven_eighths` | oai_qrh_bridge | `qrh_seven_eighths` (ArdaQRHBridge) | `MissionJudge.RH_zeta_zero_free_seven_eighths` |
| `RH_dbn_real_zeros_nine_thirtyseconds` | oai_qrh_bridge | `dbn_real_zeros_of_qrh_unconditional` (ArdaDBNUnconditional) | `MissionJudge.RH_dbn_real_zeros_nine_thirtyseconds` |
| `RH_dbn_real_zeros_of_zeta_halfplane` | dbn | `dbn_real_zeros_of_zeta_halfplane` | dbn bundle |
| `RH_dbn_real_zeros_of_qrh` | dbn | `dbn_real_zeros_of_qrh` | dbn bundle |

**How it works.** OpenAI's package has to stay the workspace root, so the judge cannot
path-require the island as it does everywhere else. The bundle in
`telperion/missions/judge/oai_qrh_bridge/` carries a lakefile stanza instead of a lakefile.
`telperion/scripts/judge_materialize.sh` installs it into a materialized `work/oai`: it copies
the bridge modules and Comparator configs in and appends one `lean_lib MissionChallenges`.
Each bridge imports its artifact plus both island guards (AxiomGuardDBNUnconditional and
AxiomGuardQRHBridge), and states the registered statement verbatim as the type of
`MissionJudge.<Slug> := <artifact theorem>`. The Comparator is tag v4.34.0 built with toolchain
v4.34.1, nanoda on, axioms `[propext, Quot.sound, Classical.choice]`.

The reviewing session built exactly these two bridge theorems at OpenAI's pin, as an appended
lean_lib, with standard axioms only. The three imports co-import cleanly.

**Why the committed bundle is empty.** Both nodes are draft. The judge renders proved nodes
only, and `mission comparator-record` refuses a node that is not proved. So before the grant
there is nothing to record and nothing to judge in CI. For local pre-grant checking only,
`--pending --out <scratch>` renders the draft nodes into a scratch directory. It is never
committed and never runs in CI.

**CI.** `missions-comparator.yml` has a new job, `judge-oai-qrh-bridge`. It lists the island's
proved nodes and exits with a notice when there are none. Otherwise it materializes the
workspace with the island's own `materialize.sh` and restores `oai-qrh-bridge.yml`'s build
checkpoint under the same cache key, read-only. It then installs the bundle, builds the bridge
modules by name, and runs the Comparator on each. `ELAN_TOOLCHAIN` is pinned to v4.34.1 for
the whole job, because the runner has no elan default (the 60b2cade9 fix).
GitHub's Actions cache is branch-scoped, and this job only restores, never saves. So until
`oai-qrh-bridge.yml` has saved a checkpoint on `main` (or on the branch being run), the judge
job on any other branch does a cold build of OpenAI's closure first (about 80 minutes on the
runner) before the Comparator stage.

**The grant order, exactly.** Every local session shares the identity
`dr.murphy.is.in@arda-dao.com`, and `mission audit` refuses an auditor with the author's
session or identity. So the read-back has to come from the operator, as
`MISSIONS_DESIGN_2026-09-11.md` section 8 allows.

1. The **operator** (the user, under their own identity, not an arda-dao.com one, and their
   own session id) writes a read-back for each of the four nodes:
   ```sh
   telperion mission audit RH_dbn_real_zeros_of_zeta_halfplane --text "<own rendering>" --identity <email> --session <id>
   telperion mission audit RH_dbn_real_zeros_of_qrh --text "<own rendering>" --identity <email> --session <id>
   telperion mission audit RH_zeta_zero_free_seven_eighths --text "<own rendering; cross-pin seam and OpenAI authorship>" --identity <email> --session <id>
   telperion mission audit RH_dbn_real_zeros_nine_thirtyseconds --text "<own rendering>" --identity <email> --session <id>
   ```
   This moves each node from draft to open.
2. `telperion mission grant <slug>` for each node. The gate still requires CI coverage of the
   artifact (oai-qrh-bridge.yml covers both oai_qrh_bridge artifacts).
3. Regenerate the bundles (`python -m telperion.missions.judge --island oai_qrh_bridge`, and
   `--island dbn`), push, and let a **missions-comparator** CI run judge the now-proved nodes.
4. `telperion mission comparator-record <slug> --run-id <run> --theorem <theorem> --run-url <url>`
   for each node that passed.

Never run `comparator-record` before the grant. The tool refuses it, and a pass on a pending
bundle is not a recordable run.

**Status, 2026-10-09: the chain is closed.** The operator recorded the four read-backs under
their own identity (118d2d42d, `independence = "independent"`); session e9 granted all four
through the gate (PR #667); `missions-comparator` run 37955041118 passed every node with
nanoda on (dbn shard for the two conditional nodes, `judge-oai-qrh-bridge` for the two bridge
nodes; the bridge pair also passed on main's run 37955332482); and the records were written
with `log_check = "verified"`, `head_check = "matched"` (PR #669). All four nodes are
`proved` on main and no longer appear in `mission provenance-report`. The explorer labels
them judge-verified. Nothing here is RH. conjecture1_proved = False.

**What it does not establish.** The shadowing guard covers the island's own modules, not the
roughly 2,900 OpenAI modules outside the guards' import closure. The judge resolves the
statement in the artifact's environment at OpenAI's pin, so whether the rh campaign's
vocabulary mirror (on de5ce8a9) means the same thing is still section 3's question. It is not
RH. conjecture1_proved = False.
