# Notice and provenance

- **The result.** Every zero of the de Bruijn–Newman function `H_t` is real for every `t ≥ 9/32`; classically,
  `Λ ≤ 9/32`. It is the composition of two theorems: OpenAI's quasi-Riemann hypothesis
  (`riemannZeta s ≠ 0` for `Re s > 7/8`) and de Bruijn's 1950 theorem as formalized on the Arda dbn island.
  It is not the Riemann Hypothesis, and it is weaker than the numerical bounds `Λ ≤ 0.22` (Polymath15) and
  `Λ ≤ 0.2` (Platt–Trudgian).
- **OpenAI.** The half-plane theorem `OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re` is from
  OpenAI, *The Quasi-Riemann Hypothesis*, OpenAI Math Release preprint, 2026
  (<https://github.com/openai/math>, commit `adc7f124`, Apache-2.0). This repository re-exports it with its
  implicit binder closed and proves nothing about ζ itself.
- **Arda.** The de Bruijn heat-flow machinery (`lean/dbn/`, nineteen modules) and the bridge island were
  developed in the Arda repository (<https://github.com/DrMurphyIsIn/Arda>) and are copied here byte-identically
  from the commit named in `provenance/ARDA_SOURCE`. Two one-line proof-term patches (`lean/patches/`) adapt two
  modules to OpenAI's Mathlib pin; no statement or definition changes.
- **LiCriterion.** `lean/Lc/` is from nicholasbulka/li-criterion-rh-equivalence-lean at `35df682f` (Apache-2.0),
  one file unmodified and one trimmed to three verbatim declarations (`lean/Lc/NOTICE`).
- **Lean and Mathlib.** Lean 4 v4.34.1, Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612` (OpenAI's pins).
- **Verification.** The theorem was checked by Lean's kernel, re-checked by nanoda through openai/ten-proofs
  Comparator (challenge imports only Mathlib; a tampered challenge is rejected), independently audited by a
  second session, and judged in CI against the registered statement (`logs/`, `provenance/`). The pinned
  OpenAI tree and Mathlib's definition of `riemannZeta` are trusted as code; everything else is kernel-checked.
- **Machine assistance.** The formalization, the audit, the tooling and this paper were produced with
  extensive use of an AI coding assistant (Claude, Anthropic) under the direction of the author. The Lean
  kernel is the sole trusted component: every claim here is either a kernel-checked theorem or labelled otherwise.
