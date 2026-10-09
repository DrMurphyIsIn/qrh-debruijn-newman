/-
  ArdaQRHBridge -- re-export of OpenAI's quasi-Riemann-hypothesis theorem for zeta in the exact
  form consumed by the Arda dbn island (`dbn_real_zeros_of_qrh`, DBNZeroFreeHalfplane.lean).

  CREDIT AND LICENSE.  The proof is entirely OpenAI's: `OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re`
  (lean/OAI/NumberTheory/DirichletL/Nonvanishing.lean, family 003 "The quasi-Riemann hypothesis")
  from https://github.com/openai/math at commit adc7f1241b42e322a6451854ab7e4b4c146bf78a,
  licensed under the Apache License, Version 2.0 (lean/LICENSE in that repository).  This file adds
  only the closure over the implicit binder.  It is compiled inside an unmodified checkout of that
  commit (see ../materialize.sh); no OpenAI file is vendored into Arda.

  Toolchain: Lean v4.34.1, Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612 (OpenAI's pins).
  The dbn island that consumes this statement is on Lean v4.34.0-rc1 / Mathlib de5ce8a9; the
  kernel cannot check across the two pins.  The cross-pin identity of `riemannZeta` is
  documented in telperion/docs/QRH_DBN_BRIDGE_2026-10-07.md.

  SCOPE.  A zero-free half-plane `Re s > 7/8` is NOT the Riemann hypothesis (RH is `Re s > 1/2`).
  Nothing here proves RH.  conjecture1_proved = False.
-/
import OAI.NumberTheory.DirichletL.Nonvanishing

/-- **QRH for ζ, re-exported**: `ζ(s) ≠ 0` for `Re s > 7/8`.  OpenAI's theorem
`OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re` (github.com/openai/math, Apache-2.0) with its
implicit binder closed.  The statement is word for word the hypothesis `hqrh` of
`dbn_real_zeros_of_qrh` on the Arda dbn island.  Not RH.  conjecture1_proved = False. -/
theorem qrh_seven_eighths : ∀ s : ℂ, (7 / 8 : ℝ) < s.re → riemannZeta s ≠ 0 :=
  fun _ hs ↦ OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re hs
