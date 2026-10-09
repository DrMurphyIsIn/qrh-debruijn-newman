/-
  ArdaDBNUnconditional -- the de Bruijn-Newman bound Λ ≤ 9/32, UNCONDITIONAL and in ONE
  environment (Lean v4.34.1, Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612, inside
  openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a).

  `dbn_real_zeros_of_qrh` is the dbn island's conditional corollary (DBNZeroFreeHalfplane, ported
  to this pin; see telperion/docs/QRH_DBN_BRIDGE_2026-10-07.md section 6 for the port record).
  `qrh_seven_eighths` is OpenAI's quasi-Riemann-hypothesis theorem for ζ
  (`OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re`, github.com/openai/math, Apache-2.0),
  re-exported in ArdaQRHBridge.  Both are elaborated against the SAME `riemannZeta`, so this is a
  single kernel check: no cross-pin identification is involved.

  SCOPE.  Classically Λ ≤ 9/32 = 0.28125 (stated sInf-free).  Weaker than Polymath15's 0.22.  A
  zero-free half-plane is not RH; RH is Λ ≤ 0.  Nothing here proves RH.
  conjecture1_proved = False.
-/
import DBNZeroFreeHalfplane
import ArdaQRHBridge

/-- **Every zero of `H_t` is real for every `t ≥ 9/32`**, unconditionally (classically
`Λ ≤ 9/32`): the dbn corollary `dbn_real_zeros_of_qrh` applied to OpenAI's 7/8 zero-free
half-plane `qrh_seven_eighths`, in one environment.  Not RH.  conjecture1_proved = False. -/
theorem dbn_real_zeros_of_qrh_unconditional :
    ∀ t : ℝ, 9 / 32 ≤ t → ∀ z : ℂ, DBN.H t z = 0 → z.im = 0 :=
  dbn_real_zeros_of_qrh qrh_seven_eighths
