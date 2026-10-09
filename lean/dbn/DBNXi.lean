/-
  DBNXi -- Route C / C2, module E of the design memo
  telperion/docs/DESIGN_RH_dbn_H0_eq_xi_2026-09-22.md (section 2 "Assembly", section 5 row E).

  The representation theorem (registry node RH.dbn_H0_eq_xi, statement verbatim):

    H_0(z) = (1/8) ξ(1/2 + iz/2)        for EVERY z ∈ ℂ,

  with `H_0 = DBN.H 0` the island's `∫_0^∞ Φ(u) cos(zu) du` and `ξ = LiCriterion.riemannXi`, the
  pinned upstream ENTIRE xi `(1/2) s (s − 1) Λ₀(s) + 1/2` built on Mathlib's
  `completedRiemannZeta₀` (so no `s ≠ 0, 1` side condition appears anywhere).

  Assembly (pure algebra on the three inputs):
    * module B (DBNXiCos): `Λ₀(1/2 + iz/2) = 8 J(z)`, `J(z) := ∫_0^∞ g(u) cos(zu) du`,
    * modules C + D (DBNGKernel, DBNXiIBP): `(z² + 1) J(z) = 1/2 − 8 H_0(z)`,
    * at `s = 1/2 + iz/2`: `s (s − 1) = −(z² + 1)/4`, so
      `ξ(s) = (1/2)(−(z² + 1)/4)(8 J) + 1/2 = −(z² + 1) J + 1/2 = 8 H_0(z)`.
  Module A (DBNXiRiemann) enters through B.

  What IS proved here (axiom-clean, see AxiomGuardDBN.lean):
    * `dbn_H0_eq_xi` -- the registry statement of RH.dbn_H0_eq_xi, verbatim, unconditional;
    * `DBN.H_zero_I : H 0 I = 1/16` -- the sanity corollary at `z = i` (`1/2 + i·i/2 = 0` and
      `ξ(0) = 1/2`), i.e. `∫_0^∞ Φ(u) cosh(u) du = 1/16`.

  SCOPE.  This is an identity between two entire functions (Riemann 1859; Titchmarsh, The Theory
  of the Riemann Zeta-Function, 2nd ed., section 10.1; Polymath15 arXiv:1904.12438 eq. (3)).  It
  is NOT RH-equivalent and says nothing about where the zeros of ξ, H_0 or H_t lie, nothing about
  the de Bruijn-Newman constant (not defined on this island), and nothing about de Bruijn's
  t ≥ 1/2 theorem (registry node RH.dbn_debruijn_real_zeros, a separate node, not proved here).
  Nothing here proves RH.  conjecture1_proved = False.
-/
import DBNXiCos
import DBNXiIBP

open MeasureTheory Set

/-- **The C2 representation theorem** (registry node RH.dbn_H0_eq_xi, statement verbatim):
`H_0(z) = (1/8) ξ(1/2 + iz/2)` for every complex `z`, with `ξ = LiCriterion.riemannXi` the entire
xi.  An identity between two entire functions; NOT RH-equivalent, and nothing here concerns the
location of any zero.  Nothing here proves RH.  conjecture1_proved = False. -/
theorem dbn_H0_eq_xi (z : ℂ) :
    DBN.H 0 z = (1 / 8 : ℂ) * LiCriterion.riemannXi (1 / 2 + Complex.I * z / 2) := by
  set J : ℂ := ∫ u in Ioi (0 : ℝ), ((DBN.g u : ℝ) : ℂ) * Complex.cos (z * u)
  have hB : completedRiemannZeta₀ (1 / 2 + Complex.I * z / 2) = 8 * J :=
    DBN.completedRiemannZeta₀_half_add_eq z
  have hD : (z ^ 2 + 1) * J = 1 / 2 - 8 * DBN.H 0 z := DBN.integral_g_cos_eq z
  unfold LiCriterion.riemannXi
  rw [hB]
  linear_combination (1 / 8 : ℂ) * hD - (J * z ^ 2 / 8) * Complex.I_sq

namespace DBN

/-- **Sanity corollary at `z = i`**: `H_0(i) = 1/16`, i.e. `∫_0^∞ Φ(u) cosh(u) du = 1/16`
(`1/2 + i·i/2 = 0` and `ξ(0) = 1/2`; the design memo's section 4 audits this numerically). -/
theorem H_zero_I : H 0 Complex.I = 1 / 16 := by
  rw [dbn_H0_eq_xi]
  have h0 : (1 / 2 + Complex.I * Complex.I / 2 : ℂ) = 0 := by
    rw [Complex.I_mul_I]
    ring
  rw [h0]
  unfold LiCriterion.riemannXi
  ring

end DBN
