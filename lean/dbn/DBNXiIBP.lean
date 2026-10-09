/-
  DBNXiIBP -- Route C / C2, module D of the design memo
  telperion/docs/DESIGN_RH_dbn_H0_eq_xi_2026-09-22.md (section 2 step (4), section 5 row D).

  Two integrations by parts on `(0, ∞)` against `cos(zu)`, for EVERY complex `z`:

    (z² + 1) ∫_0^∞ g(u) cos(zu) du = −g'(0) − ∫_0^∞ (g'' − g)(u) cos(zu) du,

  and, combined with module C's `g'(0) = −1/2` and `∫_0^∞ (g'' − g) cos(zu) du = 8 H_0(z)`,

    (z² + 1) ∫_0^∞ g(u) cos(zu) du = 1/2 − 8 H_0(z).

  Each integration by parts is one application of Mathlib's `integral_Ioi_mul_deriv_eq_deriv_mul`
  (a Bochner-integral statement on `Ioi 0` with values in `ℂ`):
    * IBP-1: `u = g`, `v = −z sin(z·)`, `v' = −z² cos(z·)`; the boundary term vanishes at `0⁺`
      (`sin 0 = 0`) and at `+∞` (super-exponential decay of `g` against `e^{‖z‖u}`);
    * IBP-2: `u = g'`, `v = cos(z·)`, `v' = −z sin(z·)`; the boundary term is `g'(0)` at `0⁺`
      and `0` at `+∞`.
  Every hypothesis (the two `HasDerivAt` families, the four `IntegrableOn` side conditions, the
  four boundary limits) is a lemma of module C (DBNGKernel.lean), stated there in exactly the
  `Pi.mul` shape this lemma consumes; no `tsum` is interchanged with an integral anywhere.

  What IS proved here (axiom-clean, see AxiomGuardDBN.lean): `integral_g_cos_ibp` and
  `integral_g_cos_eq` above.

  SCOPE.  One input to the representation theorem H_0 = ξ/8 (registry node RH.dbn_H0_eq_xi,
  assembled in DBNXi.lean), which is an identity between two entire functions and is not
  RH-equivalent.  Nothing here says anything about where the zeros of H_t lie.  Nothing here
  proves RH.  conjecture1_proved = False.
-/
import DBNGKernel

open Real MeasureTheory Set Filter Topology

namespace DBN

/-- **Module D** (design memo section 5, row D): the double integration by parts
`(z² + 1) ∫_0^∞ g cos(z·) = −g'(0) − ∫_0^∞ (g'' − g) cos(z·)`, for every complex `z`. -/
theorem integral_g_cos_ibp (z : ℂ) :
    (z ^ 2 + 1) * ∫ u in Ioi (0 : ℝ), ((g u : ℝ) : ℂ) * Complex.cos (z * u)
      = -((g' 0 : ℝ) : ℂ) - ∫ u in Ioi (0 : ℝ), ((g'' u - g u : ℝ) : ℂ) * Complex.cos (z * u) := by
  -- IBP-1: `u = g`, `v = −sin(z·)·z`
  have I1 : ∫ x in Ioi (0 : ℝ), ((g x : ℝ) : ℂ) * (-(Complex.cos (z * x) * z) * z)
      = 0 - 0 - ∫ x in Ioi (0 : ℝ), ((g' x : ℝ) : ℂ) * (-Complex.sin (z * x) * z) :=
    integral_Ioi_mul_deriv_eq_deriv_mul
      (u := fun u ↦ ((g u : ℝ) : ℂ)) (u' := fun u ↦ ((g' u : ℝ) : ℂ))
      (v := fun x : ℝ ↦ -Complex.sin (z * x) * z)
      (v' := fun x : ℝ ↦ -(Complex.cos (z * x) * z) * z)
      (fun x _ ↦ hasDerivAt_ofReal_g x) (fun x _ ↦ hasDerivAt_neg_sin_mul_ofReal_mul z x)
      (integrableOn_ofReal_g_mul_cos_deriv2 z) (integrableOn_ofReal_g'_mul_cos_deriv z)
      (tendsto_ofReal_g_mul_cos_deriv_nhdsGT z) (tendsto_ofReal_g_mul_cos_deriv_atTop z)
  -- IBP-2: `u = g'`, `v = cos(z·)`
  have I2 : ∫ x in Ioi (0 : ℝ), ((g' x : ℝ) : ℂ) * (-Complex.sin (z * x) * z)
      = 0 - ((g' 0 : ℝ) : ℂ) - ∫ x in Ioi (0 : ℝ), ((g'' x : ℝ) : ℂ) * Complex.cos (z * x) :=
    integral_Ioi_mul_deriv_eq_deriv_mul
      (u := fun u ↦ ((g' u : ℝ) : ℂ)) (u' := fun u ↦ ((g'' u : ℝ) : ℂ))
      (v := fun x : ℝ ↦ Complex.cos (z * x)) (v' := fun x : ℝ ↦ -Complex.sin (z * x) * z)
      (fun x _ ↦ hasDerivAt_ofReal_g' x) (fun x _ ↦ hasDerivAt_cos_mul_ofReal z x)
      (integrableOn_ofReal_g'_mul_cos_deriv z) (integrableOn_ofReal_g''_mul_cos_pi z)
      (tendsto_ofReal_g'_mul_cos_nhdsGT z) (tendsto_ofReal_g'_mul_cos_atTop z)
  have hL : ∫ x in Ioi (0 : ℝ), ((g x : ℝ) : ℂ) * (-(Complex.cos (z * x) * z) * z)
      = -z ^ 2 * ∫ u in Ioi (0 : ℝ), ((g u : ℝ) : ℂ) * Complex.cos (z * u) := by
    rw [← integral_const_mul]
    congr 1
    funext x
    ring
  have hsub : ∫ u in Ioi (0 : ℝ), ((g'' u - g u : ℝ) : ℂ) * Complex.cos (z * u)
      = (∫ u in Ioi (0 : ℝ), ((g'' u : ℝ) : ℂ) * Complex.cos (z * u))
        - ∫ u in Ioi (0 : ℝ), ((g u : ℝ) : ℂ) * Complex.cos (z * u) := by
    rw [← integral_sub (integrableOn_g''_mul_cos z) (integrableOn_g_mul_cos z)]
    congr 1
    funext u
    push_cast
    ring
  rw [hL] at I1
  rw [hsub]
  linear_combination -I1 + I2

/-- The E-ready form of module D: `(z² + 1) ∫_0^∞ g(u) cos(zu) du = 1/2 − 8 H_0(z)` for every
complex `z` (module C supplies `g'(0) = −1/2` and `∫_0^∞ (g'' − g) cos(z·) = 8 H_0(z)`). -/
theorem integral_g_cos_eq (z : ℂ) :
    (z ^ 2 + 1) * ∫ u in Ioi (0 : ℝ), ((g u : ℝ) : ℂ) * Complex.cos (z * u)
      = 1 / 2 - 8 * H 0 z := by
  rw [integral_g_cos_ibp, integral_g''_sub_g_mul_cos, g'_zero]
  push_cast
  ring

end DBN
