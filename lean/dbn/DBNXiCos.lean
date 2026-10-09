/-
  DBNXiCos -- Route C / C2, module B of the design memo
  telperion/docs/DESIGN_RH_dbn_H0_eq_xi_2026-09-22.md (section 2 step (3), section 5 row B).

  The change of variables `x = e^{4u}` in Riemann's symmetric integral (module A,
  `completedRiemannZeta₀_eq_integral_psi`), evaluated at `s = 1/2 + iz/2`:

    completedRiemannZeta₀ (1/2 + iz/2) = 8 ∫_0^∞ g(u) cos(zu) du        for EVERY z ∈ ℂ,

  where `g(u) = e^{u} ψ(e^{4u})` is module C's kernel `DBN.g`.  Module C defines `g` in the closed
  form `e^{u} (θ₀(u) − 1)/2`; `g_eq_exp_mul_psi` identifies the two, so `g` is declared exactly
  once on the island.

  What IS proved here (axiom-clean, see AxiomGuardDBN.lean):
    * `g_eq_thetaMoment` (definitional) and `g_eq_exp_mul_psi : g u = e^{u} ψ(e^{4u})`;
    * the substitution `u ↦ e^{4u}` maps `(0, ∞)` bijectively onto `(1, ∞)` and, for ANY
      `G : ℝ → E` (no integrability hypothesis), `∫_{(1,∞)} G = ∫_{(0,∞)} 4 e^{4u} G(e^{4u}) du`
      (`integral_Ioi_one_eq_integral_exp_four_mul`, from Mathlib's one-dimensional Jacobian
      formula `integral_image_eq_integral_abs_deriv_smul`);
    * `((e^{r} : ℝ) : ℂ)^w = exp(r w)` for real `r` and complex `w` (`ofReal_exp_cpow`);
    * the pointwise integrand identity: at `x = e^{4u}` and `s = 1/2 + iz/2`,
      `4 e^{4u} ψ(x) (x^{s/2−1} + x^{(1−s)/2−1}) = 8 g(u) cos(zu)` (`xiCos_integrand`), because
      `4u + 4u(s/2 − 1) = u + izu`, `4u + 4u((1−s)/2 − 1) = u − izu`, and
      `e^{izu} + e^{−izu} = 2 cos(zu)`;
    * `completedRiemannZeta₀_half_add_eq`: the displayed formula above.

  SCOPE.  A classical change of variables (Riemann 1859; Titchmarsh, The Theory of the Riemann
  Zeta-Function, 2nd ed., section 10.1; Polymath15 arXiv:1904.12438 eq. (3)).  It is one
  input to the representation theorem H_0 = ξ/8 (registry node RH.dbn_H0_eq_xi, assembled in
  DBNXi.lean), which is an identity between two entire functions and is not RH-equivalent.
  Nothing here says anything about where the zeros of ζ, ξ or H_t lie.  Nothing here proves RH.
  conjecture1_proved = False.
-/
import DBNXiRiemann
import DBNGKernel

open Real MeasureTheory Set Filter Topology

namespace DBN

/-! ### The kernel `g` in the `ψ` vocabulary -/

/-- Module C's kernel in its defining closed form (definitional). -/
lemma g_eq_thetaMoment (u : ℝ) : g u = Real.exp u * (thetaMoment 0 u - 1) / 2 := rfl

/-- `g(u) = e^{u} ψ(e^{4u})` (module A's `ψ`, module C's `g`). -/
lemma g_eq_exp_mul_psi (u : ℝ) : g u = Real.exp u * psi (Real.exp (4 * u)) := by
  rw [g_eq_thetaMoment, psi_exp_eq_thetaMoment]
  ring

/-! ### The substitution `x = e^{4u}` -/

/-- `u ↦ e^{4u}` maps `(0, ∞)` onto `(1, ∞)`. -/
lemma image_exp_four_mul_Ioi : (fun u : ℝ ↦ Real.exp (4 * u)) '' Ioi 0 = Ioi 1 := by
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    have hu' : (0 : ℝ) < u := hu
    exact Real.one_lt_exp_iff.mpr (by linarith)
  · intro hx
    have hx' : (1 : ℝ) < x := hx
    refine ⟨Real.log x / 4, div_pos (Real.log_pos hx') (by norm_num), ?_⟩
    show Real.exp (4 * (Real.log x / 4)) = x
    rw [mul_div_cancel₀ _ (by norm_num : (4 : ℝ) ≠ 0), Real.exp_log (zero_lt_one.trans hx')]

/-- `d/du e^{4u} = 4 e^{4u}`. -/
lemma hasDerivAt_exp_four_mul (u : ℝ) :
    HasDerivAt (fun v : ℝ ↦ Real.exp (4 * v)) (4 * Real.exp (4 * u)) u := by
  have h : HasDerivAt (fun v : ℝ ↦ Real.exp (4 * v)) (Real.exp (4 * u) * 4) u := by
    simpa using ((hasDerivAt_id u).const_mul (4 : ℝ)).exp
  exact h.congr_deriv (mul_comm _ _)

/-- **Change of variables `x = e^{4u}`** on `(1, ∞)`, for ANY `G` (both sides are Bochner
integrals, so no integrability hypothesis is needed: the Jacobian formula is an identity of
integrals, integrable or not). -/
theorem integral_Ioi_one_eq_integral_exp_four_mul {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (G : ℝ → E) :
    ∫ x in Ioi (1 : ℝ), G x
      = ∫ u in Ioi (0 : ℝ), (4 * Real.exp (4 * u)) • G (Real.exp (4 * u)) := by
  have hinj : InjOn (fun u : ℝ ↦ Real.exp (4 * u)) (Ioi 0) := fun a _ b _ hab ↦ by
    have h := Real.exp_injective hab
    linarith
  rw [← image_exp_four_mul_Ioi, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun u _ ↦ (hasDerivAt_exp_four_mul u).hasDerivWithinAt) hinj G]
  refine setIntegral_congr_fun measurableSet_Ioi (fun u _ ↦ ?_)
  rw [abs_of_pos (by positivity : (0 : ℝ) < 4 * Real.exp (4 * u))]

/-! ### Complex powers of `e^{r}` and the integrand identity -/

/-- For real `r` and complex `w`: `((e^{r} : ℝ) : ℂ)^w = exp(r w)`. -/
lemma ofReal_exp_cpow (r : ℝ) (w : ℂ) :
    ((Real.exp r : ℝ) : ℂ) ^ w = Complex.exp ((r : ℂ) * w) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos r).ne'),
    ← Complex.ofReal_log (Real.exp_pos r).le, Real.log_exp]

/-- **The integrand identity** at `x = e^{4u}`, `s = 1/2 + iz/2`:
`4 e^{4u} ψ(x) (x^{s/2−1} + x^{(1−s)/2−1}) = 8 g(u) cos(zu)`. -/
theorem xiCos_integrand (z : ℂ) (u : ℝ) :
    (4 * Real.exp (4 * u)) • ((psi (Real.exp (4 * u)) : ℂ) *
      (((Real.exp (4 * u) : ℝ) : ℂ) ^ ((1 / 2 + Complex.I * z / 2) / 2 - 1)
        + ((Real.exp (4 * u) : ℝ) : ℂ) ^ ((1 - (1 / 2 + Complex.I * z / 2)) / 2 - 1)))
      = 8 * (((g u : ℝ) : ℂ) * Complex.cos (z * u)) := by
  rw [Complex.real_smul, ofReal_exp_cpow, ofReal_exp_cpow, g_eq_exp_mul_psi]
  have e1 : Complex.exp (4 * (u : ℂ))
        * Complex.exp (4 * (u : ℂ) * ((1 / 2 + Complex.I * z / 2) / 2 - 1))
      = Complex.exp (u : ℂ) * Complex.exp (z * u * Complex.I) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    ring
  have e2 : Complex.exp (4 * (u : ℂ))
        * Complex.exp (4 * (u : ℂ) * ((1 - (1 / 2 + Complex.I * z / 2)) / 2 - 1))
      = Complex.exp (u : ℂ) * Complex.exp (-(z * u) * Complex.I) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    ring
  have hcos := Complex.two_cos (z * u)
  push_cast
  linear_combination (4 * (psi (Real.exp (4 * u)) : ℂ)) * e1
    + (4 * (psi (Real.exp (4 * u)) : ℂ)) * e2
    - (4 * (psi (Real.exp (4 * u)) : ℂ) * Complex.exp (u : ℂ)) * hcos

/-! ### Riemann's integral as a cosine transform -/

/-- **Module B** (design memo section 5, row B): for EVERY `z ∈ ℂ`,
`completedRiemannZeta₀ (1/2 + iz/2) = 8 ∫_0^∞ g(u) cos(zu) du`, with `g(u) = e^{u} ψ(e^{4u})`.
A classical identity; nothing here concerns the zeros of `ζ`.  conjecture1_proved = False. -/
theorem completedRiemannZeta₀_half_add_eq (z : ℂ) :
    completedRiemannZeta₀ (1 / 2 + Complex.I * z / 2)
      = 8 * ∫ u in Ioi (0 : ℝ), ((g u : ℝ) : ℂ) * Complex.cos (z * u) := by
  rw [completedRiemannZeta₀_eq_integral_psi, integral_Ioi_one_eq_integral_exp_four_mul,
    ← integral_const_mul]
  exact setIntegral_congr_fun measurableSet_Ioi fun u _ ↦ xiCos_integrand z u

end DBN
