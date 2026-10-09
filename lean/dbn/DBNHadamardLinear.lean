/-
  DBNHadamardLinear -- obligation L3e of telperion/docs/HADAMARD_PLAN_2026-09-23.md: an entire
  function `H` whose real part has circle averages `circleAverage |Re H| 0 R ≤ K R^p + K'` with
  `p < 2` is a polynomial of degree at most one.

  This is the "Borel-Caratheodory in the mean" step of the Hadamard factorisation: the classical
  statement needs a POINTWISE bound `Re H ≤ M(R)` on the circle, which the canonical product
  cannot provide near its zeros; instead the Poisson formula for the harmonic function `Re H`
  turns a bound on the circle AVERAGE of `|Re H|` on `|z| = R` into a pointwise bound on
  `|z| < R/2` (the Poisson kernel is at most `3` there).  Then Mathlib's Borel-Caratheodory bounds
  `‖H‖` on `|z| ≤ R/4`, two Cauchy estimates bound `‖H''‖` on `|z| ≤ R/16` by `O(R^{p-2})`, and
  `p < 2` kills `H''`.

  Pure Mathlib; the file mentions nothing about `Φ`, `H_t`, zeta or the de Bruijn flow.
  Nothing here proves RH.  conjecture1_proved = False.
-/
import Mathlib

open Real Metric Filter Topology

namespace DBN

/-! ### Step 1: the Poisson kernel on `|z| = R` is at most `3` for `|w| < R/2` -/

/-- Upper bound for the Poisson kernel of the disc of radius `R` about `0`. -/
lemma poissonKernel_zero_le {w z : ℂ} {R : ℝ} (hz : z ∈ sphere (0 : ℂ) R) (hw : w ∈ ball (0 : ℂ) R) :
    poissonKernel 0 w z ≤ (R + ‖w‖) / (R - ‖w‖) := by
  have h := re_herglotzRieszKernel_le hz hw
  rw [poissonKernel_eq_re_herglotzRieszKernel, Function.comp_apply, herglotzRieszKernel_def]
  simpa using h

/-- The Poisson kernel is nonnegative on the circle. -/
lemma poissonKernel_zero_nonneg {w z : ℂ} {R : ℝ} (hz : z ∈ sphere (0 : ℂ) R)
    (hw : w ∈ ball (0 : ℂ) R) : 0 ≤ poissonKernel 0 w z := by
  have h := le_re_herglotzRieszKernel hz hw
  rw [poissonKernel_eq_re_herglotzRieszKernel, Function.comp_apply, herglotzRieszKernel_def]
  have hR : 0 < R := pos_of_mem_ball hw
  have hwR : ‖w‖ < R := mem_ball_zero_iff.mp hw
  refine le_trans ?_ (by simpa using h)
  have := norm_nonneg w
  exact div_nonneg (by linarith) (by linarith)

/-- For `‖w‖ < R/2` the Poisson kernel on `|z| = R` is at most `3`. -/
lemma poissonKernel_zero_le_three {w z : ℂ} {R : ℝ} (hz : z ∈ sphere (0 : ℂ) R)
    (hw : ‖w‖ < R / 2) (hR : 0 < R) : poissonKernel 0 w z ≤ 3 := by
  have hwb : w ∈ ball (0 : ℂ) R := mem_ball_zero_iff.mpr (by linarith)
  refine (poissonKernel_zero_le hz hwb).trans ?_
  rw [div_le_iff₀ (by linarith)]
  linarith

/-- The Poisson kernel `poissonKernel 0 w` is continuous on the circle `|z| = R` when `‖w‖ < R`. -/
lemma continuousOn_poissonKernel_zero {w : ℂ} {R : ℝ} (hw : ‖w‖ < R) :
    ContinuousOn (poissonKernel 0 w) (sphere (0 : ℂ) |R|) := by
  intro z hz
  apply ContinuousAt.continuousWithinAt
  have hzR : ‖z‖ = |R| := by simpa using hz
  have hne : z - 0 - (w - 0) ≠ 0 := by
    intro h
    have : z = w := by simpa [sub_eq_zero] using h
    rw [this] at hzR
    have := le_abs_self R
    linarith
  unfold poissonKernel
  exact ContinuousAt.div (by fun_prop) (by fun_prop) (pow_ne_zero _ (norm_ne_zero_iff.mpr hne))

/-- **Poisson bound in the mean.**  For entire `H`, `R > 0` and `‖w‖ < R/2`,
`|Re H w| ≤ 3 · circleAverage |Re H| 0 R`. -/
lemma abs_re_le_three_mul_circleAverage {H : ℂ → ℂ} (hH : Differentiable ℂ H) {R : ℝ}
    (hR : 0 < R) {w : ℂ} (hw : ‖w‖ < R / 2) :
    |(H w).re| ≤ 3 * circleAverage (fun z ↦ |(H z).re|) 0 R := by
  set u : ℂ → ℝ := fun z ↦ (H z).re with hu
  have hharm : InnerProductSpace.HarmonicOnNhd u (closedBall (0 : ℂ) R) :=
    fun x _ ↦ (hH.analyticAt x).harmonicAt_re
  have hwb : w ∈ ball (0 : ℂ) R := mem_ball_zero_iff.mpr (by linarith)
  have hP := hharm.circleAverage_poissonKernel_smul hwb
  have hwR : ‖w‖ < R := by linarith
  have habsR : |R| = R := abs_of_pos hR
  have hcont_u : ContinuousOn u (sphere (0 : ℂ) |R|) :=
    (Complex.continuous_re.comp hH.continuous).continuousOn
  have h1 : CircleIntegrable |poissonKernel 0 w • u| 0 R := by
    apply ContinuousOn.circleIntegrable'
    exact ((continuousOn_poissonKernel_zero hwR).smul hcont_u).abs
  have h2 : CircleIntegrable (fun z ↦ (3 : ℝ) * |u z|) 0 R := by
    apply ContinuousOn.circleIntegrable'
    exact continuousOn_const.mul hcont_u.abs
  calc |u w| = |circleAverage (poissonKernel 0 w • u) 0 R| := by rw [hP]
    _ ≤ circleAverage |poissonKernel 0 w • u| 0 R := abs_circleAverage_le_circleAverage_abs
    _ ≤ circleAverage (fun z ↦ (3 : ℝ) * |u z|) 0 R := by
        refine circleAverage_mono h1 h2 fun z hz ↦ ?_
        rw [habsR] at hz
        have hk0 := poissonKernel_zero_nonneg hz hwb
        show |poissonKernel 0 w z * u z| ≤ 3 * |u z|
        rw [abs_mul, abs_of_nonneg hk0]
        exact mul_le_mul_of_nonneg_right (poissonKernel_zero_le_three hz hw hR) (abs_nonneg _)
    _ = 3 * circleAverage (fun z ↦ |u z|) 0 R := by
        rw [show (fun z ↦ (3 : ℝ) * |u z|) = fun z ↦ (3 : ℝ) • |u z| from rfl,
          circleAverage_fun_smul, smul_eq_mul]

/-! ### Step 2: Borel-Caratheodory on `|z| ≤ r/2` -/

/-- Borel-Caratheodory specialised: `Re H ≤ M` on `‖w‖ < r` gives `‖H z‖ ≤ 2M + 3‖H 0‖` on
`‖z‖ ≤ r/2`. -/
lemma norm_le_of_re_le {H : ℂ → ℂ} (hH : Differentiable ℂ H) {r M : ℝ} (hr : 0 < r) (hM : 0 < M)
    (hre : ∀ w : ℂ, ‖w‖ < r → (H w).re ≤ M) {z : ℂ} (hz : ‖z‖ ≤ r / 2) :
    ‖H z‖ ≤ 2 * M + 3 * ‖H 0‖ := by
  have hzb : z ∈ ball (0 : ℂ) r := mem_ball_zero_iff.mpr (by linarith)
  have hmaps : Set.MapsTo H (ball 0 r) {z | z.re ≤ M} := fun w hw ↦ hre w (mem_ball_zero_iff.mp hw)
  have hbc := Complex.borelCaratheodory hM hH.differentiableOn hmaps hr hzb
  have hden : r / 2 ≤ r - ‖z‖ := by linarith
  have hden' : 0 < r - ‖z‖ := by linarith
  have hz0 : 0 ≤ ‖z‖ := norm_nonneg _
  have e1 : 2 * M * ‖z‖ / (r - ‖z‖) ≤ 2 * M := by
    rw [div_le_iff₀ hden']
    nlinarith
  have e2 : ‖H 0‖ * (r + ‖z‖) / (r - ‖z‖) ≤ 3 * ‖H 0‖ := by
    rw [div_le_iff₀ hden']
    nlinarith [norm_nonneg (H 0)]
  linarith

/-! ### Step 3: two Cauchy estimates -/

/-- Cauchy estimate for an entire function on a sphere. -/
lemma norm_deriv_le_of_forall_sphere {G : ℂ → ℂ} (hG : Differentiable ℂ G) {c : ℂ} {r C : ℝ}
    (hr : 0 < r) (hC : ∀ z ∈ sphere c r, ‖G z‖ ≤ C) : ‖deriv G c‖ ≤ C / r :=
  Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr hG.diffContOnCl hC

/-- Two Cauchy estimates: a bound `M₁` for `‖H‖` on `‖z‖ ≤ R/4` gives
`‖H'' w‖ ≤ M₁ / (R/16) / (R/16)` for `‖w‖ ≤ R/16`. -/
lemma norm_deriv_deriv_le {H : ℂ → ℂ} (hH : Differentiable ℂ H) {R M₁ : ℝ} (hR : 0 < R)
    (hM₁ : ∀ z : ℂ, ‖z‖ ≤ R / 4 → ‖H z‖ ≤ M₁) {w : ℂ} (hw : ‖w‖ ≤ R / 16) :
    ‖deriv (deriv H) w‖ ≤ M₁ / (R / 16) / (R / 16) := by
  have hr : 0 < R / 16 := by positivity
  apply norm_deriv_le_of_forall_sphere hH.deriv hr
  intro z hz
  rw [mem_sphere_iff_norm] at hz
  have hzn : ‖z‖ ≤ R / 8 := by
    calc ‖z‖ = ‖(z - w) + w‖ := by ring_nf
      _ ≤ ‖z - w‖ + ‖w‖ := norm_add_le _ _
      _ ≤ R / 8 := by rw [hz]; linarith
  apply norm_deriv_le_of_forall_sphere hH hr
  intro ζ hζ
  rw [mem_sphere_iff_norm] at hζ
  apply hM₁
  calc ‖ζ‖ = ‖(ζ - z) + z‖ := by ring_nf
    _ ≤ ‖ζ - z‖ + ‖z‖ := norm_add_le _ _
    _ ≤ R / 4 := by rw [hζ]; linarith

/-! ### Step 4: the main theorem -/

/-- **L3e.**  An entire function whose real part satisfies
`circleAverage |Re H| 0 R ≤ K R^p + K'` for all `R ≥ 1`, with `p < 2`, is affine linear. -/
theorem eq_linear_of_circleAverage_abs_re_le {H : ℂ → ℂ} (hH : Differentiable ℂ H)
    {K K' p : ℝ} (hp : p < 2)
    (hbound : ∀ R : ℝ, 1 ≤ R → circleAverage (fun z ↦ |(H z).re|) 0 R ≤ K * R ^ p + K') :
    ∃ a b : ℂ, ∀ z, H z = a + b * z := by
  -- normalise the exponent and the constants
  set q : ℝ := max p 0 with hq
  have hq0 : 0 ≤ q := le_max_right _ _
  have hq2 : q < 2 := max_lt hp (by norm_num)
  set C₀ : ℝ := 6 * |K| + 6 * |K'| + 2 + 3 * ‖H 0‖ with hC₀
  have hC₀nn : 0 ≤ C₀ := by positivity
  -- the key bound: `‖H'' w‖ ≤ 256 C₀ R^(q-2)` for `R ≥ max 1 (16 ‖w‖)`
  have key : ∀ w : ℂ, ∀ R : ℝ, 1 ≤ R → 16 * ‖w‖ ≤ R →
      ‖deriv (deriv H) w‖ ≤ 256 * C₀ * R ^ (q - 2) := by
    intro w R hR1 hRw
    have hR : 0 < R := by linarith
    have hRp : 0 ≤ R ^ p := Real.rpow_nonneg hR.le p
    have hpq : R ^ p ≤ R ^ q := Real.rpow_le_rpow_of_exponent_le hR1 (le_max_left _ _)
    have h1q : 1 ≤ R ^ q := Real.one_le_rpow hR1 hq0
    set M : ℝ := 3 * (|K| * R ^ p + |K'|) + 1 with hM
    have hMpos : 0 < M := by positivity
    -- pointwise bound on `Re H` in `‖w‖ < R/2` from the mean bound (Poisson)
    have hre : ∀ w : ℂ, ‖w‖ < R / 2 → (H w).re ≤ M := by
      intro w hw
      calc (H w).re ≤ |(H w).re| := le_abs_self _
        _ ≤ 3 * circleAverage (fun z ↦ |(H z).re|) 0 R :=
            abs_re_le_three_mul_circleAverage hH hR hw
        _ ≤ 3 * (K * R ^ p + K') := by gcongr; exact hbound R hR1
        _ ≤ 3 * (|K| * R ^ p + |K'|) := by
            gcongr <;> exact le_abs_self _
        _ ≤ M := by rw [hM]; linarith
    -- Borel-Caratheodory: `‖H‖ ≤ M₁` on `‖z‖ ≤ R/2 ⊇ ‖z‖ ≤ R/4`
    set M₁ : ℝ := 2 * M + 3 * ‖H 0‖ with hM₁
    have hHle : ∀ z : ℂ, ‖z‖ ≤ R / 4 → ‖H z‖ ≤ M₁ :=
      fun z hz ↦ norm_le_of_re_le hH (by positivity : 0 < R / 2) hMpos hre (by linarith)
    -- two Cauchy estimates
    have hw16 : ‖w‖ ≤ R / 16 := by linarith
    have h2 := norm_deriv_deriv_le hH hR hHle hw16
    -- arithmetic: `M₁ ≤ C₀ R^q` and `M₁ / (R/16) / (R/16) = 256 M₁ / R²`
    have hM₁le : M₁ ≤ C₀ * R ^ q := by
      rw [hM₁, hM, hC₀]
      have e1 : |K| * R ^ p ≤ |K| * R ^ q := mul_le_mul_of_nonneg_left hpq (abs_nonneg _)
      have e2 : |K'| ≤ |K'| * R ^ q := le_mul_of_one_le_right (abs_nonneg _) h1q
      have e3 : ‖H 0‖ ≤ ‖H 0‖ * R ^ q := le_mul_of_one_le_right (norm_nonneg _) h1q
      have e4 : (6 * |K| + 6 * |K'| + 2 + 3 * ‖H 0‖) * R ^ q
          = 6 * (|K| * R ^ q) + 6 * (|K'| * R ^ q) + 2 * R ^ q + 3 * (‖H 0‖ * R ^ q) := by ring
      rw [e4]
      linarith
    have hRq : R ^ (q - 2) = R ^ q / R ^ 2 := by
      rw [Real.rpow_sub hR, Real.rpow_two]
    calc ‖deriv (deriv H) w‖ ≤ M₁ / (R / 16) / (R / 16) := h2
      _ = 256 * M₁ / R ^ 2 := by field_simp; ring
      _ ≤ 256 * (C₀ * R ^ q) / R ^ 2 := by gcongr
      _ = 256 * C₀ * R ^ (q - 2) := by rw [hRq]; ring
  -- `H'' = 0` everywhere: the bound tends to `0` as `R → ∞`
  have hdd : ∀ w : ℂ, deriv (deriv H) w = 0 := by
    intro w
    have hlim : Tendsto (fun R : ℝ ↦ 256 * C₀ * R ^ (q - 2)) atTop (𝓝 0) := by
      have h := (tendsto_rpow_neg_atTop (y := 2 - q) (by linarith)).const_mul (256 * C₀)
      rw [mul_zero] at h
      refine h.congr fun R ↦ ?_
      simp only [neg_sub]
    have hev : ∀ᶠ R : ℝ in atTop, ‖deriv (deriv H) w‖ ≤ 256 * C₀ * R ^ (q - 2) := by
      filter_upwards [eventually_ge_atTop (max 1 (16 * ‖w‖))] with R hR
      exact key w R (le_trans (le_max_left _ _) hR) (le_trans (le_max_right _ _) hR)
    have : ‖deriv (deriv H) w‖ ≤ 0 := ge_of_tendsto hlim hev
    exact norm_le_zero_iff.mp this
  -- `H'` is constant, hence `H` is affine
  have hH' : Differentiable ℂ (deriv H) := hH.deriv
  have hconst := is_const_of_deriv_eq_zero hH' hdd
  set b : ℂ := deriv H 0 with hb
  have hderiv : ∀ z, deriv H z = b := fun z ↦ hconst z 0
  set G : ℂ → ℂ := fun z ↦ H z - b * z with hG
  have hGdiff : Differentiable ℂ G := hH.sub (differentiable_id.const_mul b)
  have hGderiv : ∀ z, deriv G z = 0 := by
    intro z
    have h : HasDerivAt G (deriv H z - b * 1) z :=
      (hH z).hasDerivAt.sub ((hasDerivAt_id z).const_mul b)
    rw [h.deriv, hderiv z]; ring
  have hGconst := is_const_of_deriv_eq_zero hGdiff hGderiv
  refine ⟨H 0, b, fun z ↦ ?_⟩
  have := hGconst z 0
  simp only [hG, mul_zero, sub_zero] at this
  linear_combination this

end DBN

#print axioms DBN.eq_linear_of_circleAverage_abs_re_le
