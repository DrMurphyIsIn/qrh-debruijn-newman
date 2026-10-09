/-
  DBNHadamardMean -- the two analytic inputs of the Hadamard factorisation (Route C / C3,
  obligation L3 of telperion/docs/DESIGN_RH_dbn_debruijn_real_zeros_2026-09-22.md; plan
  telperion/docs/HADAMARD_PLAN_2026-09-23.md, steps L3c and L3d) that replace the classical
  minimum-modulus estimate for the canonical product by Jensen's formula IN THE MEAN.

  * `exists_exp_eq_of_ne_zero` (L3c): a zero-free entire function `g` is `exp ∘ H` for an entire
    `H` (primitive of `g'/g` via `Differentiable.isExactOn_univ`, constant adjusted by `Complex.log`).

  * `circleAverage_abs_re_le` (L3d): if `f = g · z^{2m} · P₀` with `g = exp ∘ H` zero-free,
    `P₀ 0 = 1`, `‖f z‖ ≤ A e^{B ‖z‖^p}` and `‖P₀ z‖ ≤ e^{K ‖z‖^p}`, then for every `R ≥ 1`

      circleAverage |Re H| 0 R ≤ 2 (log A + (B + K) R^p) + |Re H 0|.

    Proof.  `Re H = log ‖g‖`, and on the circle `|Im| = R`, off the finitely many zeros of `P₀`,
    `log ‖g‖ = log ‖f‖ − 2m log R − log ‖P₀‖ ≤ (log A + B R^p) + (log ‖P₀‖)⁻`.  The negative part
    of `log ‖P₀‖` is controlled in the mean by Jensen's formula for `P₀` (`P₀ 0 = 1`, all divisor
    terms non-negative): `circleAverage (log ‖P₀‖) ≥ 0`, hence
    `circleAverage (log ‖P₀‖)⁻ ≤ circleAverage log⁺ ‖P₀‖ ≤ K R^p`.  The mean value property of the
    harmonic function `Re H` and `|x| = 2 x⁺ − x` finish the estimate.  The finitely many zeros of
    `P₀` on the circle are removed by a codiscrete congruence of circle averages.

  This is where the classical proof needs a lower bound `log ‖P₀‖ ≥ −r^p` on circles avoiding the
  zeros (Cartan / Boutroux-Cartan); the mean version above is all the Borel-Caratheodory step
  (L3e) needs.  Pure Mathlib; nothing here mentions `Φ`, `H_t` or `ξ`.  Nothing here proves RH.
  conjecture1_proved = False.
-/
import Mathlib

open Real Set Filter Topology

namespace DBN

/-! ### L3c: logarithm of a zero-free entire function -/

/-- A zero-free entire function is the exponential of an entire function. -/
theorem exists_exp_eq_of_ne_zero {g : ℂ → ℂ} (hg : Differentiable ℂ g) (h0 : ∀ z, g z ≠ 0) :
    ∃ H : ℂ → ℂ, Differentiable ℂ H ∧ ∀ z, Complex.exp (H z) = g z := by
  have hu : Differentiable ℂ (fun z ↦ deriv g z / g z) := hg.deriv.div hg h0
  obtain ⟨H₀, hH₀⟩ := hu.isExactOn_univ
  have hH₀d : Differentiable ℂ H₀ := fun z ↦ (hH₀ z (mem_univ z)).differentiableAt
  set F : ℂ → ℂ := fun z ↦ g z * Complex.exp (-H₀ z) with hF_def
  have hF : ∀ z, HasDerivAt F 0 z := by
    intro z
    have h1 : HasDerivAt g (deriv g z) z := (hg z).hasDerivAt
    have h2 : HasDerivAt (fun z ↦ Complex.exp (-H₀ z))
        (Complex.exp (-H₀ z) * (-(deriv g z / g z))) z :=
      (hH₀ z (mem_univ z)).neg.cexp
    refine (h1.mul h2).congr_deriv ?_
    have hgz := h0 z
    field_simp
    ring
  have hFd : Differentiable ℂ F := fun z ↦ (hF z).differentiableAt
  have hconst : ∀ z, F z = F 0 :=
    fun z ↦ is_const_of_deriv_eq_zero hFd (fun z ↦ (hF z).deriv) z 0
  have hF0 : F 0 ≠ 0 := mul_ne_zero (h0 0) (Complex.exp_ne_zero _)
  refine ⟨fun z ↦ H₀ z + Complex.log (F 0), hH₀d.add_const _, fun z ↦ ?_⟩
  rw [Complex.exp_add, Complex.exp_log hF0, ← hconst z]
  simp only [hF_def]
  rw [← mul_assoc, mul_comm (Complex.exp (H₀ z)), mul_assoc, ← Complex.exp_add, add_neg_cancel,
    Complex.exp_zero, mul_one]

/-! ### L3d: the mean estimate -/

/-- `|x| = 2 max x 0 − x`. -/
lemma abs_eq_two_mul_max_sub (x : ℝ) : |x| = 2 * max x 0 - x := by
  rcases le_total x 0 with h | h
  · rw [abs_of_nonpos h, max_eq_right h]; ring
  · rw [abs_of_nonneg h, max_eq_left h]; ring

/-- `log⁺ (exp t) = t` for `t ≥ 0`. -/
lemma posLog_exp_of_nonneg {t : ℝ} (ht : 0 ≤ t) : Real.posLog (Real.exp t) = t := by
  rw [Real.posLog_eq_log (by rw [abs_of_pos (Real.exp_pos t)]; exact Real.one_le_exp ht),
    Real.log_exp]

/-- Mean value property for the real part of an entire function. -/
lemma circleAverage_re_eq {H : ℂ → ℂ} (hH : Differentiable ℂ H) (R : ℝ) :
    circleAverage (fun z ↦ (H z).re) 0 R = (H 0).re :=
  InnerProductSpace.HarmonicOnNhd.circleAverage_eq
    (fun x _ ↦ (hH.analyticAt x).harmonicAt_re)

/-- Jensen in the mean: for `P₀` entire with `P₀ 0 = 1`, `circleAverage (log ‖P₀‖) 0 R ≥ 0`. -/
lemma circleAverage_log_norm_nonneg {P₀ : ℂ → ℂ} (hP₀ : Differentiable ℂ P₀) (hP₀0 : P₀ 0 = 1)
    {R : ℝ} (hR : 0 < R) :
    0 ≤ circleAverage (fun z ↦ Real.log ‖P₀ z‖) 0 R := by
  have hana : AnalyticOnNhd ℂ P₀ (Metric.closedBall 0 |R|) := fun x _ ↦ hP₀.analyticAt x
  have hne : P₀ 0 ≠ 0 := by rw [hP₀0]; exact one_ne_zero
  rw [hana.circleAverage_log_norm hR.ne' hne, hP₀0, norm_one, Real.log_one, add_zero]
  set D := MeromorphicOn.divisor P₀ (Metric.closedBall 0 |R|) with hD
  have hDnn : 0 ≤ D := MeromorphicOn.AnalyticOnNhd.divisor_nonneg hana
  have hD0 : D 0 = 0 := by
    rw [hD, MeromorphicOn.AnalyticOnNhd.divisor_apply hana (by simp)]
    rw [(hana 0 (by simp)).analyticOrderAt_eq_zero.mpr hne]
    simp
  refine finsum_nonneg fun u ↦ ?_
  by_cases hu : D u = 0
  · rw [hu]; simp
  · have hu0 : u ≠ 0 := by rintro rfl; exact hu hD0
    have hmem : u ∈ Metric.closedBall (0 : ℂ) |R| := D.supportWithinDomain hu
    have hDu : (0 : ℝ) ≤ (D u : ℝ) := by exact_mod_cast hDnn u
    refine mul_nonneg hDu (Real.log_nonneg ?_)
    rw [zero_sub, norm_neg, ← div_eq_mul_inv]
    rw [Metric.mem_closedBall, dist_zero_right, abs_of_pos hR] at hmem
    exact (one_le_div (norm_pos_iff.mpr hu0)).mpr hmem

/-- The positive part of `log ‖P₀‖` is bounded in the mean by the growth bound. -/
lemma circleAverage_posLog_norm_le {P₀ : ℂ → ℂ} (hP₀ : Differentiable ℂ P₀)
    {K p : ℝ} (hK : 0 ≤ K) (_hp : 0 ≤ p)
    (hPgrowth : ∀ z, ‖P₀ z‖ ≤ Real.exp (K * ‖z‖ ^ p)) {R : ℝ} (hR : 0 < R) :
    circleAverage (fun z ↦ Real.posLog ‖P₀ z‖) 0 R ≤ K * R ^ p := by
  have hmero : MeromorphicOn P₀ (Metric.sphere (0 : ℂ) |R|) :=
    AnalyticOnNhd.meromorphicOn (fun x _ ↦ hP₀.analyticAt x)
  refine circleAverage_mono_on_of_le_circle hmero.circleIntegrable_posLog_norm fun z hz ↦ ?_
  rw [Metric.mem_sphere, dist_zero_right, abs_of_pos hR] at hz
  calc Real.posLog ‖P₀ z‖ ≤ Real.posLog (Real.exp (K * ‖z‖ ^ p)) :=
        Real.posLog_le_posLog (norm_nonneg _) (hPgrowth z)
    _ = K * ‖z‖ ^ p := posLog_exp_of_nonneg (mul_nonneg hK (Real.rpow_nonneg (norm_nonneg _) _))
    _ = K * R ^ p := by rw [hz]

/-- **The mean estimate (L3d).** -/
theorem circleAverage_abs_re_le {f P₀ g H : ℂ → ℂ} {m : ℕ}
    (_hf : Differentiable ℂ f) (hP₀ : Differentiable ℂ P₀) (hP₀0 : P₀ 0 = 1)
    (hH : Differentiable ℂ H) (hgH : ∀ z, Complex.exp (H z) = g z)
    (hfg : ∀ z, f z = g z * (z ^ (2 * m) * P₀ z))
    {A B K p : ℝ} (hA : 1 ≤ A) (hB : 0 ≤ B) (hK : 0 ≤ K) (hp : 0 ≤ p)
    (hfgrowth : ∀ z, ‖f z‖ ≤ A * Real.exp (B * ‖z‖ ^ p))
    (hPgrowth : ∀ z, ‖P₀ z‖ ≤ Real.exp (K * ‖z‖ ^ p))
    {R : ℝ} (hR : 1 ≤ R) :
    circleAverage (fun z ↦ |(H z).re|) 0 R ≤ 2 * (Real.log A + (B + K) * R ^ p) + |(H 0).re| := by
  have hRpos : 0 < R := by linarith
  have hRabs : |R| = R := abs_of_pos hRpos
  set u : ℂ → ℝ := fun z ↦ (H z).re with hu_def
  have hu_cont : Continuous u := Complex.continuous_re.comp hH.continuous
  have hu_int : CircleIntegrable u 0 R := hu_cont.continuousOn.circleIntegrable'
  have hmax_int : CircleIntegrable (fun z ↦ max (u z) 0) 0 R :=
    (hu_cont.max continuous_const).continuousOn.circleIntegrable'
  -- the constant part of the bound
  set L : ℝ := Real.log A + B * R ^ p with hL_def
  have hL : 0 ≤ L := add_nonneg (Real.log_nonneg hA)
    (mul_nonneg hB (Real.rpow_nonneg hRpos.le _))
  -- the comparison function
  set ψ : ℂ → ℝ := fun z ↦ L + Real.posLog ‖P₀ z‖ - Real.log ‖P₀ z‖ with hψ_def
  have hmero : MeromorphicOn P₀ (Metric.sphere (0 : ℂ) |R|) :=
    AnalyticOnNhd.meromorphicOn (fun x _ ↦ hP₀.analyticAt x)
  have hψ_int : CircleIntegrable ψ 0 R := by
    have h1 : CircleIntegrable (fun z ↦ L + Real.posLog ‖P₀ z‖) 0 R :=
      (circleIntegrable_const L 0 R).add hmero.circleIntegrable_posLog_norm
    exact h1.sub hmero.circleIntegrable_log_norm
  have hψ_nonneg : ∀ z, 0 ≤ ψ z := by
    intro z
    simp only [hψ_def]
    have : Real.log ‖P₀ z‖ ≤ Real.posLog ‖P₀ z‖ := by
      rw [Real.posLog_apply]; exact le_max_right _ _
    linarith
  -- pointwise bound off the zeros of `P₀` on the circle
  have hpt : ∀ z ∈ Metric.sphere (0 : ℂ) |R|, P₀ z ≠ 0 → max (u z) 0 ≤ ψ z := by
    intro z hz hPz
    rw [Metric.mem_sphere, dist_zero_right, hRabs] at hz
    refine max_le ?_ (hψ_nonneg z)
    have hz0 : z ≠ 0 := by
      intro h; rw [h, norm_zero] at hz; linarith
    have hg : g z ≠ 0 := by rw [← hgH z]; exact Complex.exp_ne_zero _
    have hu_eq : u z = Real.log ‖g z‖ := by
      simp only [hu_def]
      rw [← hgH z, Complex.norm_exp, Real.log_exp]
    have hnorm : ‖f z‖ = ‖g z‖ * (‖z‖ ^ (2 * m) * ‖P₀ z‖) := by
      rw [hfg z, norm_mul, norm_mul, norm_pow]
    have hgpos : 0 < ‖g z‖ := norm_pos_iff.mpr hg
    have hPpos : 0 < ‖P₀ z‖ := norm_pos_iff.mpr hPz
    have hzpos : 0 < ‖z‖ ^ (2 * m) := pow_pos (norm_pos_iff.mpr hz0) _
    have hlogf : Real.log ‖f z‖ = Real.log ‖g z‖ + (2 * m) * Real.log ‖z‖ + Real.log ‖P₀ z‖ := by
      rw [hnorm, Real.log_mul hgpos.ne' (mul_pos hzpos hPpos).ne', Real.log_mul hzpos.ne' hPpos.ne',
        Real.log_pow]
      push_cast
      ring
    have hlogz : 0 ≤ (2 * m : ℝ) * Real.log ‖z‖ :=
      mul_nonneg (by positivity) (Real.log_nonneg (by rw [hz]; exact hR))
    have hlogf_le : Real.log ‖f z‖ ≤ L := by
      calc Real.log ‖f z‖ ≤ Real.log (A * Real.exp (B * ‖z‖ ^ p)) :=
            Real.log_le_log (by rw [hnorm]; positivity) (hfgrowth z)
        _ = Real.log A + B * ‖z‖ ^ p := by
            rw [Real.log_mul (by linarith) (Real.exp_pos _).ne', Real.log_exp]
        _ = L := by rw [hL_def, hz]
    have hpos : 0 ≤ Real.posLog ‖P₀ z‖ := Real.posLog_nonneg
    simp only [hψ_def]
    rw [hu_eq]
    linarith
  -- remove the zeros of `P₀` on the circle by a codiscrete congruence
  set φ : ℂ → ℝ := fun z ↦ if P₀ z = 0 then ψ z else max (u z) 0 with hφ_def
  have hcod : (fun z ↦ max (u z) 0) =ᶠ[codiscreteWithin (Metric.sphere (0 : ℂ) |R|)] φ := by
    have hmem : P₀ ⁻¹' {0}ᶜ ∈ codiscreteWithin (Metric.sphere (0 : ℂ) |R|) :=
      Filter.codiscreteWithin_mono (subset_univ _)
        (AnalyticOnNhd.preimage_zero_mem_codiscrete (fun x _ ↦ hP₀.analyticAt x)
          (x := 0) (by rw [hP₀0]; exact one_ne_zero))
    filter_upwards [hmem] with z hz
    simp only [mem_preimage, mem_compl_iff, mem_singleton_iff] at hz
    simp [hφ_def, hz]
  have hφ_int : CircleIntegrable φ 0 R := hmax_int.congr_codiscreteWithin hcod
  have hφ_le : ∀ z ∈ Metric.sphere (0 : ℂ) |R|, φ z ≤ ψ z := by
    intro z hz
    simp only [hφ_def]
    split_ifs with h
    · exact le_rfl
    · exact hpt z hz h
  -- the mean of the positive part
  have hmean_pos : circleAverage (fun z ↦ max (u z) 0) 0 R ≤ L + K * R ^ p := by
    rw [circleAverage_congr_codiscreteWithin hcod hRpos.ne']
    refine (circleAverage_mono hφ_int hψ_int hφ_le).trans ?_
    have h1 : CircleIntegrable (fun z ↦ L + Real.posLog ‖P₀ z‖) 0 R :=
      (circleIntegrable_const L 0 R).add hmero.circleIntegrable_posLog_norm
    have hψ_eq : ψ = (fun z ↦ L + Real.posLog ‖P₀ z‖) - fun z ↦ Real.log ‖P₀ z‖ := by
      funext z; simp [hψ_def]
    rw [hψ_eq, circleAverage_sub h1 hmero.circleIntegrable_log_norm]
    have h2 : (fun z ↦ L + Real.posLog ‖P₀ z‖) = (fun _ ↦ L) + fun z ↦ Real.posLog ‖P₀ z‖ := by
      funext z; simp
    rw [h2, circleAverage_add (circleIntegrable_const L 0 R) hmero.circleIntegrable_posLog_norm,
      circleAverage_const]
    have h3 := circleAverage_posLog_norm_le hP₀ hK hp hPgrowth hRpos
    have h4 := circleAverage_log_norm_nonneg hP₀ hP₀0 hRpos
    linarith
  -- assemble via `|x| = 2 max x 0 − x` and the mean value property
  have habs : (fun z ↦ |(H z).re|) = (2 : ℝ) • (fun z ↦ max (u z) 0) - u := by
    funext z
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hu_def]
    exact abs_eq_two_mul_max_sub _
  rw [habs, circleAverage_sub (hmax_int.const_smul (a := (2 : ℝ))) hu_int, circleAverage_smul,
    smul_eq_mul, hu_def, circleAverage_re_eq hH]
  have h5 : -(H 0).re ≤ |(H 0).re| := neg_le_abs _
  have h6 : L + K * R ^ p = Real.log A + (B + K) * R ^ p := by rw [hL_def]; ring
  linarith

end DBN

#print axioms DBN.exists_exp_eq_of_ne_zero
#print axioms DBN.circleAverage_abs_re_le
