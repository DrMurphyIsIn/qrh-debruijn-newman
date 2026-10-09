/-
  DBNHurwitz -- Hurwitz's theorem on zeros of locally uniform limits, in the maximum-modulus
  form (Route C / C3, obligation L2e of telperion/docs/DESIGN_RH_dbn_debruijn_real_zeros_2026-09-22.md
  section 2.4 "Closure").

  Mathlib at the pinned rev has no Hurwitz theorem, no Rouche and no argument principle (memo
  section 3.1, "Absent").  None of them is needed: the closure step only asks that a zero of the
  limit `f` inside an open set `U` on which every approximant is zero-free cannot exist, and that
  follows from the maximum principle applied to `1 / F i` on a small disk:

    * `f` is entire and not identically zero, so its zero `w` is isolated (identity theorem);
    * pick a closed disk around `w`, inside `U`, whose boundary circle avoids the zeros of `f`,
      so `‖f‖ ≥ m > 0` there (compactness of the circle);
    * for `i` far along the filter, `‖F i - f‖ < m/2` on the disk, so `‖F i‖ > m/2` on the circle,
      and `F i` is zero-free on the disk (it lies in `U`); the maximum principle for
      `1 / F i` (`Complex.norm_le_of_forall_mem_frontier_norm_le`) gives `‖F i w‖ ≥ m/2`;
    * but `‖F i w‖ = ‖F i w - f w‖ < m/2`.  Contradiction.

  This is pure complex analysis: it mentions neither `Φ` nor `H_t` and imports only Mathlib.
  The consumer is the heat-flow closure step (`DBNHeatApprox.lean`), where `F N = G t N` are the
  de Bruijn approximants and `f = H t`.

  SCOPE.  Nothing here proves RH, de Bruijn's theorem, or anything about the zeros of `H_t`.
  conjecture1_proved = False.
-/
import Mathlib

open Complex Metric Filter Topology Set

namespace DBN

/-- **Hurwitz's theorem, zero-free form (maximum-modulus proof).**  Let `F i → f` locally
uniformly on an open set `U` along a nontrivial filter `p`, where eventually each `F i` is
complex-differentiable on `U` and has no zero in `U`.  If `f` is entire and not identically zero,
then `f` has no zero in `U`. -/
theorem hurwitz_ne_zero {ι : Type*} {p : Filter ι} [p.NeBot] {F : ι → ℂ → ℂ} {f : ℂ → ℂ}
    {U : Set ℂ} (hU : IsOpen U)
    (hF : ∀ᶠ i in p, DifferentiableOn ℂ (F i) U ∧ ∀ z ∈ U, F i z ≠ 0)
    (hf : Differentiable ℂ f) (hconv : TendstoLocallyUniformlyOn F f p U)
    (hf0 : ∃ z, f z ≠ 0) {w : ℂ} (hw : w ∈ U) : f w ≠ 0 := by
  intro hfw
  -- Step 1: the zero `w` of the entire, not identically zero, function `f` is isolated.
  have hiso : ∀ᶠ z in 𝓝[≠] w, f z ≠ 0 := by
    rcases (hf.analyticAt w).eventually_eq_zero_or_eventually_ne_zero with h | h
    · exfalso
      obtain ⟨z₀, hz₀⟩ := hf0
      have hEq := (hf.differentiableOn.analyticOnNhd isOpen_univ).eqOn_zero_of_preconnected_of_eventuallyEq_zero
        isPreconnected_univ (mem_univ w) h
      exact hz₀ (hEq (mem_univ z₀))
    · exact h
  -- Step 2: a radius `r` with `closedBall w r ⊆ U` and `f ≠ 0` on the circle `sphere w r`.
  obtain ⟨r₀, hr₀, hr₀U⟩ := Metric.isOpen_iff.mp hU w hw
  obtain ⟨r₁, hr₁, hr₁f⟩ := Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp hiso)
  set r : ℝ := min r₀ r₁ / 2 with hr_def
  have hr : 0 < r := by positivity
  have hrr₀ : r < r₀ := by
    have := min_le_left r₀ r₁
    rw [hr_def]; linarith
  have hrr₁ : r < r₁ := by
    have := min_le_right r₀ r₁
    rw [hr_def]; linarith
  have hball : closedBall w r ⊆ U := (closedBall_subset_ball hrr₀).trans hr₀U
  have hsph : ∀ z ∈ sphere w r, f z ≠ 0 := by
    intro z hz
    have hd : dist z w = r := mem_sphere.mp hz
    refine hr₁f (by rw [hd]; exact hrr₁) ?_
    intro hzw
    rw [hzw, dist_self] at hd
    exact hr.ne' hd.symm
  -- Step 3: `‖f‖` attains a positive minimum `m` on the circle.
  obtain ⟨z₁, hz₁, hmin⟩ := (isCompact_sphere w r).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr hr.le) (continuous_norm.comp hf.continuous).continuousOn
  set m : ℝ := ‖f z₁‖ with hm_def
  have hm : 0 < m := norm_pos_iff.mpr (hsph z₁ hz₁)
  -- Step 4: uniform convergence on the closed disk; pick a good index `i`.
  have hunif : TendstoUniformlyOn F f p (closedBall w r) :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).mp hconv _ hball (isCompact_closedBall w r)
  rw [Metric.tendstoUniformlyOn_iff] at hunif
  obtain ⟨i, hi_close, hi_d, hi_ne⟩ := ((hunif (m / 2) (half_pos hm)).and hF).exists
  -- Step 5: on the circle `‖F i‖ > m/2`, so `‖(F i)⁻¹‖ ≤ 2/m`.
  have hbound : ∀ z ∈ frontier (ball w r), ‖(fun z ↦ (F i z)⁻¹) z‖ ≤ 2 / m := by
    intro z hz
    rw [frontier_ball w hr.ne'] at hz
    have h1 : m ≤ ‖f z‖ := hmin hz
    have h2 : dist (f z) (F i z) < m / 2 := hi_close z (sphere_subset_closedBall hz)
    rw [dist_eq_norm] at h2
    have h3 : m / 2 < ‖F i z‖ := by
      have := norm_sub_norm_le (f z) (F i z)
      linarith
    show ‖(F i z)⁻¹‖ ≤ 2 / m
    rw [norm_inv]
    have h4 : (0 : ℝ) < m / 2 := half_pos hm
    calc ‖F i z‖⁻¹ ≤ (m / 2)⁻¹ := inv_anti₀ h4 h3.le
      _ = 2 / m := by rw [inv_div]
  -- Step 6: maximum principle for `(F i)⁻¹` on the disk gives `‖(F i w)⁻¹‖ ≤ 2/m`.
  have hdiff : DiffContOnCl ℂ (fun z ↦ (F i z)⁻¹) (ball w r) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball w hr.ne']
    exact (hi_d.mono hball).inv fun z hz ↦ hi_ne z (hball hz)
  have hw_le : ‖(fun z ↦ (F i z)⁻¹) w‖ ≤ 2 / m :=
    Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hdiff hbound
      (by rw [closure_ball w hr.ne']; exact mem_closedBall_self hr.le)
  -- Step 7: but `‖F i w‖ = ‖F i w - f w‖ < m/2`, so `‖(F i w)⁻¹‖ > 2/m`.
  have hw_close : dist (f w) (F i w) < m / 2 := hi_close w (mem_closedBall_self hr.le)
  rw [hfw, dist_comm, dist_zero_right] at hw_close
  have hFw : 0 < ‖F i w‖ := norm_pos_iff.mpr (hi_ne w hw)
  have : 2 / m < ‖(F i w)⁻¹‖ := by
    rw [norm_inv]
    calc 2 / m = (m / 2)⁻¹ := by rw [inv_div]
      _ < ‖F i w‖⁻¹ := inv_strictAnti₀ hFw hw_close
  exact absurd hw_le (not_le.mpr this)

/-- **Hurwitz's theorem for entire approximants.**  Locally uniform convergence on all of `ℂ`
of entire functions `F i`, eventually zero-free on the open set `U`, to an entire `f` that is not
identically zero: `f` is zero-free on `U`. -/
theorem hurwitz_ne_zero_of_entire {ι : Type*} {p : Filter ι} [p.NeBot] {F : ι → ℂ → ℂ}
    {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hFd : ∀ i, Differentiable ℂ (F i))
    (hFne : ∀ᶠ i in p, ∀ z ∈ U, F i z ≠ 0) (hf : Differentiable ℂ f)
    (hconv : TendstoLocallyUniformly F f p) (hf0 : ∃ z, f z ≠ 0) {w : ℂ} (hw : w ∈ U) :
    f w ≠ 0 :=
  hurwitz_ne_zero hU (hFne.mono fun i hi ↦ ⟨(hFd i).differentiableOn, hi⟩) hf
    (hconv.tendstoLocallyUniformlyOn) hf0 hw

end DBN
