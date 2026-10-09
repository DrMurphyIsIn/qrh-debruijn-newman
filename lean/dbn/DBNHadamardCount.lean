/-
  DBNHadamardCount -- Route C / C3, obligation L3a of
  telperion/docs/HADAMARD_PLAN_2026-09-23.md: zero counting from growth.

  For an entire function `f`, not identically zero, with `‖f z‖ ≤ A exp(B ‖z‖^ρ)`, the
  multiplicity-weighted sum `∑ ord_s(f) ‖s‖^(-p)` over the nonzero zeros `s` of `f` converges for
  every `p > ρ` (`summable_zero_multiplicity_rpow`).  This is the convergence-exponent half of
  Hadamard's theorem.

  Proof.  Jensen's inequality (`AnalyticOnNhd.sum_divisor_le`, Mathlib) at a centre `c` with
  `f c ≠ 0` bounds the number `n(r)` of zeros (with multiplicity) in `closedBall c r` by
  `(log A + B (‖c‖ + 2r)^ρ - log ‖f c‖) / log 2`.  Group the zeros with `‖s‖ > 1` dyadically by
  `k = ⌊log₂ ‖s‖⌋`: the group contributes at most `(2^k)^(-p) n(‖c‖ + 2^(k+1))`, which is
  dominated by a convergent geometric series since `p > ρ`.  The finitely many zeros with
  `‖s‖ ≤ 1` contribute a fixed amount.  Everything is pure Mathlib.

  Nothing here proves RH.  conjecture1_proved = False.
-/
import Mathlib

open Metric Set Filter

namespace DBN

section Count

variable {f : ℂ → ℂ}

/-- An entire function that is not identically zero has finite order at every point. -/
lemma analyticOrderAt_ne_top_of_entire (hf : Differentiable ℂ f) (hne : ∃ z, f z ≠ 0) (z : ℂ) :
    analyticOrderAt f z ≠ ⊤ := by
  intro h
  rw [AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero z (fun w ↦ hf.analyticAt w)] at h
  obtain ⟨w, hw⟩ := hne
  exact hw (by rw [h]; rfl)

/-- For an entire function that is not identically zero, the divisor on any set `U` is the
natural-number order at points of `U`. -/
lemma divisor_eq_analyticOrderNatAt (hf : Differentiable ℂ f) (hne : ∃ z, f z ≠ 0) {U : Set ℂ}
    {z : ℂ} (hz : z ∈ U) :
    MeromorphicOn.divisor f U z = (analyticOrderNatAt f z : ℤ) := by
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply (fun w _ ↦ hf.analyticAt w) hz]
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (analyticOrderAt_ne_top_of_entire hf hne z)
  rw [analyticOrderNatAt, ← hn]
  simp

/-- A zero of an entire function (not identically zero) has order at least one. -/
lemma one_le_analyticOrderNatAt (hf : Differentiable ℂ f) (hne : ∃ z, f z ≠ 0) {z : ℂ}
    (hz : f z = 0) : 1 ≤ analyticOrderNatAt f z := by
  have h1 : analyticOrderAt f z ≠ 0 := analyticOrderAt_ne_zero.mpr ⟨hf.analyticAt z, hz⟩
  have h2 := analyticOrderAt_ne_top_of_entire hf hne z
  rw [Nat.one_le_iff_ne_zero]
  intro h0
  rw [analyticOrderNatAt, ENat.toNat_eq_zero] at h0
  tauto

/-- The number of zeros of `f` in `closedBall c |r|`, counted with multiplicity. -/
noncomputable def zeroCount (f : ℂ → ℂ) (c : ℂ) (r : ℝ) : ℝ :=
  ((∑ᶠ u, MeromorphicOn.divisor f (closedBall c |r|) u : ℤ) : ℝ)

/-- The multiplicities of finitely many nonzero zeros inside `closedBall c |r|` add up to at most
the zero count. -/
lemma sum_ord_le_zeroCount (hf : Differentiable ℂ f) (hne : ∃ z, f z ≠ 0) {c : ℂ} {r : ℝ}
    (G : Finset {s : ℂ // f s = 0 ∧ s ≠ 0}) (hG : ∀ s ∈ G, (s : ℂ) ∈ closedBall c |r|) :
    ∑ s ∈ G, (analyticOrderNatAt f s : ℝ) ≤ zeroCount f c r := by
  classical
  set D := MeromorphicOn.divisor f (closedBall c |r|) with hD
  have hfin := D.finiteSupport (isCompact_closedBall c |r|)
  unfold zeroCount
  rw [← hD, finsum_eq_sum_of_support_subset (s := hfin.toFinset) _ (by simp), Int.cast_sum]
  have key : ∑ s ∈ G, (analyticOrderNatAt f s : ℝ)
      = ∑ u ∈ G.map (Function.Embedding.subtype _), ((D u : ℤ) : ℝ) := by
    rw [Finset.sum_map]
    refine Finset.sum_congr rfl fun s hs ↦ ?_
    rw [Function.Embedding.coe_subtype, hD, divisor_eq_analyticOrderNatAt hf hne (hG s hs)]
    simp
  rw [key]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro u hu
    rw [Finset.mem_map] at hu
    obtain ⟨s, hs, rfl⟩ := hu
    rw [Set.Finite.mem_toFinset, Function.mem_support, Function.Embedding.coe_subtype, hD,
      divisor_eq_analyticOrderNatAt hf hne (hG s hs)]
    have := one_le_analyticOrderNatAt hf hne s.2.1
    exact_mod_cast (by omega : analyticOrderNatAt f s ≠ 0)
  · intro u _ _
    exact_mod_cast (MeromorphicOn.AnalyticOnNhd.divisor_nonneg (fun w _ ↦ hf.analyticAt w)) u

/-- **Jensen's inequality, made explicit for the growth bound.** -/
lemma zeroCount_le (hf : Differentiable ℂ f) {c : ℂ} (hc : f c ≠ 0) {A B ρ : ℝ} (hA : 1 ≤ A)
    (hB : 0 ≤ B) (hρ : 0 < ρ) (hgrowth : ∀ z, ‖f z‖ ≤ A * Real.exp (B * ‖z‖ ^ ρ))
    {r : ℝ} (hr : 0 < r) :
    zeroCount f c r ≤ (Real.log A + B * (‖c‖ + 2 * r) ^ ρ - Real.log ‖f c‖) / Real.log 2 := by
  have hA0 : 0 < A := by linarith
  set M : ℝ := A * Real.exp (B * (‖c‖ + 2 * r) ^ ρ) with hM
  have hM1 : 1 ≤ M := one_le_mul_of_one_le_of_one_le hA (Real.one_le_exp (by positivity))
  have hR : |(2 * r)| = 2 * r := abs_of_pos (by linarith)
  have hr' : |r| = r := abs_of_pos hr
  have h := AnalyticOnNhd.sum_divisor_le (c := c) (r := r) (R := 2 * r) (M := M)
    (by rw [hr']; exact hr) (by rw [hr', hR]; linarith) hM1
    (fun z _ ↦ hf.analyticAt z) hc ?_
  · unfold zeroCount
    convert h using 2
    · rw [hM, Real.log_div (by positivity) (norm_ne_zero_iff.mpr hc),
        Real.log_mul hA0.ne' (Real.exp_pos _).ne', Real.log_exp]
    · rw [mul_div_assoc, div_self hr.ne', mul_one]
  · intro z hz
    rw [mem_sphere_iff_norm, hR] at hz
    have hz' : ‖z‖ ≤ ‖c‖ + 2 * r := by
      calc ‖z‖ = ‖(z - c) + c‖ := by congr 1; ring
        _ ≤ ‖z - c‖ + ‖c‖ := norm_add_le _ _
        _ = ‖c‖ + 2 * r := by rw [hz]; ring
    calc ‖f z‖ ≤ A * Real.exp (B * ‖z‖ ^ ρ) := hgrowth z
      _ ≤ M := by
        rw [hM]
        gcongr

/-! ### Dyadic grouping -/

/-- The dyadic index `⌊log₂ ‖s‖⌋₊` of a point. -/
noncomputable def dyadicIdx (s : ℂ) : ℕ := ⌊Real.logb 2 ‖s‖⌋₊

lemma two_pow_dyadicIdx_le {s : ℂ} (hs : 1 < ‖s‖) : (2:ℝ) ^ dyadicIdx s ≤ ‖s‖ := by
  have h0 : 0 < ‖s‖ := by linarith
  have hl : 0 ≤ Real.logb 2 ‖s‖ := Real.logb_nonneg one_lt_two hs.le
  calc (2:ℝ) ^ dyadicIdx s = (2:ℝ) ^ (dyadicIdx s : ℝ) := (Real.rpow_natCast _ _).symm
    _ ≤ (2:ℝ) ^ Real.logb 2 ‖s‖ :=
        Real.rpow_le_rpow_of_exponent_le one_le_two (Nat.floor_le hl)
    _ = ‖s‖ := Real.rpow_logb two_pos (by norm_num) h0

lemma lt_two_pow_dyadicIdx_succ {s : ℂ} (hs : 1 < ‖s‖) :
    ‖s‖ < (2:ℝ) ^ (dyadicIdx s + 1) := by
  have h0 : 0 < ‖s‖ := by linarith
  calc ‖s‖ = (2:ℝ) ^ Real.logb 2 ‖s‖ := (Real.rpow_logb two_pos (by norm_num) h0).symm
    _ < (2:ℝ) ^ ((dyadicIdx s : ℝ) + 1) :=
        Real.rpow_lt_rpow_of_exponent_lt one_lt_two (Nat.lt_floor_add_one _)
    _ = (2:ℝ) ^ (dyadicIdx s + 1) := by
        rw [← Real.rpow_natCast]
        push_cast
        rfl

lemma two_pow_rpow_neg_mul (k : ℕ) (a b : ℝ) :
    ((2:ℝ) ^ k) ^ (-a) * ((2:ℝ) ^ k) ^ b = ((2:ℝ) ^ (b - a)) ^ k := by
  rw [← Real.rpow_natCast (2:ℝ) k, ← Real.rpow_mul (by norm_num), ← Real.rpow_mul (by norm_num),
    ← Real.rpow_add two_pos, ← Real.rpow_natCast ((2:ℝ) ^ (b - a)) k,
    ← Real.rpow_mul (by norm_num)]
  congr 1
  ring

lemma two_pow_rpow_neg (k : ℕ) (a : ℝ) : ((2:ℝ) ^ k) ^ (-a) = ((2:ℝ) ^ (-a)) ^ k := by
  rw [← Real.rpow_natCast (2:ℝ) k, ← Real.rpow_mul (by norm_num),
    ← Real.rpow_natCast ((2:ℝ) ^ (-a)) k, ← Real.rpow_mul (by norm_num)]
  congr 1
  ring

/-- The contribution of the `k`-th dyadic group of zeros (those with `2^k ≤ ‖s‖ < 2^(k+1)`) is
dominated by a geometric term. -/
lemma dyadic_group_sum_le (hf : Differentiable ℂ f) (hne : ∃ z, f z ≠ 0) {c : ℂ} (hc : f c ≠ 0)
    {A B ρ p : ℝ} (hA : 1 ≤ A) (hB : 0 ≤ B) (hρ : 0 < ρ) (hp : ρ < p)
    (hgrowth : ∀ z, ‖f z‖ ≤ A * Real.exp (B * ‖z‖ ^ ρ))
    (F : Finset {s : ℂ // f s = 0 ∧ s ≠ 0}) (hF : ∀ s ∈ F, 1 < ‖(s : ℂ)‖) (k : ℕ) :
    ∑ s ∈ F with dyadicIdx s.1 = k, (analyticOrderNatAt f s : ℝ) * ‖(s : ℂ)‖ ^ (-p)
      ≤ (B * (3 * ‖c‖ + 4) ^ ρ * ((2:ℝ) ^ (ρ - p)) ^ k
          + |Real.log A - Real.log ‖f c‖| * ((2:ℝ) ^ (-p)) ^ k) / Real.log 2 := by
  classical
  set G := F.filter (fun s : {s : ℂ // f s = 0 ∧ s ≠ 0} ↦ dyadicIdx s.1 = k) with hGdef
  have hG : ∀ s ∈ G, 1 < ‖(s : ℂ)‖ ∧ dyadicIdx (s : ℂ) = k := fun s hs ↦ by
    simp only [hGdef, Finset.mem_filter] at hs
    exact ⟨hF s hs.1, hs.2⟩
  set r : ℝ := ‖c‖ + 2 ^ (k + 1) with hr
  have hr0 : 0 < r := by positivity
  have hmem : ∀ s ∈ G, (s : ℂ) ∈ closedBall c |r| := by
    intro s hs
    rw [mem_closedBall_iff_norm, abs_of_pos hr0, hr]
    have := lt_two_pow_dyadicIdx_succ (hG s hs).1
    rw [(hG s hs).2] at this
    linarith [norm_sub_le (s : ℂ) c]
  have hpk : 0 < (2:ℝ) ^ k := by positivity
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hin : Real.log A + B * (‖c‖ + 2 * r) ^ ρ - Real.log ‖f c‖
      ≤ B * (3 * ‖c‖ + 4) ^ ρ * ((2:ℝ) ^ k) ^ ρ + |Real.log A - Real.log ‖f c‖| := by
    have h1 : (‖c‖ + 2 * r) ^ ρ ≤ (3 * ‖c‖ + 4) ^ ρ * ((2:ℝ) ^ k) ^ ρ := by
      rw [← Real.mul_rpow (by positivity) (by positivity)]
      apply Real.rpow_le_rpow (by positivity) _ hρ.le
      rw [hr, pow_succ]
      have : (1:ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
      nlinarith [norm_nonneg c]
    have h2 : Real.log A - Real.log ‖f c‖ ≤ |Real.log A - Real.log ‖f c‖| := le_abs_self _
    nlinarith [mul_le_mul_of_nonneg_left h1 hB]
  have hnn : 0 ≤ ((2:ℝ) ^ k) ^ (-p) := Real.rpow_nonneg hpk.le _
  calc ∑ s ∈ G, (analyticOrderNatAt f s : ℝ) * ‖(s : ℂ)‖ ^ (-p)
      ≤ ∑ s ∈ G, (analyticOrderNatAt f s : ℝ) * ((2:ℝ) ^ k) ^ (-p) := by
        apply Finset.sum_le_sum
        intro s hs
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Real.rpow_le_rpow_of_nonpos hpk _ (by linarith)
        rw [← (hG s hs).2]
        exact two_pow_dyadicIdx_le (hG s hs).1
    _ = ((2:ℝ) ^ k) ^ (-p) * ∑ s ∈ G, (analyticOrderNatAt f s : ℝ) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun s _ ↦ ?_
        ring
    _ ≤ ((2:ℝ) ^ k) ^ (-p) * zeroCount f c r :=
        mul_le_mul_of_nonneg_left (sum_ord_le_zeroCount hf hne G hmem) hnn
    _ ≤ ((2:ℝ) ^ k) ^ (-p)
          * ((Real.log A + B * (‖c‖ + 2 * r) ^ ρ - Real.log ‖f c‖) / Real.log 2) :=
        mul_le_mul_of_nonneg_left (zeroCount_le hf hc hA hB hρ hgrowth hr0) hnn
    _ ≤ ((2:ℝ) ^ k) ^ (-p)
          * ((B * (3 * ‖c‖ + 4) ^ ρ * ((2:ℝ) ^ k) ^ ρ + |Real.log A - Real.log ‖f c‖|)
              / Real.log 2) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hin hlog.le) hnn
    _ = (B * (3 * ‖c‖ + 4) ^ ρ * ((2:ℝ) ^ (ρ - p)) ^ k
          + |Real.log A - Real.log ‖f c‖| * ((2:ℝ) ^ (-p)) ^ k) / Real.log 2 := by
        rw [← two_pow_rpow_neg_mul k p ρ, ← two_pow_rpow_neg k p]
        ring

/-- **L3a: convergence exponent.**  For an entire function `f`, not identically zero, with
`‖f z‖ ≤ A exp(B ‖z‖^ρ)`, and every `p > ρ`, the sum `∑ ord_s(f) ‖s‖^(-p)` over the nonzero
zeros `s` of `f` converges. -/
theorem summable_zero_multiplicity_rpow {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hne : ∃ z, f z ≠ 0)
    {A B ρ p : ℝ} (hA : 1 ≤ A) (hB : 0 ≤ B) (hρ : 0 < ρ) (hp : ρ < p)
    (hgrowth : ∀ z, ‖f z‖ ≤ A * Real.exp (B * ‖z‖ ^ ρ)) :
    Summable (fun s : {s : ℂ // f s = 0 ∧ s ≠ 0} ↦
      (analyticOrderNatAt f s : ℝ) * ‖(s : ℂ)‖ ^ (-p)) := by
  classical
  obtain ⟨c, hc⟩ := hne
  have hne' : ∃ z, f z ≠ 0 := ⟨c, hc⟩
  set g : {s : ℂ // f s = 0 ∧ s ≠ 0} → ℝ :=
    fun s ↦ (analyticOrderNatAt f s : ℝ) * ‖(s : ℂ)‖ ^ (-p) with hg
  have hg0 : ∀ s, 0 ≤ g s := fun s ↦ by positivity
  -- the finitely many zeros in the closed unit ball
  have hsmall : {s : {s : ℂ // f s = 0 ∧ s ≠ 0} | ‖(s : ℂ)‖ ≤ 1}.Finite := by
    have hfin := (MeromorphicOn.divisor f (closedBall (0:ℂ) |1|)).finiteSupport
      (isCompact_closedBall _ _)
    refine (hfin.preimage (f := fun s : {s : ℂ // f s = 0 ∧ s ≠ 0} ↦ (s : ℂ))
      Subtype.val_injective.injOn).subset ?_
    intro s hs
    have hs : ‖(s : ℂ)‖ ≤ 1 := hs
    simp only [mem_preimage, Function.mem_support]
    have hs' : (s : ℂ) ∈ closedBall (0:ℂ) |1| := by
      rw [abs_one, mem_closedBall_zero_iff]
      exact hs
    rw [divisor_eq_analyticOrderNatAt hf hne' hs']
    have := one_le_analyticOrderNatAt hf hne' s.2.1
    exact_mod_cast (by omega : analyticOrderNatAt f s ≠ 0)
  set K₀ : ℝ := ∑ s ∈ hsmall.toFinset, g s with hK₀
  -- geometric constants
  set q₁ : ℝ := (2:ℝ) ^ (ρ - p) with hq₁def
  set q₂ : ℝ := (2:ℝ) ^ (-p) with hq₂def
  have hq₁ : q₁ < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
  have hq₂ : q₂ < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
  have hq₁0 : 0 ≤ q₁ := by positivity
  have hq₂0 : 0 ≤ q₂ := by positivity
  set C₁ : ℝ := B * (3 * ‖c‖ + 4) ^ ρ with hC₁def
  set C₂ : ℝ := |Real.log A - Real.log ‖f c‖| with hC₂def
  have hC₁ : 0 ≤ C₁ := by positivity
  have hC₂ : 0 ≤ C₂ := abs_nonneg _
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  set K₁ : ℝ := (C₁ * (1 - q₁)⁻¹ + C₂ * (1 - q₂)⁻¹) / Real.log 2 with hK₁
  refine summable_of_sum_le hg0 (c := K₀ + K₁) (fun F ↦ ?_)
  rw [← Finset.sum_filter_add_sum_filter_not F (fun s ↦ ‖(s : ℂ)‖ ≤ 1)]
  apply add_le_add
  · apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro s hs
      simp only [Finset.mem_filter] at hs
      simpa using hs.2
    · intro s _ _
      exact hg0 s
  · set F₁ := F.filter (fun s : {s : ℂ // f s = 0 ∧ s ≠ 0} ↦ ¬ ‖(s : ℂ)‖ ≤ 1) with hF₁def
    have hF₁ : ∀ s ∈ F₁, 1 < ‖(s : ℂ)‖ := fun s hs ↦ by
      simp only [hF₁def, Finset.mem_filter] at hs
      exact lt_of_not_ge hs.2
    set J := F₁.sup (fun s : {s : ℂ // f s = 0 ∧ s ≠ 0} ↦ dyadicIdx (s : ℂ)) + 1 with hJ
    have hmaps : ∀ s ∈ F₁, dyadicIdx (s : ℂ) ∈ Finset.range J := fun s hs ↦ by
      rw [Finset.mem_range]
      exact Nat.lt_succ_of_le (Finset.le_sup (f := fun s : {s : ℂ // f s = 0 ∧ s ≠ 0} ↦ dyadicIdx (s : ℂ)) hs)
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    have h1 : ∑ k ∈ Finset.range J, q₁ ^ k ≤ (1 - q₁)⁻¹ := by
      rw [← tsum_geometric_of_lt_one hq₁0 hq₁]
      exact (summable_geometric_of_lt_one hq₁0 hq₁).sum_le_tsum _ (fun k _ ↦ by positivity)
    have h2 : ∑ k ∈ Finset.range J, q₂ ^ k ≤ (1 - q₂)⁻¹ := by
      rw [← tsum_geometric_of_lt_one hq₂0 hq₂]
      exact (summable_geometric_of_lt_one hq₂0 hq₂).sum_le_tsum _ (fun k _ ↦ by positivity)
    calc ∑ k ∈ Finset.range J, ∑ s ∈ F₁ with dyadicIdx s.1 = k, g s
        ≤ ∑ k ∈ Finset.range J, (C₁ * q₁ ^ k + C₂ * q₂ ^ k) / Real.log 2 := by
          apply Finset.sum_le_sum
          intro k _
          exact dyadic_group_sum_le hf hne' hc hA hB hρ hp hgrowth F₁ hF₁ k
      _ = (C₁ * ∑ k ∈ Finset.range J, q₁ ^ k + C₂ * ∑ k ∈ Finset.range J, q₂ ^ k)
            / Real.log 2 := by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_div]
      _ ≤ K₁ := by
          apply div_le_div_of_nonneg_right _ hlog.le
          nlinarith [mul_le_mul_of_nonneg_left h1 hC₁, mul_le_mul_of_nonneg_left h2 hC₂]

end Count

end DBN

#print axioms DBN.summable_zero_multiplicity_rpow
