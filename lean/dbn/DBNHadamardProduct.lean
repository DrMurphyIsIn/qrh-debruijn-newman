/-
  DBNHadamardProduct -- the even canonical product (Route C / C3, obligation L3b of
  telperion/docs/HADAMARD_PLAN_2026-09-23.md, section 3).

  For a sequence of reciprocal zeros `τ : ℕ → ℂ` with `∑ ‖τ k‖² < ∞`, the even genus-zero product

    evenProduct τ z := ∏' k, (1 − z² τ_k²)

  converges (`hasProd_evenProduct`), is entire (`differentiable_evenProduct`, locally uniform
  convergence), is even, equals `1` at the origin, satisfies the growth bound

    ‖evenProduct τ z‖ ≤ exp ((1 + 2/p) (∑' k, ‖τ k‖^p) ‖z‖^p)        (`norm_evenProduct_le`)

  for every `0 < p ≤ 2` with `∑ ‖τ k‖^p < ∞` (from `log(1 + x) ≤ (1 + 1/α) x^α`, `α = p/2`), vanishes
  exactly at the points `z` with `z² τ_k² = 1` for some `k` (`evenProduct_eq_zero_iff`), and its
  order of vanishing at such a `z ≠ 0` is the number of indices `k` with `z² τ_k² = 1`
  (`analyticOrderNatAt_evenProduct`): the product is split into the finitely many vanishing
  factors, each of order one, and a zero-free remainder.

  Everything here is abstract complex analysis and mentions neither `Φ` nor `H_t`.  WHAT IS NOT
  HERE: the zero counting of an entire function of finite order (L3a), the quotient argument and
  the Jensen-in-the-mean estimate (L3c/L3d), and the assembly of the Hadamard factorisation
  (L3e).  Nothing here proves RH.  conjecture1_proved = False.
-/
import Mathlib

open Filter Topology

namespace DBN

/-! ### Generic products over an arbitrary index type -/

section generic

variable {ι : Type*} (τ : ι → ℂ)

/-- The factors, written in the `1 + f` shape used by Mathlib's product lemmas. -/
lemma factor_eq_one_add (z : ℂ) (k : ι) :
    1 - z ^ 2 * τ k ^ 2 = 1 + -(z ^ 2 * τ k ^ 2) := by ring

lemma factor_fun_eq (z : ℂ) :
    (fun k ↦ 1 - z ^ 2 * τ k ^ 2) = fun k ↦ 1 + -(z ^ 2 * τ k ^ 2) := by
  funext k; ring

lemma norm_neg_factor (z : ℂ) (k : ι) : ‖-(z ^ 2 * τ k ^ 2)‖ = ‖z‖ ^ 2 * ‖τ k‖ ^ 2 := by
  rw [norm_neg, norm_mul, norm_pow, norm_pow]

variable {τ}

/-- Summability of the factor norms at every point. -/
lemma summable_norm_neg_factor (hτ2 : Summable (fun k ↦ ‖τ k‖ ^ 2)) (z : ℂ) :
    Summable (fun k ↦ ‖-(z ^ 2 * τ k ^ 2)‖) := by
  simp_rw [norm_neg_factor]
  exact hτ2.mul_left _

/-- The product converges at every point. -/
theorem multipliable_factor (hτ2 : Summable (fun k ↦ ‖τ k‖ ^ 2)) (z : ℂ) :
    Multipliable (fun k ↦ 1 - z ^ 2 * τ k ^ 2) := by
  rw [factor_fun_eq]
  exact multipliable_one_add_of_summable (summable_norm_neg_factor hτ2 z)

/-- A finite product of the factors is entire. -/
lemma differentiable_finset_prod_factor (s : Finset ι) :
    Differentiable ℂ (fun w : ℂ ↦ ∏ k ∈ s, (1 - w ^ 2 * τ k ^ 2)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty]; exact differentiable_const _
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact ((differentiable_const _).sub ((differentiable_id.pow 2).mul_const _)).mul ih

/-- The infinite product is entire: locally uniform convergence on every ball. -/
theorem differentiable_tprod_factor (hτ2 : Summable (fun k ↦ ‖τ k‖ ^ 2)) :
    Differentiable ℂ (fun z : ℂ ↦ ∏' k, (1 - z ^ 2 * τ k ^ 2)) := by
  intro z
  set R : ℝ := ‖z‖ + 1 with hR
  have hzR : z ∈ Metric.ball (0 : ℂ) R := by
    rw [Metric.mem_ball, dist_zero_right]; linarith
  have hDO : DifferentiableOn ℂ (fun z : ℂ ↦ ∏' k, (1 + -(z ^ 2 * τ k ^ 2)))
      (Metric.ball 0 R) := by
    have hu : Summable (fun k ↦ R ^ 2 * ‖τ k‖ ^ 2) := hτ2.mul_left _
    have hLU := Summable.hasProdLocallyUniformlyOn_one_add (K := Metric.ball (0 : ℂ) R)
      (f := fun k (x : ℂ) ↦ -(x ^ 2 * τ k ^ 2)) Metric.isOpen_ball hu ?_ ?_
    · have hT := hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn.mp hLU
      refine hT.differentiableOn ?_ Metric.isOpen_ball
      refine Eventually.of_forall fun s ↦ ?_
      have := differentiable_finset_prod_factor (τ := τ) s
      simp_rw [factor_eq_one_add] at this
      exact this.differentiableOn
    · refine Eventually.of_forall fun k x hx ↦ ?_
      rw [norm_neg_factor]
      have hx' : ‖x‖ ≤ R := by
        rw [Metric.mem_ball, dist_zero_right] at hx; exact hx.le
      have hR0 : 0 ≤ R := by positivity
      gcongr
    · intro k
      exact ((continuous_id.pow 2).mul_const _).neg.continuousOn
  have : (fun z : ℂ ↦ ∏' k, (1 - z ^ 2 * τ k ^ 2))
      = fun z : ℂ ↦ ∏' k, (1 + -(z ^ 2 * τ k ^ 2)) := by
    funext w; simp_rw [factor_eq_one_add]
  rw [this]
  exact hDO.differentiableAt (Metric.isOpen_ball.mem_nhds hzR)

/-- The product is zero-free where all factors are. -/
theorem tprod_factor_ne_zero (hτ2 : Summable (fun k ↦ ‖τ k‖ ^ 2)) {z : ℂ}
    (hz : ∀ k, z ^ 2 * τ k ^ 2 ≠ 1) : ∏' k, (1 - z ^ 2 * τ k ^ 2) ≠ 0 := by
  rw [factor_fun_eq]
  refine tprod_one_add_ne_zero_of_summable (fun k ↦ ?_) (summable_norm_neg_factor hτ2 z)
  rw [← factor_eq_one_add]
  exact sub_ne_zero.mpr (Ne.symm (hz k))

end generic

/-! ### The even canonical product -/

/-- The even canonical product `∏' k, (1 − z² τ_k²)`. -/
noncomputable def evenProduct (τ : ℕ → ℂ) (z : ℂ) : ℂ := ∏' k, (1 - z ^ 2 * τ k ^ 2)

variable {τ : ℕ → ℂ}

theorem hasProd_evenProduct (hτ2 : Summable (fun k ↦ ‖τ k‖ ^ 2)) (z : ℂ) :
    HasProd (fun k ↦ 1 - z ^ 2 * τ k ^ 2) (evenProduct τ z) :=
  (multipliable_factor hτ2 z).hasProd

theorem differentiable_evenProduct (hτ2 : Summable (fun k ↦ ‖τ k‖ ^ 2)) :
    Differentiable ℂ (evenProduct τ) :=
  differentiable_tprod_factor hτ2

theorem evenProduct_zero (τ : ℕ → ℂ) : evenProduct τ 0 = 1 := by
  simp [evenProduct]

theorem evenProduct_neg (τ : ℕ → ℂ) (z : ℂ) : evenProduct τ (-z) = evenProduct τ z := by
  simp only [evenProduct, neg_sq]

/-! ### Growth -/

/-- `log (1 + x) ≤ (1 + 1/α) x^α` for `x ≥ 0` and `0 < α ≤ 1`. -/
lemma log_one_add_le_rpow {x α : ℝ} (hx : 0 ≤ x) (hα : 0 < α) (hα1 : α ≤ 1) :
    Real.log (1 + x) ≤ (1 + 1 / α) * x ^ α := by
  have hxα : 0 ≤ x ^ α := Real.rpow_nonneg hx _
  have h1α : 0 < 1 / α := by positivity
  rcases le_or_gt x 1 with hx1 | hx1
  · -- `log (1 + x) ≤ x ≤ x^α ≤ (1 + 1/α) x^α`
    have h1 : Real.log (1 + x) ≤ x := by
      have := Real.log_le_sub_one_of_pos (by linarith : 0 < 1 + x)
      linarith
    have h2 : x ≤ x ^ α := Real.self_le_rpow_of_le_one hx hx1 hα1
    nlinarith
  · -- `log (1 + x) ≤ log (2x) = log 2 + log x ≤ 1 + x^α/α ≤ (1 + 1/α) x^α`
    have hx0 : 0 < x := by linarith
    have h1 : Real.log (1 + x) ≤ Real.log (2 * x) :=
      Real.log_le_log (by linarith) (by linarith)
    have h2 : Real.log (2 * x) = Real.log 2 + Real.log x :=
      Real.log_mul (by norm_num) hx0.ne'
    have h3 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
      linarith
    have h4 : Real.log x ≤ x ^ α / α := Real.log_le_rpow_div hx hα
    have h5 : 1 ≤ x ^ α := Real.one_le_rpow hx1.le hα.le
    have h6 : x ^ α / α = 1 / α * x ^ α := by ring
    nlinarith

/-- `(‖z‖² ‖w‖²)^(p/2) = ‖z‖^p ‖w‖^p`. -/
lemma mul_sq_rpow_half (z w : ℂ) (p : ℝ) :
    (‖z‖ ^ 2 * ‖w‖ ^ 2) ^ (p / 2) = ‖z‖ ^ p * ‖w‖ ^ p := by
  have h : ∀ v : ℂ, (‖v‖ ^ 2) ^ (p / 2) = ‖v‖ ^ p := by
    intro v
    rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg v)]
    congr 1
    push_cast
    ring
  rw [Real.mul_rpow (by positivity) (by positivity), h, h]

/-- One factor: `‖1 − z² τ_k²‖ ≤ exp ((1 + 2/p) ‖z‖^p ‖τ_k‖^p)`. -/
lemma norm_factor_le_exp {p : ℝ} (hp0 : 0 < p) (hp2 : p ≤ 2) (z : ℂ) (k : ℕ) :
    ‖1 - z ^ 2 * τ k ^ 2‖ ≤ Real.exp ((1 + 2 / p) * (‖z‖ ^ p * ‖τ k‖ ^ p)) := by
  set x : ℝ := ‖z‖ ^ 2 * ‖τ k‖ ^ 2 with hx
  have hx0 : 0 ≤ x := by positivity
  have h1 : ‖1 - z ^ 2 * τ k ^ 2‖ ≤ 1 + x := by
    calc ‖1 - z ^ 2 * τ k ^ 2‖ ≤ ‖(1 : ℂ)‖ + ‖z ^ 2 * τ k ^ 2‖ := norm_sub_le _ _
      _ = 1 + x := by rw [norm_one, norm_mul, norm_pow, norm_pow]
  have h2 : 1 + x = Real.exp (Real.log (1 + x)) := (Real.exp_log (by linarith)).symm
  have h3 : Real.log (1 + x) ≤ (1 + 1 / (p / 2)) * x ^ (p / 2) :=
    log_one_add_le_rpow hx0 (by positivity) (by linarith)
  have h4 : (1 + 1 / (p / 2)) * x ^ (p / 2) = (1 + 2 / p) * (‖z‖ ^ p * ‖τ k‖ ^ p) := by
    rw [hx, mul_sq_rpow_half]
    congr 1
    field_simp
  calc ‖1 - z ^ 2 * τ k ^ 2‖ ≤ 1 + x := h1
    _ = Real.exp (Real.log (1 + x)) := h2
    _ ≤ Real.exp ((1 + 2 / p) * (‖z‖ ^ p * ‖τ k‖ ^ p)) := by
        rw [Real.exp_le_exp, ← h4]; exact h3

/-- **Growth of the even canonical product**: for `0 < p ≤ 2` with `∑ ‖τ k‖^p < ∞`,
`‖evenProduct τ z‖ ≤ exp ((1 + 2/p) (∑' k, ‖τ k‖^p) ‖z‖^p)`. -/
theorem norm_evenProduct_le (hτ2 : Summable (fun k ↦ ‖τ k‖ ^ 2)) {p : ℝ} (hp0 : 0 < p)
    (hp2 : p ≤ 2) (hτp : Summable (fun k ↦ ‖τ k‖ ^ p)) (z : ℂ) :
    ‖evenProduct τ z‖ ≤ Real.exp ((1 + 2 / p) * (∑' k, ‖τ k‖ ^ p) * ‖z‖ ^ p) := by
  have hT : Tendsto (fun n ↦ ‖∏ k ∈ Finset.range n, (1 - z ^ 2 * τ k ^ 2)‖) atTop
      (𝓝 ‖evenProduct τ z‖) :=
    (hasProd_evenProduct hτ2 z).tendsto_prod_nat.norm
  refine le_of_tendsto' hT fun n ↦ ?_
  have hc : 0 ≤ (1 + 2 / p) * ‖z‖ ^ p := by positivity
  calc ‖∏ k ∈ Finset.range n, (1 - z ^ 2 * τ k ^ 2)‖
      ≤ ∏ k ∈ Finset.range n, ‖1 - z ^ 2 * τ k ^ 2‖ := Finset.norm_prod_le _ _
    _ ≤ ∏ k ∈ Finset.range n, Real.exp ((1 + 2 / p) * (‖z‖ ^ p * ‖τ k‖ ^ p)) :=
        Finset.prod_le_prod (fun k _ ↦ norm_nonneg _) (fun k _ ↦ norm_factor_le_exp hp0 hp2 z k)
    _ = Real.exp (∑ k ∈ Finset.range n, (1 + 2 / p) * (‖z‖ ^ p * ‖τ k‖ ^ p)) :=
        (Real.exp_sum _ _).symm
    _ = Real.exp ((1 + 2 / p) * ‖z‖ ^ p * ∑ k ∈ Finset.range n, ‖τ k‖ ^ p) := by
        congr 1
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ ↦ ?_
        ring
    _ ≤ Real.exp ((1 + 2 / p) * (∑' k, ‖τ k‖ ^ p) * ‖z‖ ^ p) := by
        rw [Real.exp_le_exp]
        have hs : ∑ k ∈ Finset.range n, ‖τ k‖ ^ p ≤ ∑' k, ‖τ k‖ ^ p :=
          hτp.sum_le_tsum _ (fun k _ ↦ by positivity)
        calc (1 + 2 / p) * ‖z‖ ^ p * ∑ k ∈ Finset.range n, ‖τ k‖ ^ p
            ≤ (1 + 2 / p) * ‖z‖ ^ p * ∑' k, ‖τ k‖ ^ p := by gcongr
          _ = (1 + 2 / p) * (∑' k, ‖τ k‖ ^ p) * ‖z‖ ^ p := by ring

/-! ### Zeros -/

/-- A product sequence with a vanishing factor converges to zero. -/
lemma eq_zero_of_hasProd_of_eq_zero {g : ℕ → ℂ} {L : ℂ} (h : HasProd g L) {k₀ : ℕ}
    (hk₀ : g k₀ = 0) : L = 0 := by
  have hT := h.tendsto_prod_nat
  have hev : (fun _ : ℕ ↦ (0 : ℂ)) =ᶠ[atTop] fun n ↦ ∏ k ∈ Finset.range n, g k := by
    filter_upwards [eventually_gt_atTop k₀] with n hn
    rw [Finset.prod_eq_zero (Finset.mem_range.mpr hn) hk₀]
  exact tendsto_nhds_unique hT (tendsto_const_nhds.congr' hev)

/-- The zeros of the even canonical product are exactly the points `z` with `z² τ_k² = 1`. -/
theorem evenProduct_eq_zero_iff (hτ2 : Summable (fun k ↦ ‖τ k‖ ^ 2)) (z : ℂ) :
    evenProduct τ z = 0 ↔ ∃ k, z ^ 2 * τ k ^ 2 = 1 := by
  constructor
  · intro h0
    by_contra hne
    push Not at hne
    exact tprod_factor_ne_zero hτ2 hne h0
  · rintro ⟨k, hk⟩
    exact eq_zero_of_hasProd_of_eq_zero (hasProd_evenProduct hτ2 z) (k₀ := k)
      (sub_eq_zero.mpr hk.symm)

/-- The even canonical product does not vanish at `z` when no factor does. -/
theorem evenProduct_ne_zero (hτ2 : Summable (fun k ↦ ‖τ k‖ ^ 2)) {z : ℂ}
    (hz : ∀ k, z ^ 2 * τ k ^ 2 ≠ 1) : evenProduct τ z ≠ 0 :=
  tprod_factor_ne_zero hτ2 hz

/-- Only finitely many factors vanish at a given point. -/
theorem finite_setOf_factor_eq_zero (hτ2 : Summable (fun k ↦ ‖τ k‖ ^ 2)) (z : ℂ) :
    {k | z ^ 2 * τ k ^ 2 = 1}.Finite := by
  rcases eq_or_ne z 0 with rfl | hz
  · have : {k : ℕ | (0 : ℂ) ^ 2 * τ k ^ 2 = 1} = ∅ := by
      ext k; simp
    rw [this]; exact Set.finite_empty
  · have hzpos : 0 < ‖z‖ ^ 2 := by positivity
    have hT : Tendsto (fun k ↦ ‖τ k‖ ^ 2) cofinite (𝓝 0) := hτ2.tendsto_cofinite_zero
    have hev : ∀ᶠ k in cofinite, ‖τ k‖ ^ 2 < (‖z‖ ^ 2)⁻¹ :=
      hT.eventually_lt_const (by positivity)
    have hfin : {k | ¬ (‖τ k‖ ^ 2 < (‖z‖ ^ 2)⁻¹)}.Finite := eventually_cofinite.mp hev
    refine hfin.subset fun k hk ↦ ?_
    simp only [Set.mem_ofPred_eq] at hk ⊢
    have h1 : ‖z‖ ^ 2 * ‖τ k‖ ^ 2 = 1 := by
      have := congrArg norm hk
      rwa [norm_mul, norm_pow, norm_pow, norm_one] at this
    have h2 : ‖τ k‖ ^ 2 = (‖z‖ ^ 2)⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [h2]; exact lt_irrefl _

/-! ### Order of vanishing -/

/-- A vanishing factor has order exactly one at `z ≠ 0`. -/
lemma analyticOrderAt_factor {z : ℂ} (hz : z ≠ 0) {k : ℕ} (hk : z ^ 2 * τ k ^ 2 = 1) :
    analyticOrderAt (fun w : ℂ ↦ 1 - w ^ 2 * τ k ^ 2) z = 1 := by
  have hd : Differentiable ℂ (fun w : ℂ ↦ 1 - w ^ 2 * τ k ^ 2) :=
    (differentiable_const _).sub ((differentiable_id.pow 2).mul_const _)
  refine (hd.analyticAt z).analyticOrderAt_eq_one_of_zero_deriv_ne_zero ?_ ?_
  · exact sub_eq_zero.mpr hk.symm
  · have hD : HasDerivAt (fun w : ℂ ↦ 1 - w ^ 2 * τ k ^ 2) (-(2 * z * τ k ^ 2)) z := by
      have := ((hasDerivAt_pow 2 z).mul_const (τ k ^ 2)).const_sub 1
      simpa using this
    rw [hD.deriv]
    have hτ : τ k ^ 2 ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hk; exact zero_ne_one hk
    exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero two_ne_zero hz) hτ)

/-- The order of a finite product of vanishing factors is its cardinality. -/
lemma analyticOrderAt_finset_prod_factor {z : ℂ} (hz : z ≠ 0) (s : Finset ℕ)
    (hs : ∀ k ∈ s, z ^ 2 * τ k ^ 2 = 1) :
    analyticOrderAt (fun w : ℂ ↦ ∏ k ∈ s, (1 - w ^ 2 * τ k ^ 2)) z = (s.card : ℕ∞) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Finset.card_empty, Nat.cast_zero]
    exact (analyticAt_const).analyticOrderAt_eq_zero.mpr one_ne_zero
  | insert a s ha ih =>
    have hfun : (fun w : ℂ ↦ ∏ k ∈ insert a s, (1 - w ^ 2 * τ k ^ 2))
        = (fun w : ℂ ↦ 1 - w ^ 2 * τ a ^ 2) * (fun w : ℂ ↦ ∏ k ∈ s, (1 - w ^ 2 * τ k ^ 2)) := by
      funext w
      simp only [Pi.mul_apply, Finset.prod_insert ha]
    have ha' : AnalyticAt ℂ (fun w : ℂ ↦ 1 - w ^ 2 * τ a ^ 2) z :=
      ((differentiable_const _).sub ((differentiable_id.pow 2).mul_const _)).analyticAt z
    have hs' : AnalyticAt ℂ (fun w : ℂ ↦ ∏ k ∈ s, (1 - w ^ 2 * τ k ^ 2)) z :=
      (differentiable_finset_prod_factor (τ := τ) s).analyticAt z
    rw [hfun, analyticOrderAt_mul ha' hs',
      analyticOrderAt_factor hz (hs a (Finset.mem_insert_self a s)),
      ih (fun k hk ↦ hs k (Finset.mem_insert_of_mem hk)), Finset.card_insert_of_notMem ha]
    push_cast
    ring

/-- Splitting the product at a point: the vanishing factors times the rest. -/
lemma evenProduct_eq_finset_prod_mul (hτ2 : Summable (fun k ↦ ‖τ k‖ ^ 2)) (s : Finset ℕ)
    (w : ℂ) :
    evenProduct τ w = (∏ k ∈ s, (1 - w ^ 2 * τ k ^ 2))
      * ∏' k : ↥((s : Set ℕ)ᶜ), (1 - w ^ 2 * τ k ^ 2) := by
  have h1 : Multipliable ((fun k ↦ 1 - w ^ 2 * τ k ^ 2) ∘ (Subtype.val : (↑s : Set ℕ) → ℕ)) := by
    have := Finset.hasProd s (fun k ↦ 1 - w ^ 2 * τ k ^ 2)
    exact this.multipliable
  have h2 : Multipliable ((fun k ↦ 1 - w ^ 2 * τ k ^ 2) ∘ (Subtype.val : ↥((s : Set ℕ)ᶜ) → ℕ)) := by
    have hτ2' : Summable (fun k : ↥((s : Set ℕ)ᶜ) ↦ ‖τ k‖ ^ 2) := hτ2.subtype _
    exact multipliable_factor (τ := fun k : ↥((s : Set ℕ)ᶜ) ↦ τ k) hτ2' w
  have := Multipliable.tprod_mul_tprod_compl (s := (↑s : Set ℕ)) h1 h2
  have h3 : ∏' x : (↑s : Set ℕ), (1 - w ^ 2 * τ x ^ 2) = ∏ k ∈ s, (1 - w ^ 2 * τ k ^ 2) := by
    rw [tprod_fintype]
    exact Finset.prod_coe_sort s (fun k ↦ 1 - w ^ 2 * τ k ^ 2)
  rw [evenProduct, ← this, h3]

/-- **Order of the even canonical product** at `z ≠ 0`: the number of vanishing factors. -/
theorem analyticOrderNatAt_evenProduct (hτ2 : Summable (fun k ↦ ‖τ k‖ ^ 2)) {z : ℂ} (hz : z ≠ 0) :
    analyticOrderNatAt (evenProduct τ) z = (finite_setOf_factor_eq_zero hτ2 z).toFinset.card := by
  set s : Finset ℕ := (finite_setOf_factor_eq_zero hτ2 z).toFinset with hs_def
  have hmem : ∀ k, k ∈ s ↔ z ^ 2 * τ k ^ 2 = 1 := fun k ↦ by
    rw [hs_def, Set.Finite.mem_toFinset]; rfl
  -- the remainder product over the complement
  set Q : ℂ → ℂ := fun w ↦ ∏' k : ↥((s : Set ℕ)ᶜ), (1 - w ^ 2 * τ k ^ 2) with hQ
  have hτ2' : Summable (fun k : ↥((s : Set ℕ)ᶜ) ↦ ‖τ k‖ ^ 2) := hτ2.subtype _
  have hQd : Differentiable ℂ Q := differentiable_tprod_factor hτ2'
  have hQz : Q z ≠ 0 := by
    refine tprod_factor_ne_zero hτ2' fun k ↦ ?_
    have hk : (k : ℕ) ∉ s := k.2
    exact fun h ↦ hk ((hmem k).mpr h)
  have hsplit : evenProduct τ = (fun w ↦ ∏ k ∈ s, (1 - w ^ 2 * τ k ^ 2)) * Q := by
    funext w
    rw [Pi.mul_apply, evenProduct_eq_finset_prod_mul hτ2 s w]
  have hord : analyticOrderAt (evenProduct τ) z = (s.card : ℕ∞) := by
    rw [hsplit, analyticOrderAt_mul ((differentiable_finset_prod_factor (τ := τ) s).analyticAt z)
        (hQd.analyticAt z),
      analyticOrderAt_finset_prod_factor hz s (fun k hk ↦ (hmem k).mp hk),
      (hQd.analyticAt z).analyticOrderAt_eq_zero.mpr hQz, add_zero]
  rw [analyticOrderNatAt, hord]
  simp

end DBN

#print axioms DBN.hasProd_evenProduct
#print axioms DBN.differentiable_evenProduct
#print axioms DBN.evenProduct_zero
#print axioms DBN.evenProduct_neg
#print axioms DBN.norm_evenProduct_le
#print axioms DBN.evenProduct_eq_zero_iff
#print axioms DBN.evenProduct_ne_zero
#print axioms DBN.finite_setOf_factor_eq_zero
#print axioms DBN.analyticOrderNatAt_evenProduct
