/-
  DBNHadamard -- the Hadamard factorisation of an even entire function of order `< 2`
  (Route C / C3, obligation L3 of telperion/docs/DESIGN_RH_dbn_debruijn_real_zeros_2026-09-22.md;
  plan telperion/docs/HADAMARD_PLAN_2026-09-23.md).

  **Theorem** (`evenHadamardData_of_order_lt_two`).  Let `f` be entire, even, not identically
  zero, with `‖f z‖ ≤ A exp(B ‖z‖^ρ)` for some `0 < ρ < 2`.  Then `f` carries abstract even
  Hadamard data (`DBNStep.EvenHadamardData`): there are `c : ℂ`, `m : ℕ` and `τ : ℕ → ℂ` with

      f z = lim_n c · z^{2m} · ∏_{k<n} (1 − z² τ_k²)      for every `z`.

  The route is the genus-zero Hadamard theorem in the variable `z²`, assembled from four
  Mathlib-only modules:

    * `DBNHadamardCount`   (L3a) Jensen's inequality ⇒ `Σ ord_s(f) ‖s‖^{-p} < ∞` for `p > ρ`;
    * `DBNHadamardProduct` (L3b) the even canonical product `P₀ z = ∏' k, (1 − z² τ_k²)`: entire,
      `P₀ 0 = 1`, growth `log ‖P₀ z‖ ≤ K ‖z‖^p`, zeros and multiplicities;
    * `DBNHadamardMean`    (L3c/L3d) `g = exp ∘ H` for the zero-free quotient, and the estimate
      `circleAverage |Re H| 0 R ≤ 2 (log A + (B + K) R^p) + |Re H 0|`.  The classical
      minimum-modulus step for `P₀` is REPLACED by Jensen's formula in the mean
      (`circleAverage (log ‖P₀‖) ≥ 0`), so no exceptional circles are needed;
    * `DBNHadamardLinear`  (L3e) Poisson + Borel-Carathéodory + Cauchy ⇒ `H` is affine.

  This module supplies the bookkeeping that is specific to EVEN functions and to the
  ℕ-indexed shape of `EvenHadamardData`: orders at `±s` agree and the order at `0` is even
  (`analyticOrderAt_neg_of_even`, `even_analyticOrderNatAt_zero`); one representative per pair
  `±s` (`IsRep`), listed with multiplicity as a sequence `τ` (`repSeq`); the quotient
  `f / (z^{2m} P₀)` is entire and zero-free via meromorphic normal forms (`exists_quotient`);
  evenness kills the linear term of `H`.

  WHAT IS NOT HERE: nothing about the location of zeros; nothing about `Φ`, `H_t` or the
  approximants (that is `DBNHadamardApprox`).  Nothing here proves RH.
  conjecture1_proved = False.
-/
import DBNStep
import DBNHadamardCount
import DBNHadamardProduct
import DBNHadamardMean
import DBNHadamardLinear

open Set Filter Topology Real

namespace DBN

variable {f : ℂ → ℂ}

/-! ### Orders of an even function -/

/-- The analytic order of an even function at `-z` equals its order at `z`. -/
lemma analyticOrderAt_neg_of_even (heven : ∀ z, f (-z) = f z) (z : ℂ) :
    analyticOrderAt f (-z) = analyticOrderAt f z := by
  have h := analyticOrderAt_comp_of_deriv_ne_zero (f := f) (g := fun w : ℂ ↦ -w) (z₀ := z)
    analyticAt_id.neg (by
      rw [show (fun w : ℂ ↦ -w) = Neg.neg from rfl, deriv_neg]
      exact neg_ne_zero.mpr one_ne_zero)
  have hfe : (f ∘ fun w : ℂ ↦ -w) = f := funext heven
  rw [hfe] at h
  exact h.symm

lemma analyticOrderNatAt_neg_of_even (heven : ∀ z, f (-z) = f z) (z : ℂ) :
    analyticOrderNatAt f (-z) = analyticOrderNatAt f z := by
  simp only [analyticOrderNatAt, analyticOrderAt_neg_of_even heven]

/-- The order at the origin of an even entire function (not identically zero) is even. -/
lemma even_analyticOrderNatAt_zero (hf : Differentiable ℂ f) (heven : ∀ z, f (-z) = f z)
    (hne : ∃ z, f z ≠ 0) : Even (analyticOrderNatAt f 0) := by
  set n := analyticOrderNatAt f 0 with hn
  have hfin := analyticOrderAt_ne_top_of_entire hf hne 0
  have hord : analyticOrderAt f 0 = n := by
    rw [hn, analyticOrderNatAt, ENat.natCast_toNat hfin]
  obtain ⟨g, hg, hg0, hfg⟩ := (hf.analyticAt 0).analyticOrderAt_eq_natCast.mp hord
  have hfg' : ∀ᶠ z in 𝓝 (0 : ℂ), f (-z) = (-z - 0) ^ n • g (-z) := by
    have ht : Tendsto (fun z : ℂ ↦ -z) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_neg.tendsto (0 : ℂ))
    exact ht.eventually hfg
  set φ : ℂ → ℂ := fun z ↦ g z - (-1) ^ n * g (-z) with hφ_def
  have hφ : ∀ᶠ z in 𝓝[≠] (0 : ℂ), φ z = 0 := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hfg, nhdsWithin_le_nhds hfg']
      with z hz h1 h2
    have hz' : z ≠ 0 := hz
    have hnp : (-z - 0) ^ n = (-1) ^ n * z ^ n := by
      rw [sub_zero, neg_eq_neg_one_mul, mul_pow]
    have e := heven z
    rw [h2, h1, hnp] at e
    simp only [sub_zero, smul_eq_mul] at e
    have : z ^ n * φ z = 0 := by
      simp only [hφ_def]
      linear_combination -e
    exact (mul_eq_zero.mp this).resolve_left (pow_ne_zero n hz')
  have hc : ContinuousAt φ 0 := by
    have h1 : ContinuousAt (fun z : ℂ ↦ g (-z)) 0 := by
      have : ContinuousAt g (-(0 : ℂ)) := by simpa using hg.continuousAt
      exact this.comp continuous_neg.continuousAt
    exact hg.continuousAt.sub (continuousAt_const.mul h1)
  have h0 : φ 0 = 0 := by
    have t1 : Tendsto φ (𝓝[≠] 0) (𝓝 (φ 0)) := hc.tendsto.mono_left nhdsWithin_le_nhds
    have t2 : Tendsto φ (𝓝[≠] 0) (𝓝 0) :=
      tendsto_const_nhds.congr' (hφ.mono fun z hz ↦ hz.symm)
    exact tendsto_nhds_unique t1 t2
  simp only [hφ_def, neg_zero] at h0
  have h1 : (1 - (-1) ^ n) * g 0 = 0 := by linear_combination h0
  have h2 : (-1 : ℂ) ^ n = 1 := by
    have := (mul_eq_zero.mp h1).resolve_right hg0
    linear_combination -this
  rcases Nat.even_or_odd n with hev | hodd
  · exact hev
  · rw [hodd.neg_one_pow] at h2
    norm_num at h2

/-! ### Representatives of `±` pairs -/

/-- `s` is the chosen representative of the pair `{s, -s}`: `re s > 0`, or `re s = 0` and
`im s > 0`. -/
def IsRep (s : ℂ) : Prop := 0 < s.re ∨ (s.re = 0 ∧ 0 < s.im)

lemma isRep_or_isRep_neg {s : ℂ} (hs : s ≠ 0) : IsRep s ∨ IsRep (-s) := by
  unfold IsRep
  simp only [Complex.neg_re, Complex.neg_im]
  rcases lt_trichotomy s.re 0 with h | h | h
  · right; left; linarith
  · rcases lt_trichotomy s.im 0 with h' | h' | h'
    · right; right; exact ⟨by linarith, by linarith⟩
    · exact absurd (Complex.ext h h') hs
    · left; right; exact ⟨h, h'⟩
  · left; left; exact h

lemma not_isRep_neg_of_isRep {s : ℂ} (h : IsRep s) : ¬ IsRep (-s) := by
  unfold IsRep at *
  simp only [Complex.neg_re, Complex.neg_im]
  rintro (h' | ⟨h1', h2'⟩) <;> rcases h with h | ⟨h1, h2⟩ <;> linarith

/-- The representative zeros of `f`: zeros `s ≠ 0` with `IsRep s`. -/
abbrev RepZero (f : ℂ → ℂ) : Type := {s : ℂ // f s = 0 ∧ s ≠ 0 ∧ IsRep s}

/-- The representative zeros of `f` listed with multiplicity. -/
abbrev ZeroIdx (f : ℂ → ℂ) : Type := Σ s : RepZero f, Fin (analyticOrderNatAt f s.1)

/-- L3a transported to the index type `ZeroIdx f`. -/
lemma summable_zeroIdx_rpow (hf : Differentiable ℂ f) (hne : ∃ z, f z ≠ 0)
    {A B ρ p : ℝ} (hA : 1 ≤ A) (hB : 0 ≤ B) (hρ : 0 < ρ) (hp : ρ < p)
    (hgrowth : ∀ z, ‖f z‖ ≤ A * Real.exp (B * ‖z‖ ^ ρ)) :
    Summable (fun t : ZeroIdx f ↦ ‖(t.1.1 : ℂ)‖ ^ (-p)) := by
  have h1 := summable_zero_multiplicity_rpow hf hne hA hB hρ hp hgrowth
  have h2 : Summable (fun s : RepZero f ↦
      (analyticOrderNatAt f s.1 : ℝ) * ‖(s.1 : ℂ)‖ ^ (-p)) := by
    have := h1.comp_injective
      (i := fun s : RepZero f ↦ (⟨s.1, s.2.1, s.2.2.1⟩ : {s : ℂ // f s = 0 ∧ s ≠ 0}))
      (fun a b hab ↦ by
        apply Subtype.ext
        have := congrArg Subtype.val hab
        simpa using this)
    exact this
  rw [summable_sigma_of_nonneg (fun t ↦ Real.rpow_nonneg (norm_nonneg _) _)]
  refine ⟨fun s ↦ (hasSum_fintype _).summable, ?_⟩
  convert h2 using 1
  funext s
  simp only [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

lemma countable_zeroIdx_of_summable {p : ℝ}
    (h : Summable (fun t : ZeroIdx f ↦ ‖(t.1.1 : ℂ)‖ ^ (-p))) : Countable (ZeroIdx f) := by
  have h' := h.toNNReal.countable_support_nnreal
  have hsupp : Function.support (fun t : ZeroIdx f ↦ (‖(t.1.1 : ℂ)‖ ^ (-p)).toNNReal) = univ := by
    ext t
    simp only [Function.mem_support, mem_univ, iff_true, ne_eq, Real.toNNReal_eq_zero, not_le]
    exact Real.rpow_pos_of_pos (norm_pos_iff.mpr t.1.2.2.1) _
  rw [hsupp] at h'
  exact Set.countable_univ_iff.mp h'

/-! ### The sequence of reciprocal representative zeros -/

/-- The sequence `τ`: `τ (e t) = (s_t)⁻¹` for an injection `e : ZeroIdx f → ℕ`, and `τ n = 0`
(a trivial factor) off the range of `e`. -/
noncomputable def repSeq (e : ZeroIdx f → ℕ) : ℕ → ℂ :=
  Function.extend e (fun t ↦ ((t.1.1 : ℂ))⁻¹) 0

lemma repSeq_apply {e : ZeroIdx f → ℕ} (he : Function.Injective e) (t : ZeroIdx f) :
    repSeq e (e t) = ((t.1.1 : ℂ))⁻¹ :=
  he.extend_apply _ _ _

lemma repSeq_of_notMem_range {e : ZeroIdx f → ℕ} {n : ℕ} (h : n ∉ range e) : repSeq e n = 0 := by
  unfold repSeq
  rw [Function.extend_apply' _ _ _ (by simpa [Set.mem_range] using h)]
  rfl

lemma summable_repSeq_rpow {e : ZeroIdx f → ℕ} (he : Function.Injective e) {q : ℝ} (hq : q ≠ 0)
    (h : Summable (fun t : ZeroIdx f ↦ ‖(t.1.1 : ℂ)‖ ^ (-q))) :
    Summable (fun k ↦ ‖repSeq e k‖ ^ q) := by
  rw [← he.summable_iff (f := fun k ↦ ‖repSeq e k‖ ^ q)]
  · convert h using 1
    funext t
    simp only [Function.comp, repSeq_apply he, norm_inv, Real.inv_rpow (norm_nonneg _),
      Real.rpow_neg (norm_nonneg _)]
  · intro k hk
    simp [repSeq_of_notMem_range hk, Real.zero_rpow hq]

/-- The number of `k` with `z² τ_k² = 1` is the order of `f` at `z` (for `z ≠ 0`). -/
lemma ncard_factor_eq_analyticOrderNatAt (heven : ∀ z, f (-z) = f z) {e : ZeroIdx f → ℕ} (he : Function.Injective e) {z : ℂ} (hz : z ≠ 0) :
    {k | z ^ 2 * repSeq e k ^ 2 = 1}.ncard = analyticOrderNatAt f z := by
  -- Step 1: the set is the image under `e` of `{t | s_t² = z²}`.
  have hset : {k | z ^ 2 * repSeq e k ^ 2 = 1} = e '' {t : ZeroIdx f | (t.1.1 : ℂ) ^ 2 = z ^ 2} := by
    ext k
    simp only [mem_ofPred_eq, mem_image]
    constructor
    · intro hk
      have hk' : k ∈ range e := by
        by_contra hk'
        rw [repSeq_of_notMem_range hk'] at hk
        simp at hk
      obtain ⟨t, rfl⟩ := hk'
      refine ⟨t, ?_, rfl⟩
      rw [repSeq_apply he, inv_pow, mul_inv_eq_one₀ (pow_ne_zero _ t.1.2.2.1)] at hk
      exact hk.symm
    · rintro ⟨t, ht, rfl⟩
      rw [repSeq_apply he, inv_pow, mul_inv_eq_one₀ (pow_ne_zero _ t.1.2.2.1)]
      exact ht.symm
  rw [hset, Set.ncard_image_of_injective _ he]
  -- Step 2: compute the cardinality of `{t | s_t² = z²}`.
  by_cases hfz : f z = 0
  · -- the representative of the pair `±z`
    obtain ⟨r, hr, hrz⟩ : ∃ r : ℂ, IsRep r ∧ (r = z ∨ r = -z) := by
      rcases isRep_or_isRep_neg hz with h | h
      · exact ⟨z, h, Or.inl rfl⟩
      · exact ⟨-z, h, Or.inr rfl⟩
    have hfr : f r = 0 := by rcases hrz with rfl | rfl <;> simp [heven, hfz]
    have hr0 : r ≠ 0 := by rcases hrz with rfl | rfl <;> simpa using hz
    obtain ⟨r₀, hr₀⟩ : ∃ r₀ : RepZero f, (r₀.1 : ℂ) = r := ⟨⟨r, hfr, hr0, hr⟩, rfl⟩
    have hrepz : analyticOrderNatAt f r = analyticOrderNatAt f z := by
      rcases hrz with rfl | rfl
      · rfl
      · exact analyticOrderNatAt_neg_of_even heven z
    have hsq : r ^ 2 = z ^ 2 := by rcases hrz with rfl | rfl <;> simp
    have hset2 : {t : ZeroIdx f | (t.1.1 : ℂ) ^ 2 = z ^ 2}
        = range (fun i : Fin (analyticOrderNatAt f r₀.1) ↦ (⟨r₀, i⟩ : ZeroIdx f)) := by
      ext ⟨s, i⟩
      simp only [mem_ofPred_eq, mem_range]
      constructor
      · intro hs
        -- `s = ±z` and `s` is a representative, so `s = r`
        have hs' : (s.1 : ℂ) = r := by
          rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with h | h <;> rcases hrz with rfl | rfl
          · exact h
          · have := not_isRep_neg_of_isRep s.2.2.2
            rw [h] at this
            exact absurd hr this
          · have := s.2.2.2
            rw [h] at this
            exact absurd this (not_isRep_neg_of_isRep hr)
          · exact h
        have hsr : s = r₀ := Subtype.ext (hs'.trans hr₀.symm)
        subst hsr
        exact ⟨i, rfl⟩
      · rintro ⟨j, hj⟩
        obtain ⟨h1, h2⟩ := Sigma.mk.inj_iff.mp hj
        subst h1
        rw [hr₀, hsq]
    rw [hset2, Set.ncard_range_of_injective, Nat.card_eq_fintype_card, Fintype.card_fin, hr₀, hrepz]
    intro i j hij
    exact eq_of_heq (Sigma.mk.inj_iff.mp hij).2
  · -- no zero at `±z`: the set is empty and the order is `0`
    have hempty : {t : ZeroIdx f | (t.1.1 : ℂ) ^ 2 = z ^ 2} = ∅ := by
      ext t
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
      intro ht
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp ht with h | h
      · exact hfz (h ▸ t.1.2.1)
      · exact hfz (by have := t.1.2.1; rw [h, heven] at this; exact this)
    rw [hempty, Set.ncard_empty, analyticOrderNatAt, analyticOrderAt_eq_zero.mpr (Or.inr hfz)]
    rfl

/-! ### The zero-free quotient -/

/-- If two entire functions (not identically zero) have the same orders everywhere, their quotient
is an entire zero-free function `g` with `f = g * P` everywhere. -/
lemma exists_quotient {f P : ℂ → ℂ} (hf : Differentiable ℂ f) (hP : Differentiable ℂ P)
    (hne : ∃ z, f z ≠ 0) (hPne : ∃ z, P z ≠ 0)
    (hord : ∀ z, analyticOrderNatAt P z = analyticOrderNatAt f z) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ (∀ z, g z ≠ 0) ∧ ∀ z, f z = g z * P z := by
  have hfa : AnalyticOnNhd ℂ f univ := fun z _ ↦ hf.analyticAt z
  have hPa : AnalyticOnNhd ℂ P univ := fun z _ ↦ hP.analyticAt z
  have hmer : MeromorphicOn (f / P) univ := hfa.meromorphicOn.div hPa.meromorphicOn
  set g := toMeromorphicNFOn (f / P) univ with hg_def
  have hNF : MeromorphicNFOn g univ := meromorphicNFOn_toMeromorphicNFOn (f / P) univ
  have hordz : ∀ z, meromorphicOrderAt g z = 0 := by
    intro z
    rw [hg_def, meromorphicOrderAt_toMeromorphicNFOn hmer (mem_univ z),
      meromorphicOrderAt_div (hfa z (mem_univ z)).meromorphicAt (hPa z (mem_univ z)).meromorphicAt,
      (hfa z (mem_univ z)).meromorphicOrderAt_eq, (hPa z (mem_univ z)).meromorphicOrderAt_eq]
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (analyticOrderAt_ne_top_of_entire hf hne z)
    obtain ⟨n', hn'⟩ := ENat.ne_top_iff_exists.mp (analyticOrderAt_ne_top_of_entire hP hPne z)
    have hnn : n' = n := by
      have := hord z
      rw [analyticOrderNatAt, analyticOrderNatAt, ← hn, ← hn'] at this
      simpa using this
    subst hnn
    rw [← hn, ← hn']
    simp
  have hga : ∀ z, AnalyticAt ℂ g z := fun z ↦
    (hNF (mem_univ z)).meromorphicOrderAt_nonneg_iff_analyticAt.mp (by rw [hordz z])
  have hgne : ∀ z, g z ≠ 0 := fun z ↦
    (hNF (mem_univ z)).meromorphicOrderAt_eq_zero_iff.mp (hordz z)
  refine ⟨g, fun z ↦ (hga z).differentiableAt, hgne, fun z ↦ ?_⟩
  by_cases hPz : P z = 0
  · have hfz : f z = 0 := by
      have h1 := one_le_analyticOrderNatAt hP hPne hPz
      rw [hord z] at h1
      by_contra hfz
      rw [analyticOrderNatAt, analyticOrderAt_eq_zero.mpr (Or.inr hfz)] at h1
      simp at h1
    rw [hfz, hPz, mul_zero]
  · have hdiv : AnalyticAt ℂ (f / P) z := (hf.analyticAt z).div (hP.analyticAt z) hPz
    have : g z = (f / P) z := by
      rw [hg_def, toMeromorphicNFOn_eq_toMeromorphicNFAt hmer (mem_univ z),
        toMeromorphicNFAt_eq_self.mpr hdiv.meromorphicNFAt]
    rw [this, Pi.div_apply, div_mul_cancel₀ _ hPz]

/-! ### The factorisation theorem -/

/-- **Hadamard factorisation, even genus-zero case.**  An even entire function, not identically
zero, of order `< 2` (`‖f z‖ ≤ A exp(B ‖z‖^ρ)` with `0 < ρ < 2`, `1 ≤ A`, `0 ≤ B`) carries
abstract even Hadamard data: `f z = lim c z^{2m} ∏_{k<n} (1 − z² τ_k²)`. -/
theorem evenHadamardData_of_order_lt_two (hf : Differentiable ℂ f)
    (heven : ∀ z, f (-z) = f z) (hne : ∃ z, f z ≠ 0) {A B ρ : ℝ}
    (hA : 1 ≤ A) (hB : 0 ≤ B) (hρ₀ : 0 < ρ) (hρ : ρ < 2)
    (hgrowth : ∀ z, ‖f z‖ ≤ A * Real.exp (B * ‖z‖ ^ ρ)) : Nonempty (EvenHadamardData f) := by
  set p : ℝ := (ρ + 2) / 2 with hp_def
  have hp0 : 0 < p := by rw [hp_def]; linarith
  have hρp : ρ < p := by rw [hp_def]; linarith
  have hp2 : p < 2 := by rw [hp_def]; linarith
  -- the zeros, with multiplicity, as a sequence
  have hsum_p := summable_zeroIdx_rpow hf hne hA hB hρ₀ hρp hgrowth
  have hsum_2 := summable_zeroIdx_rpow hf hne hA hB hρ₀ hρ hgrowth
  have : Countable (ZeroIdx f) := countable_zeroIdx_of_summable hsum_2
  obtain ⟨e, he⟩ := exists_injective_nat (ZeroIdx f)
  set τ : ℕ → ℂ := repSeq e with hτ_def
  have hτ2 : Summable (fun k ↦ ‖τ k‖ ^ 2) := by
    simpa only [Real.rpow_two] using summable_repSeq_rpow he two_ne_zero hsum_2
  have hτp : Summable (fun k ↦ ‖τ k‖ ^ p) := summable_repSeq_rpow he hp0.ne' hsum_p
  -- the even canonical product and the monomial
  set P₀ : ℂ → ℂ := evenProduct τ with hP₀_def
  have hP₀ : Differentiable ℂ P₀ := differentiable_evenProduct hτ2
  have hP₀0 : P₀ 0 = 1 := evenProduct_zero τ
  obtain ⟨m, hm⟩ := even_analyticOrderNatAt_zero hf heven hne
  set P : ℂ → ℂ := fun z ↦ z ^ (2 * m) * P₀ z with hP_def
  have hP : Differentiable ℂ P := (differentiable_id.pow _).mul hP₀
  have hP₀near : ∀ᶠ z in 𝓝 (0 : ℂ), P₀ z ≠ 0 :=
    hP₀.continuous.continuousAt.eventually_ne (by rw [hP₀0]; exact one_ne_zero)
  have hPne : ∃ z, P z ≠ 0 := by
    obtain ⟨z, hz1, hz2⟩ :=
      ((hP₀near.filter_mono (nhdsWithin_le_nhds (s := {(0 : ℂ)}ᶜ))).and
        eventually_mem_nhdsWithin).exists
    have hz2' : z ≠ 0 := hz2
    exact ⟨z, mul_ne_zero (pow_ne_zero _ hz2') hz1⟩
  have hP₀ne : ∃ z, P₀ z ≠ 0 := ⟨0, by rw [hP₀0]; exact one_ne_zero⟩
  -- `P` has the orders of `f`
  have hord : ∀ z, analyticOrderNatAt P z = analyticOrderNatAt f z := by
    intro z
    have hmon : AnalyticAt ℂ (fun w : ℂ ↦ w ^ (2 * m)) z := analyticAt_id.pow _
    have hmon_fin : analyticOrderAt (fun w : ℂ ↦ w ^ (2 * m)) z ≠ ⊤ :=
      analyticOrderAt_ne_top_of_entire (differentiable_id.pow _) ⟨1, by simp⟩ z
    have hP₀fin : analyticOrderAt P₀ z ≠ ⊤ := analyticOrderAt_ne_top_of_entire hP₀ hP₀ne z
    have hmul := analyticOrderNatAt_mul hmon (hP₀.analyticAt z) hmon_fin hP₀fin
    have hPeq : analyticOrderNatAt P z
        = analyticOrderNatAt ((fun w : ℂ ↦ w ^ (2 * m)) * P₀) z := rfl
    rw [hPeq, hmul]
    rcases eq_or_ne z 0 with rfl | hz
    · have h1 : analyticOrderNatAt (fun w : ℂ ↦ w ^ (2 * m)) 0 = 2 * m := by
        have : (fun w : ℂ ↦ w ^ (2 * m)) = (fun w : ℂ ↦ w - 0) ^ (2 * m) := by
          funext w; simp
        rw [this, analyticOrderNatAt, analyticOrderAt_centeredMonomial]
        simp
      have h2 : analyticOrderNatAt P₀ 0 = 0 := by
        rw [analyticOrderNatAt, analyticOrderAt_eq_zero (f := P₀) (z₀ := 0) |>.mpr
          (Or.inr (by rw [hP₀0]; exact one_ne_zero))]
        rfl
      rw [h1, h2, hm]; ring
    · have h1 : analyticOrderNatAt (fun w : ℂ ↦ w ^ (2 * m)) z = 0 := by
        rw [analyticOrderNatAt, analyticOrderAt_eq_zero (f := fun w : ℂ ↦ w ^ (2 * m)) (z₀ := z)
          |>.mpr (Or.inr (pow_ne_zero _ hz))]
        rfl
      rw [h1, zero_add, hP₀_def, analyticOrderNatAt_evenProduct hτ2 hz,
        ← Set.ncard_eq_toFinset_card _ _, ncard_factor_eq_analyticOrderNatAt heven he hz]
  -- the zero-free quotient and its logarithm
  obtain ⟨g, hg, hgne, hfg⟩ := exists_quotient hf hP hne hPne hord
  obtain ⟨H, hH, hgH⟩ := exists_exp_eq_of_ne_zero hg hgne
  -- growth of `f` with the exponent `p`
  have hfgrowth' : ∀ z, ‖f z‖ ≤ (A * Real.exp B) * Real.exp (B * ‖z‖ ^ p) := by
    intro z
    have hle : ‖z‖ ^ ρ ≤ 1 + ‖z‖ ^ p := by
      rcases le_or_gt ‖z‖ 1 with h | h
      · have := Real.rpow_le_one (norm_nonneg z) h hρ₀.le
        linarith [Real.rpow_nonneg (norm_nonneg z) p]
      · have := Real.rpow_le_rpow_of_exponent_le h.le hρp.le
        linarith
    calc ‖f z‖ ≤ A * Real.exp (B * ‖z‖ ^ ρ) := hgrowth z
      _ ≤ A * Real.exp (B * (1 + ‖z‖ ^ p)) := by
          gcongr
      _ = (A * Real.exp B) * Real.exp (B * ‖z‖ ^ p) := by
          rw [mul_add, mul_one, Real.exp_add]; ring
  have hA' : 1 ≤ A * Real.exp B := one_le_mul_of_one_le_of_one_le hA (Real.one_le_exp hB)
  -- growth of `P₀`
  set K : ℝ := (1 + 2 / p) * ∑' k, ‖τ k‖ ^ p with hK_def
  have hK : 0 ≤ K := by
    rw [hK_def]
    exact mul_nonneg (by positivity) (tsum_nonneg fun k ↦ Real.rpow_nonneg (norm_nonneg _) _)
  have hPgrowth : ∀ z, ‖P₀ z‖ ≤ Real.exp (K * ‖z‖ ^ p) := fun z ↦
    norm_evenProduct_le hτ2 hp0 hp2.le hτp z
  -- the mean estimate and linearity of `H`
  have hmean : ∀ R : ℝ, 1 ≤ R → circleAverage (fun z ↦ |(H z).re|) 0 R
      ≤ (2 * (B + K)) * R ^ p + (2 * Real.log (A * Real.exp B) + |(H 0).re|) := by
    intro R hR
    have := circleAverage_abs_re_le (m := m) hf hP₀ hP₀0 hH hgH (fun z ↦ hfg z) hA' hB hK hp0.le
      hfgrowth' hPgrowth hR
    linarith
  obtain ⟨a, b, hab⟩ := eq_linear_of_circleAverage_abs_re_le hH hp2 hmean
  -- evenness of `g`, hence `b = 0`
  have hPeven : ∀ z, P (-z) = P z := by
    intro z
    simp only [hP_def, (even_two_mul m).neg_pow, hP₀_def, evenProduct_neg]
  have hgsym : ∀ z, g (-z) = g z := by
    have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), g (-z) = g z := by
      refine Filter.Eventually.frequently ?_
      filter_upwards [nhdsWithin_le_nhds hP₀near, self_mem_nhdsWithin] with z hz1 hz2
      have hPz : P z ≠ 0 := mul_ne_zero (pow_ne_zero _ hz2) hz1
      have e1 := hfg (-z)
      rw [heven, hPeven, hfg z] at e1
      exact (mul_right_cancel₀ hPz e1).symm
    have h1 : AnalyticOnNhd ℂ (fun z ↦ g (-z)) univ := fun z _ ↦
      (hg.comp differentiable_id.neg).analyticAt z
    have h2 : AnalyticOnNhd ℂ g univ := fun z _ ↦ hg.analyticAt z
    exact fun z ↦
      h1.eqOn_of_preconnected_of_frequently_eq h2 isPreconnected_univ (mem_univ 0) hfreq (mem_univ z)
  have hb : b = 0 := by
    by_contra hb
    set z₀ : ℂ := Real.pi * Complex.I / (2 * b) with hz₀
    have h := hgsym z₀
    rw [← hgH, ← hgH, hab, hab] at h
    have h' : Complex.exp (a + b * z₀) / Complex.exp (a + b * -z₀) = 1 := by
      rw [h, div_self (Complex.exp_ne_zero _)]
    rw [← Complex.exp_sub] at h'
    have e : a + b * z₀ - (a + b * -z₀) = Real.pi * Complex.I := by
      rw [hz₀]; field_simp; ring
    rw [e, Complex.exp_pi_mul_I] at h'
    norm_num at h'
  -- assemble
  refine ⟨EvenHadamardData.ofHasProd (Complex.exp a) m τ P₀ (hasProd_evenProduct hτ2) fun z ↦ ?_⟩
  rw [hfg z, ← hgH z, hab z, hb, zero_mul, add_zero]
  simp only [hP_def]
  ring

end DBN

#print axioms DBN.evenHadamardData_of_order_lt_two
