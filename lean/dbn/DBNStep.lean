/-
  DBNStep -- the discrete de Bruijn step (Route C / C3, obligation L4 of
  telperion/docs/DESIGN_RH_dbn_debruijn_real_zeros_2026-09-22.md, section 2.2), developed
  against an ABSTRACT even Hadamard product so that it can be wired to the Hadamard
  factorisation (obligation L3e, `DBNHadamard.lean`, NOT on this island yet) later.

  The vertical-shift average of an entire function `f` is

    (T_δ f)(z) = (f(z + iδ) + f(z − iδ)) / 2          (`DBN.shiftAvg δ f`).

  On the kernel side `T_δ` is multiplication by `cosh(δu)` (`DBNHeatApprox.Gδ_succ`), which is why
  it is the right discretisation of the heat flow `e^{tu²}`; the `1 − ε D²` discretisation only
  preserves a zero strip and does not contract it (memo section 2.3), and is NOT used anywhere.

  **The step lemma** (`EvenHadamardData.shiftAvg_zero_im_sq_le`).  Let `f` be real
  (`f (conj z) = conj (f z)`) and carry even Hadamard data

    f z = lim_n c · z^{2m} · ∏_{k<n} (1 − z² τ_k²)       (`EvenHadamardData f`),

  (`τ k` the reciprocal of the `k`-th zero, one per `±` pair, `τ k = 0` a trivial factor).  If
  every zero of `f` satisfies `(Im z)² ≤ Δ2`, then for every `δ > 0` every zero `w` of `T_δ f`
  satisfies `(Im w)² ≤ max (Δ2 − δ²) 0`.

  Proof (memo section 2.2, made factor-by-factor).  Reality of `f` gives the conjugate expansion
  `f z = lim conj c · z^{2m} ∏ (1 − z² conj(τ_k)²)` for free, so
  `‖f z‖² = lim ‖c‖² ‖z‖^{4m} ∏_k Q_k(z)` with `Q_k(z) = ‖1 − z²τ_k²‖ ‖1 − z² conj(τ_k)²‖`.
  For `τ ≠ 0`, `ρ = τ⁻¹`, `Q(z) = ‖τ‖⁴ (‖z − ρ‖ ‖z − conj ρ‖)(‖z + ρ‖ ‖z + conj ρ‖)`, and for a
  conjugate pair `(‖z − σ‖ ‖z − conj σ‖)² = (a² + Y² + q²)² − 4Y²q²` (`a = Re z − Re σ`,
  `Y = Im z`, `q = Im σ`), a parabola in `Y²`.  At `z = w ± iδ` with `y = Im w > 0` the
  difference of the two values is `8 y δ (y² + δ² + a² − q²)`, positive as soon as
  `y² + δ² > Δ2 ≥ q²`.  So every factor strictly grows from `w − iδ` to `w + iδ`, the partial
  ratios are monotone, and `‖f(w + iδ)‖ > ‖f(w − iδ)‖`, which forbids `f(w + iδ) = −f(w − iδ)`.

  Iterating (`zero_im_sq_le_of_shiftAvg_iterate`) contracts `Δ2` by `δ²` per step.

  Everything here is abstract complex analysis: it imports only Mathlib and mentions neither `Φ`
  nor `H_t`.  WHAT IS NOT HERE: the Hadamard factorisation itself (that the de Bruijn
  approximants carry `EvenHadamardData` is obligation L3, open), the zero strip of `H_0`
  (obligation L1, open), and de Bruijn's theorem.  Nothing here proves RH.
  conjecture1_proved = False.
-/
import Mathlib

open Complex ComplexConjugate Filter Topology

namespace DBN

/-! ### The vertical-shift average `T_δ` -/

/-- The vertical-shift average `(T_δ f)(z) = (f(z + iδ) + f(z − iδ)) / 2`. -/
noncomputable def shiftAvg (δ : ℝ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (f (z + I * δ) + f (z - I * δ)) / 2

/-- `T_δ` preserves entire functions. -/
lemma differentiable_shiftAvg {f : ℂ → ℂ} (hf : Differentiable ℂ f) (δ : ℝ) :
    Differentiable ℂ (shiftAvg δ f) := by
  have h1 : Differentiable ℂ (fun z : ℂ ↦ f (z + I * δ)) :=
    hf.comp (differentiable_id.add_const _)
  have h2 : Differentiable ℂ (fun z : ℂ ↦ f (z - I * δ)) :=
    hf.comp (differentiable_id.sub_const _)
  exact (h1.add h2).div_const 2

/-- `T_δ` preserves even functions. -/
lemma shiftAvg_neg {f : ℂ → ℂ} (hf : ∀ z, f (-z) = f z) (δ : ℝ) (z : ℂ) :
    shiftAvg δ f (-z) = shiftAvg δ f z := by
  unfold shiftAvg
  rw [show -z + I * δ = -(z - I * δ) by ring, show -z - I * δ = -(z + I * δ) by ring, hf, hf,
    add_comm]

/-- `T_δ` preserves real functions (`f (conj z) = conj (f z)`). -/
lemma shiftAvg_conj {f : ℂ → ℂ} (hf : ∀ z, f (conj z) = conj (f z)) (δ : ℝ) (z : ℂ) :
    shiftAvg δ f (conj z) = conj (shiftAvg δ f z) := by
  unfold shiftAvg
  have e1 : conj z + I * δ = conj (z - I * δ) := by
    rw [map_sub, map_mul, Complex.conj_I, Complex.conj_ofReal]; ring
  have e2 : conj z - I * δ = conj (z + I * δ) := by
    rw [map_add, map_mul, Complex.conj_I, Complex.conj_ofReal]; ring
  rw [e1, e2, hf, hf, map_div₀, map_add, add_comm]
  congr 1
  exact (Complex.conj_ofNat 2).symm

/-! ### Partial products -/

/-- If one factor of a product sequence vanishes, its limit vanishes. -/
lemma eq_zero_of_tendsto_prod_of_eq_zero {R : Type*} [CommMonoidWithZero R] [TopologicalSpace R]
    [T2Space R] {X : R} {g : ℕ → R} {L : R}
    (h : Tendsto (fun n : ℕ ↦ X * ∏ k ∈ Finset.range n, g k) atTop (𝓝 L)) {k₀ : ℕ}
    (hk₀ : g k₀ = 0) : L = 0 := by
  have hev : (fun _ : ℕ ↦ (0 : R)) =ᶠ[atTop] fun n ↦ X * ∏ k ∈ Finset.range n, g k := by
    filter_upwards [eventually_gt_atTop k₀] with n hn
    rw [Finset.prod_eq_zero (Finset.mem_range.mpr hn) hk₀, mul_zero]
  exact tendsto_nhds_unique h (tendsto_const_nhds.congr' hev)

/-- A product sequence with nonzero limit has no zero term. -/
lemma prod_ne_zero_of_tendsto {R : Type*} [CommMonoidWithZero R] [NoZeroDivisors R] [Nontrivial R]
    [TopologicalSpace R] [T2Space R] {X : R} {g : ℕ → R} {L : R}
    (h : Tendsto (fun n : ℕ ↦ X * ∏ k ∈ Finset.range n, g k) atTop (𝓝 L)) (hL : L ≠ 0)
    (n : ℕ) : X * ∏ k ∈ Finset.range n, g k ≠ 0 := by
  intro h0
  rcases mul_eq_zero.mp h0 with hX | hP
  · apply hL
    refine tendsto_nhds_unique h ?_
    simp only [hX, zero_mul]
    exact tendsto_const_nhds
  · obtain ⟨k, -, hgk⟩ := Finset.prod_eq_zero_iff.mp hP
    exact hL (eq_zero_of_tendsto_prod_of_eq_zero h hgk)

/-! ### Abstract even Hadamard data -/

/-- **Abstract even Hadamard data** for `f : ℂ → ℂ`: a constant `c`, a multiplicity `m` of the
zero at the origin (of order `2m`), and reciprocal zeros `τ k` (one per `±` pair, with
multiplicity; `τ k = 0` encodes a trivial factor `1`), such that the partial products
`c z^{2m} ∏_{k<n} (1 − z² τ_k²)` converge pointwise to `f z`.

This is the shape the Hadamard factorisation of an even entire function of order `< 2` produces
(memo section 2.4; obligation L3e), weakened to pointwise convergence along `Finset.range`, which
is all the step lemma uses.  No summability of `τ` and no growth bound are recorded: they are
L3's business, not L4's. -/
structure EvenHadamardData (f : ℂ → ℂ) where
  /-- the leading constant -/
  c : ℂ
  /-- half the order of the zero of `f` at the origin -/
  m : ℕ
  /-- reciprocals of the nonzero zeros, one per `±` pair, with multiplicity (`0` = trivial) -/
  τ : ℕ → ℂ
  /-- the partial products converge pointwise to `f` -/
  tendsto_prod : ∀ z : ℂ,
    Tendsto (fun n : ℕ ↦ c * z ^ (2 * m) * ∏ k ∈ Finset.range n, (1 - z ^ 2 * τ k ^ 2))
      atTop (𝓝 (f z))

namespace EvenHadamardData

variable {f : ℂ → ℂ} (D : EvenHadamardData f)
include D

/-- A function with even Hadamard data is even. -/
lemma even (z : ℂ) : f (-z) = f z := by
  have h := D.tendsto_prod z
  have hfun : (fun n : ℕ ↦ D.c * (-z) ^ (2 * D.m) * ∏ k ∈ Finset.range n, (1 - (-z) ^ 2 * D.τ k ^ 2))
      = fun n : ℕ ↦ D.c * z ^ (2 * D.m) * ∏ k ∈ Finset.range n, (1 - z ^ 2 * D.τ k ^ 2) := by
    funext n
    rw [(even_two_mul D.m).neg_pow, neg_sq]
  exact tendsto_nhds_unique (D.tendsto_prod (-z)) (hfun ▸ h)

/-- The zeros of the factors are zeros of `f`. -/
lemma eq_zero_of_factor {z : ℂ} {k : ℕ} (hk : 1 - z ^ 2 * D.τ k ^ 2 = 0) : f z = 0 :=
  eq_zero_of_tendsto_prod_of_eq_zero (D.tendsto_prod z) hk

/-- `τ k⁻¹` is a zero of `f` when `τ k ≠ 0`. -/
lemma apply_inv_eq_zero {k : ℕ} (hk : D.τ k ≠ 0) : f (D.τ k)⁻¹ = 0 := by
  apply D.eq_zero_of_factor (k := k)
  rw [inv_pow, inv_mul_cancel₀ (pow_ne_zero 2 hk), sub_self]

/-- The degenerate case: no zero at the origin and only trivial factors means `f` is constant. -/
lemma eq_const (hm : D.m = 0) (hτ : ∀ k, D.τ k = 0) (z : ℂ) : f z = D.c := by
  refine tendsto_nhds_unique (D.tendsto_prod z) ?_
  simp only [hm, hτ, mul_zero, pow_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, mul_one, sub_zero, Finset.prod_const_one]
  exact tendsto_const_nhds

/-- For a REAL function, reality hands over the conjugate expansion for free:
`f z = lim conj c · z^{2m} ∏ (1 − z² conj(τ_k)²)`. -/
lemma tendsto_prod_conj (hreal : ∀ z, f (conj z) = conj (f z)) (z : ℂ) :
    Tendsto (fun n : ℕ ↦ conj D.c * z ^ (2 * D.m) *
      ∏ k ∈ Finset.range n, (1 - z ^ 2 * conj (D.τ k) ^ 2)) atTop (𝓝 (f z)) := by
  have h := (Complex.continuous_conj.tendsto _).comp (D.tendsto_prod (conj z))
  rw [hreal, Complex.conj_conj] at h
  refine h.congr fun n ↦ ?_
  simp only [Function.comp_apply, map_mul, map_pow, map_prod, map_sub, map_one,
    Complex.conj_conj]

/-- A zero of a conjugate factor is also a zero of `f` (real case). -/
lemma eq_zero_of_conj_factor (hreal : ∀ z, f (conj z) = conj (f z)) {z : ℂ} {k : ℕ}
    (hk : 1 - z ^ 2 * conj (D.τ k) ^ 2 = 0) : f z = 0 :=
  eq_zero_of_tendsto_prod_of_eq_zero (D.tendsto_prod_conj hreal z) hk

end EvenHadamardData

/-- **Adapter for the Hadamard factorisation (L3)**: even Hadamard data from an unconditional
product identity `f z = c z^{2m} P z` with `HasProd (fun k ↦ 1 − z² τ_k²) (P z)` for every `z`
(the form `hasProdLocallyUniformlyOn_one_add` yields pointwise). -/
noncomputable def EvenHadamardData.ofHasProd {f : ℂ → ℂ} (c : ℂ) (m : ℕ) (τ : ℕ → ℂ)
    (P : ℂ → ℂ) (hP : ∀ z, HasProd (fun k ↦ 1 - z ^ 2 * τ k ^ 2) (P z))
    (hf : ∀ z, f z = c * z ^ (2 * m) * P z) : EvenHadamardData f where
  c := c
  m := m
  τ := τ
  tendsto_prod z := by
    rw [hf z]
    exact ((hP z).tendsto_prod_nat).const_mul (c * z ^ (2 * m))

/-- **Adapter for L3, `tprod` form**: even Hadamard data from
`f z = c z^{2m} ∏' k, (1 − z² τ_k²)` with multipliable factors. -/
noncomputable def EvenHadamardData.ofMultipliable {f : ℂ → ℂ} (c : ℂ) (m : ℕ) (τ : ℕ → ℂ)
    (hτ : ∀ z, Multipliable (fun k ↦ 1 - z ^ 2 * τ k ^ 2))
    (hf : ∀ z, f z = c * z ^ (2 * m) * ∏' k, (1 - z ^ 2 * τ k ^ 2)) : EvenHadamardData f :=
  EvenHadamardData.ofHasProd c m τ _ (fun z ↦ (hτ z).hasProd) hf

/-! ### The factor modulus `Q_τ` and the conjugate-pair parabola -/

/-- The factor modulus `Q_τ(z) = ‖1 − z²τ²‖ · ‖1 − z² conj(τ)²‖`. -/
noncomputable def hadQ (τ z : ℂ) : ℝ := ‖1 - z ^ 2 * τ ^ 2‖ * ‖1 - z ^ 2 * conj τ ^ 2‖

lemma hadQ_nonneg (τ z : ℂ) : 0 ≤ hadQ τ z := by
  unfold hadQ; positivity

lemma hadQ_zero (z : ℂ) : hadQ 0 z = 1 := by
  simp [hadQ]

/-- The squared modulus of the partial products, from the product expansion and its conjugate. -/
lemma EvenHadamardData.tendsto_sq_norm {f : ℂ → ℂ} (D : EvenHadamardData f)
    (hreal : ∀ z, f (conj z) = conj (f z)) (z : ℂ) :
    Tendsto (fun n : ℕ ↦ ‖D.c‖ ^ 2 * ‖z‖ ^ (4 * D.m) * ∏ k ∈ Finset.range n, hadQ (D.τ k) z)
      atTop (𝓝 (‖f z‖ ^ 2)) := by
  have h := ((D.tendsto_prod z).norm).mul ((D.tendsto_prod_conj hreal z).norm)
  rw [← sq] at h
  refine h.congr fun n ↦ ?_
  simp only [norm_mul, norm_pow, norm_prod, Complex.norm_conj, hadQ, Finset.prod_mul_distrib]
  ring

/-- **The conjugate-pair parabola.**  `(‖z − σ‖ ‖z − conj σ‖)² = (a² + Y² + q²)² − 4 Y² q²`
with `a = Re z − Re σ`, `Y = Im z`, `q = Im σ`. -/
lemma sq_norm_sub_mul_norm_sub_conj (z σ : ℂ) :
    (‖z - σ‖ * ‖z - conj σ‖) ^ 2
      = ((z.re - σ.re) ^ 2 + z.im ^ 2 + σ.im ^ 2) ^ 2 - 4 * z.im ^ 2 * σ.im ^ 2 := by
  rw [mul_pow, Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.conj_re, Complex.conj_im]
  ring

/-- **One conjugate pair grows under the upward shift.**  For `y = Im w > 0`, `δ > 0` and
`(Im σ)² < y² + δ²`, the pair modulus `‖z − σ‖ ‖z − conj σ‖` is strictly larger at `w + iδ`
than at `w − iδ`: the difference of squares is `8 y δ (y² + δ² + a² − q²)`. -/
lemma pair_lt {w σ : ℂ} {δ : ℝ} (hy : 0 < w.im) (hδ : 0 < δ)
    (hσ : σ.im ^ 2 < w.im ^ 2 + δ ^ 2) :
    ‖(w - I * δ) - σ‖ * ‖(w - I * δ) - conj σ‖ < ‖(w + I * δ) - σ‖ * ‖(w + I * δ) - conj σ‖ := by
  apply lt_of_pow_lt_pow_left₀ 2 (by positivity)
  rw [sq_norm_sub_mul_norm_sub_conj, sq_norm_sub_mul_norm_sub_conj]
  have hre1 : (w - I * δ).re = w.re := by simp
  have hre2 : (w + I * δ).re = w.re := by simp
  have him1 : (w - I * δ).im = w.im - δ := by simp
  have him2 : (w + I * δ).im = w.im + δ := by simp
  rw [hre1, hre2, him1, him2]
  set a := w.re - σ.re
  set q := σ.im
  set y := w.im
  have key : (a ^ 2 + (y + δ) ^ 2 + q ^ 2) ^ 2 - 4 * (y + δ) ^ 2 * q ^ 2
      - ((a ^ 2 + (y - δ) ^ 2 + q ^ 2) ^ 2 - 4 * (y - δ) ^ 2 * q ^ 2)
      = 8 * y * δ * (y ^ 2 + δ ^ 2 + a ^ 2 - q ^ 2) := by ring
  have hpos : 0 < 8 * y * δ * (y ^ 2 + δ ^ 2 + a ^ 2 - q ^ 2) := by
    have h1 : 0 < y ^ 2 + δ ^ 2 + a ^ 2 - q ^ 2 := by nlinarith [sq_nonneg a]
    positivity
  linarith

/-- `Q_τ` in terms of the zero `ρ = τ⁻¹`: two conjugate pairs, centred at `± Re ρ`. -/
lemma hadQ_eq {τ : ℂ} (hτ : τ ≠ 0) (z : ℂ) :
    hadQ τ z = ‖τ‖ ^ 4 * ((‖z - τ⁻¹‖ * ‖z - conj (τ⁻¹)‖)
      * (‖z - (-τ⁻¹)‖ * ‖z - conj (-τ⁻¹)‖)) := by
  have hc : conj τ ≠ 0 := (map_ne_zero _).mpr hτ
  have h1 : 1 - z ^ 2 * τ ^ 2 = -(τ ^ 2) * ((z - τ⁻¹) * (z - (-τ⁻¹))) := by
    field_simp
    ring
  have h2 : 1 - z ^ 2 * conj τ ^ 2 = -(conj τ ^ 2) * ((z - conj (τ⁻¹)) * (z - conj (-τ⁻¹))) := by
    rw [map_neg, map_inv₀]
    field_simp
    ring
  unfold hadQ
  rw [h1, h2]
  simp only [norm_mul, norm_neg, norm_pow, Complex.norm_conj]
  ring

/-- **Each nontrivial factor grows strictly under the upward shift.** -/
lemma hadQ_lt {τ w : ℂ} {δ : ℝ} (hτ : τ ≠ 0) (hy : 0 < w.im) (hδ : 0 < δ)
    (hρ : (τ⁻¹).im ^ 2 < w.im ^ 2 + δ ^ 2) : hadQ τ (w - I * δ) < hadQ τ (w + I * δ) := by
  rw [hadQ_eq hτ, hadQ_eq hτ]
  have hp1 := pair_lt (σ := τ⁻¹) hy hδ hρ
  have hp2 := pair_lt (σ := -τ⁻¹) hy hδ (by rwa [Complex.neg_im, neg_sq])
  have hτ4 : 0 < ‖τ‖ ^ 4 := by positivity
  exact mul_lt_mul_of_pos_left (mul_lt_mul'' hp1 hp2 (by positivity) (by positivity)) hτ4

/-- The upward shift moves away from the real axis: `‖w − iδ‖ < ‖w + iδ‖` for `Im w > 0`. -/
lemma norm_sub_lt_norm_add {w : ℂ} {δ : ℝ} (hy : 0 < w.im) (hδ : 0 < δ) :
    ‖w - I * δ‖ < ‖w + I * δ‖ := by
  apply lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _)
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.add_re, Complex.sub_im, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  nlinarith [mul_pos hy hδ]

/-! ### The step lemma -/

/-- `max (max a 0 − d) 0 = max (a − d) 0` for `d ≥ 0`: strips compose additively in `Im²`. -/
lemma max_sub_max_zero {a d : ℝ} (hd : 0 ≤ d) : max (max a 0 - d) 0 = max (a - d) 0 := by
  rcases le_total a 0 with ha | ha
  · rw [max_eq_right ha, max_eq_right (by linarith), max_eq_right (by linarith)]
  · rw [max_eq_left ha]

namespace EvenHadamardData

variable {f : ℂ → ℂ} (D : EvenHadamardData f)
include D

/-- **The main inequality.**  For real `f` with even Hadamard data and zeros in `(Im z)² ≤ Δ2`,
not constant (`m ≠ 0` or some `τ k ≠ 0`), and `w` with `Im w > 0`, `Δ2 < (Im w)² + δ²`,
`f(w − iδ) ≠ 0`: `‖f(w − iδ)‖ < ‖f(w + iδ)‖`. -/
theorem norm_lt_norm (hreal : ∀ z, f (conj z) = conj (f z)) {Δ2 δ : ℝ} (hδ : 0 < δ)
    (hzeros : ∀ z, f z = 0 → z.im ^ 2 ≤ Δ2) {w : ℂ} (hy : 0 < w.im)
    (hΔ : Δ2 < w.im ^ 2 + δ ^ 2) (hne : f (w - I * δ) ≠ 0) (hnd : D.m ≠ 0 ∨ ∃ k, D.τ k ≠ 0) :
    ‖f (w - I * δ)‖ < ‖f (w + I * δ)‖ := by
  set zm := w - I * δ with hzm
  set zp := w + I * δ with hzp
  -- the squared-modulus partial products at `zp` (A) and `zm` (B)
  set X : ℝ := ‖D.c‖ ^ 2 * ‖zp‖ ^ (4 * D.m) with hX
  set Y : ℝ := ‖D.c‖ ^ 2 * ‖zm‖ ^ (4 * D.m) with hY
  set A : ℕ → ℝ := fun n ↦ X * ∏ k ∈ Finset.range n, hadQ (D.τ k) zp with hA
  set B : ℕ → ℝ := fun n ↦ Y * ∏ k ∈ Finset.range n, hadQ (D.τ k) zm with hB
  have hAlim : Tendsto A atTop (𝓝 (‖f zp‖ ^ 2)) := D.tendsto_sq_norm hreal zp
  have hBlim : Tendsto B atTop (𝓝 (‖f zm‖ ^ 2)) := D.tendsto_sq_norm hreal zm
  have hfm : 0 < ‖f zm‖ ^ 2 := by positivity
  have hBne : ∀ n, B n ≠ 0 := prod_ne_zero_of_tendsto hBlim hfm.ne'
  -- consequences of `B n ≠ 0`
  have hY0 : Y ≠ 0 := by
    have := hBne 0
    simpa [hB] using this
  have hQm : ∀ k, 0 < hadQ (D.τ k) zm := by
    intro k
    refine lt_of_le_of_ne (hadQ_nonneg _ _) (Ne.symm fun h0 ↦ hBne (k + 1) ?_)
    simp only [hB, Finset.prod_range_succ, h0, mul_zero]
  -- each factor grows (weakly), nontrivial ones strictly
  have hQlt : ∀ k, D.τ k ≠ 0 → hadQ (D.τ k) zm < hadQ (D.τ k) zp := by
    intro k hk
    have hz := hzeros _ (D.apply_inv_eq_zero hk)
    exact hadQ_lt hk hy hδ (lt_of_le_of_lt hz hΔ)
  have hQle : ∀ k, hadQ (D.τ k) zm ≤ hadQ (D.τ k) zp := by
    intro k
    by_cases hk : D.τ k = 0
    · rw [hk, hadQ_zero, hadQ_zero]
    · exact (hQlt k hk).le
  -- the ratio sequence
  set r : ℕ → ℝ := fun n ↦ A n / B n with hr
  have hr_succ : ∀ n, r (n + 1) = r n * (hadQ (D.τ n) zp / hadQ (D.τ n) zm) := by
    intro n
    simp only [hr, hA, hB, Finset.prod_range_succ]
    rw [← mul_assoc, ← mul_assoc, mul_div_mul_comm]
  have hratio_ge : ∀ n, 1 ≤ hadQ (D.τ n) zp / hadQ (D.τ n) zm := fun n ↦
    (one_le_div (hQm n)).mpr (hQle n)
  have hr0 : 1 ≤ r 0 := by
    have hYpos : 0 < Y := lt_of_le_of_ne (by positivity) (Ne.symm hY0)
    simp only [hr, hA, hB, Finset.range_zero, Finset.prod_empty, mul_one]
    rw [one_le_div hYpos]
    have hn : ‖zm‖ ≤ ‖zp‖ := (norm_sub_lt_norm_add hy hδ).le
    have := pow_le_pow_left₀ (norm_nonneg zm) hn (4 * D.m)
    simp only [hX, hY]
    gcongr
  have hr_pos : ∀ n, 0 < r n := by
    intro n
    induction n with
    | zero => linarith
    | succ n ih =>
      rw [hr_succ]
      exact mul_pos ih (lt_of_lt_of_le one_pos (hratio_ge n))
  have hmono : Monotone r := by
    refine monotone_nat_of_le_succ fun n ↦ ?_
    rw [hr_succ]
    exact le_mul_of_one_le_right (hr_pos n).le (hratio_ge n)
  have hrlim : Tendsto r atTop (𝓝 (‖f zp‖ ^ 2 / ‖f zm‖ ^ 2)) := hAlim.div hBlim hfm.ne'
  have hle_lim : ∀ n, r n ≤ ‖f zp‖ ^ 2 / ‖f zm‖ ^ 2 := fun n ↦ hmono.ge_of_tendsto hrlim n
  -- some term of the ratio sequence is strictly above `1`
  have hstrict : ∃ n, 1 < r n := by
    rcases hnd with hm | ⟨k, hk⟩
    · refine ⟨0, ?_⟩
      have hYpos : 0 < Y := lt_of_le_of_ne (by positivity) (Ne.symm hY0)
      simp only [hr, hA, hB, Finset.range_zero, Finset.prod_empty, mul_one]
      rw [one_lt_div hYpos]
      have hc : 0 < ‖D.c‖ ^ 2 := by
        rcases eq_or_ne ‖D.c‖ 0 with h | h
        · exfalso; apply hY0; simp [hY, h]
        · positivity
      have hzm0 : ‖zm‖ ≠ 0 := by
        intro h
        apply hY0
        simp [hY, h, hm]
      have hn := norm_sub_lt_norm_add hy hδ
      have h4 : ‖zm‖ ^ (4 * D.m) < ‖zp‖ ^ (4 * D.m) :=
        pow_lt_pow_left₀ hn (norm_nonneg _) (by omega)
      simp only [hX, hY]
      exact mul_lt_mul_of_pos_left h4 hc
    · refine ⟨k + 1, ?_⟩
      rw [hr_succ]
      have h1 : 1 ≤ r k := le_trans hr0 (hmono (Nat.zero_le k))
      have h2 : 1 < hadQ (D.τ k) zp / hadQ (D.τ k) zm :=
        (one_lt_div (hQm k)).mpr (hQlt k hk)
      nlinarith
  obtain ⟨n, hn⟩ := hstrict
  have hlim1 : 1 < ‖f zp‖ ^ 2 / ‖f zm‖ ^ 2 := lt_of_lt_of_le hn (hle_lim n)
  rw [one_lt_div hfm] at hlim1
  exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) hlim1

/-- **The discrete de Bruijn step (memo section 2.2).**  If `f` is real, carries even Hadamard
data, and all zeros of `f` satisfy `(Im z)² ≤ Δ2`, then for `δ > 0` every zero `w` of
`T_δ f = shiftAvg δ f` satisfies `(Im w)² ≤ max (Δ2 − δ²) 0`. -/
theorem shiftAvg_zero_im_sq_le (hreal : ∀ z, f (conj z) = conj (f z)) {Δ2 δ : ℝ} (hδ : 0 < δ)
    (hzeros : ∀ z, f z = 0 → z.im ^ 2 ≤ Δ2) {w : ℂ} (hw : shiftAvg δ f w = 0) :
    w.im ^ 2 ≤ max (Δ2 - δ ^ 2) 0 := by
  by_contra hlt
  push Not at hlt
  have h1 : Δ2 - δ ^ 2 < w.im ^ 2 := lt_of_le_of_lt (le_max_left _ _) hlt
  have h2 : 0 < w.im ^ 2 := lt_of_le_of_lt (le_max_right _ _) hlt
  -- the upper half-plane case
  have key : ∀ v : ℂ, 0 < v.im → Δ2 < v.im ^ 2 + δ ^ 2 → shiftAvg δ f v ≠ 0 := by
    intro v hv hΔ hsum
    unfold shiftAvg at hsum
    have hsum' : f (v + I * δ) = -f (v - I * δ) := by linear_combination (2 : ℂ) * hsum
    by_cases hm : f (v - I * δ) = 0
    · have hp : f (v + I * δ) = 0 := by rw [hsum', hm, neg_zero]
      have hz := hzeros _ hp
      have him : (v + I * δ).im = v.im + δ := by simp
      rw [him] at hz
      nlinarith [mul_pos hv hδ]
    · by_cases hdeg : D.m = 0 ∧ ∀ k, D.τ k = 0
      · have hc1 := D.eq_const hdeg.1 hdeg.2 (v + I * δ)
        have hc2 := D.eq_const hdeg.1 hdeg.2 (v - I * δ)
        rw [hc1, hc2] at hsum'
        apply hm
        rw [hc2]
        linear_combination hsum' / 2
      · have hnd : D.m ≠ 0 ∨ ∃ k, D.τ k ≠ 0 := by
          by_contra h
          push Not at h
          exact hdeg ⟨h.1, h.2⟩
        have hlt' := D.norm_lt_norm hreal hδ hzeros hv hΔ hm hnd
        rw [hsum', norm_neg] at hlt'
        exact lt_irrefl _ hlt'
  have hne : w.im ≠ 0 := by
    intro h
    rw [h] at h2
    norm_num at h2
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · -- lower half-plane: reflect through the origin (`T_δ f` is even)
    have hw' : shiftAvg δ f (-w) = 0 := by rw [shiftAvg_neg D.even]; exact hw
    refine key (-w) (by rw [Complex.neg_im]; linarith) ?_ hw'
    rw [Complex.neg_im, neg_sq]
    linarith
  · exact key w hpos (by linarith) hw

/-- **Discrete heat-flow monotonicity** (the step lemma with `Δ2 = 0`, memo section 2.2, last
paragraph): if a real `f` with even Hadamard data has only real zeros, so has `T_δ f`. -/
theorem shiftAvg_real_zeros (hreal : ∀ z, f (conj z) = conj (f z)) {δ : ℝ} (hδ : 0 < δ)
    (hzeros : ∀ z, f z = 0 → z.im = 0) {w : ℂ} (hw : shiftAvg δ f w = 0) : w.im = 0 := by
  have h := D.shiftAvg_zero_im_sq_le hreal hδ (Δ2 := 0)
    (fun z hz ↦ by rw [hzeros z hz]; norm_num) hw
  rw [max_eq_right (by nlinarith [sq_nonneg δ] : (0 : ℝ) - δ ^ 2 ≤ 0)] at h
  exact (pow_eq_zero_iff two_ne_zero).mp (le_antisymm h (sq_nonneg _))

end EvenHadamardData

/-- **Iterated step.**  Let `F 0, F 1, …` satisfy `F (k+1) = T_δ (F k)` with `δ > 0`, each `F k`
real and carrying even Hadamard data, and let the zeros of `F 0` satisfy `(Im z)² ≤ Δ2`.  Then the
zeros of `F N` satisfy `(Im z)² ≤ max (Δ2 − N δ²) 0`. -/
theorem zero_im_sq_le_of_shiftAvg_iterate {F : ℕ → ℂ → ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hsucc : ∀ k, F (k + 1) = shiftAvg δ (F k))
    (hdata : ∀ k, Nonempty (EvenHadamardData (F k)))
    (hreal : ∀ k z, F k (conj z) = conj (F k z))
    {Δ2 : ℝ} (h0 : ∀ z, F 0 z = 0 → z.im ^ 2 ≤ Δ2) :
    ∀ N : ℕ, ∀ z, F N z = 0 → z.im ^ 2 ≤ max (Δ2 - N * δ ^ 2) 0 := by
  intro N
  induction N with
  | zero =>
    intro z hz
    simp only [Nat.cast_zero, zero_mul, sub_zero]
    exact le_max_of_le_left (h0 z hz)
  | succ N ih =>
    intro z hz
    obtain ⟨D⟩ := hdata N
    rw [hsucc] at hz
    have h := D.shiftAvg_zero_im_sq_le (hreal N) hδ ih hz
    rw [max_sub_max_zero (sq_nonneg δ)] at h
    calc z.im ^ 2 ≤ max (Δ2 - N * δ ^ 2 - δ ^ 2) 0 := h
      _ = max (Δ2 - ((N + 1 : ℕ) : ℝ) * δ ^ 2) 0 := by push_cast; ring_nf

end DBN
