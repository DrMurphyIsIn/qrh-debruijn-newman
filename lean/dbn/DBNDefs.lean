/-
  DBNDefs -- Route C (de Bruijn-Newman) foundations, milestone C2 of
  telperion/docs/RH_ROUTES_ROADMAP_2026-09-16.md section 4.

  Conventions (Polymath15 arXiv:1904.12438 section 1, Rodgers-Tao Forum Math. Pi 8 (2020) e6):

    Φ(u) := ∑_{n ≥ 1} (2π²n⁴e^{9u} − 3πn²e^{5u}) exp(−πn²e^{4u}),
    H_t(z) := ∫_0^∞ e^{tu²} Φ(u) cos(zu) du,

  so that (classically, Titchmarsh 10.1 / Polymath15 eq. (3)) H_0(z) = (1/8) ξ(1/2 + iz/2) with
  ξ(s) = (1/2) s (s−1) π^{−s/2} Γ(s/2) ζ(s).  That representation theorem is NOT proved here;
  it is registered as the registry statement RH.dbn_H0_eq_xi.  Λ (the de Bruijn-Newman constant)
  is deliberately NOT defined in this module (sInf ill-posedness trap: it is only well defined
  after C3 shows the real-zero set {t | all zeros of H_t real} is a non-empty up-set).

  What IS proved here (axiom-clean, see AxiomGuardDBN.lean):
    * summability of the Φ series and of the theta-moment series for every u,
    * the theta-moment functions are differentiable with the termwise derivative,
    * the theta functional equation for the zeroth moment (from Mathlib's
      `jacobiTheta₂_functional_equation`), differentiated twice,
    * Φ is EVEN: Φ(−u) = Φ(u) -- a theorem, not an assumption,
    * Φ is continuous and super-exponentially decaying,
    * the H_t integrand is integrable for every t and z,
    * H_t(z) is real for real z, and H_t(−z) = H_t(z),
    * the bridge from the pinned LiCriterion.riemannXi vocabulary to Mathlib's completedRiemannZeta.

  conjecture1_proved = False.  Nothing here claims RH or any bound on Λ.
-/
import Mathlib
import Lc.LiCriterion.Basic

open Real MeasureTheory Set Filter Topology

namespace DBN

/-! ### The theta moments `thetaMoment k u = ∑_{n ∈ ℤ} (n²)^k exp(−π n² e^{4u})` -/

/-- The `k`-th theta moment in the Polymath15 variable `u` (`x = e^{4u}`):
`∑_{n ∈ ℤ} (n²)^k exp(−π n² e^{4u})`.  `thetaMoment 0 u = θ(i e^{4u})` is the Jacobi theta value. -/
noncomputable def thetaMoment (k : ℕ) (u : ℝ) : ℝ :=
  ∑' n : ℤ, ((n : ℝ) ^ 2) ^ k * Real.exp (-Real.pi * (n : ℝ) ^ 2 * Real.exp (4 * u))

/-- Summability of the theta-moment series for any `x > 0` (from Mathlib's uniform bound
`summable_pow_mul_jacobiTheta₂_term_bound`). -/
lemma summable_thetaTerm (k : ℕ) {x : ℝ} (hx : 0 < x) :
    Summable (fun n : ℤ ↦ ((n : ℝ) ^ 2) ^ k * Real.exp (-π * (n : ℝ) ^ 2 * x)) := by
  have := summable_pow_mul_jacobiTheta₂_term_bound 0 hx (2 * k)
  refine this.congr fun n ↦ ?_
  rw [Int.cast_abs, pow_mul, sq_abs]
  congr 1
  ring_nf

lemma summable_thetaMoment (k : ℕ) (u : ℝ) :
    Summable (fun n : ℤ ↦ ((n : ℝ) ^ 2) ^ k * Real.exp (-π * (n : ℝ) ^ 2 * Real.exp (4 * u))) :=
  summable_thetaTerm k (Real.exp_pos _)

/-- Termwise differentiation of the theta moments: `(thetaMoment k)' = −4π e^{4u} thetaMoment (k+1)`. -/
lemma hasDerivAt_thetaMoment (k : ℕ) (u : ℝ) :
    HasDerivAt (thetaMoment k) (-4 * π * Real.exp (4 * u) * thetaMoment (k + 1) u) u := by
  have hterm : ∀ (n : ℤ) (v : ℝ), HasDerivAt
      (fun v ↦ ((n : ℝ) ^ 2) ^ k * Real.exp (-π * (n : ℝ) ^ 2 * Real.exp (4 * v)))
      (((n : ℝ) ^ 2) ^ k * (Real.exp (-π * (n : ℝ) ^ 2 * Real.exp (4 * v)) *
        (-π * (n : ℝ) ^ 2 * (Real.exp (4 * v) * 4)))) v := by
    intro n v
    have h1 : HasDerivAt (fun v : ℝ ↦ 4 * v) 4 v := by
      simpa using (hasDerivAt_id v).const_mul (4 : ℝ)
    exact ((h1.exp.const_mul (-π * (n : ℝ) ^ 2)).exp).const_mul _
  set T : ℝ := Real.exp (4 * (u - 1)) with hT
  have hTpos : 0 < T := Real.exp_pos _
  have hsum := (summable_thetaTerm (k + 1) hTpos).mul_left (4 * π * Real.exp (4 * (u + 1)))
  have key := hasDerivAt_tsum_of_isPreconnected
    (u := fun n : ℤ ↦ 4 * π * Real.exp (4 * (u + 1)) *
      (((n : ℝ) ^ 2) ^ (k + 1) * Real.exp (-π * (n : ℝ) ^ 2 * T)))
    (t := Set.Ioo (u - 1) (u + 1)) hsum isOpen_Ioo isPreconnected_Ioo
    (g := fun n v ↦ ((n : ℝ) ^ 2) ^ k * Real.exp (-π * (n : ℝ) ^ 2 * Real.exp (4 * v)))
    (g' := fun n v ↦ ((n : ℝ) ^ 2) ^ k * (Real.exp (-π * (n : ℝ) ^ 2 * Real.exp (4 * v)) *
        (-π * (n : ℝ) ^ 2 * (Real.exp (4 * v) * 4))))
    (fun n v _ ↦ hterm n v) ?_ (y₀ := u) ⟨by linarith, by linarith⟩
    (summable_thetaMoment k u) (y := u) ⟨by linarith, by linarith⟩
  · refine key.congr_deriv ?_
    unfold thetaMoment
    rw [← tsum_mul_left]
    exact tsum_congr fun n ↦ by ring
  · intro n v hv
    have hv1 : Real.exp (4 * v) ≤ Real.exp (4 * (u + 1)) := Real.exp_le_exp.mpr (by linarith [hv.2])
    have hv2 : Real.exp (-π * (n : ℝ) ^ 2 * Real.exp (4 * v)) ≤ Real.exp (-π * (n : ℝ) ^ 2 * T) := by
      apply Real.exp_le_exp.mpr
      have : T ≤ Real.exp (4 * v) := Real.exp_le_exp.mpr (by linarith [hv.1])
      nlinarith [Real.pi_pos, sq_nonneg (n : ℝ), mul_nonneg Real.pi_pos.le (sq_nonneg (n : ℝ))]
    have hrw : ((n : ℝ) ^ 2) ^ k * (Real.exp (-π * (n : ℝ) ^ 2 * Real.exp (4 * v)) *
        (-π * (n : ℝ) ^ 2 * (Real.exp (4 * v) * 4)))
        = -(4 * π * Real.exp (4 * v) *
            (((n : ℝ) ^ 2) ^ (k + 1) * Real.exp (-π * (n : ℝ) ^ 2 * Real.exp (4 * v)))) := by ring
    rw [Real.norm_eq_abs, hrw, abs_neg, abs_of_nonneg (by positivity)]
    gcongr

@[fun_prop]
lemma continuous_thetaMoment (k : ℕ) : Continuous (thetaMoment k) :=
  continuous_iff_continuousAt.mpr fun u ↦ (hasDerivAt_thetaMoment k u).continuousAt

/-! ### The theta functional equation for the zeroth moment -/

/-- The zeroth moment is the Jacobi theta value `θ(i e^{4u}) = jacobiTheta₂ 0 (i e^{4u})`. -/
lemma ofReal_thetaMoment_zero (u : ℝ) :
    ((thetaMoment 0 u : ℝ) : ℂ) = jacobiTheta₂ 0 (Complex.I * (Real.exp (4 * u) : ℂ)) := by
  unfold thetaMoment jacobiTheta₂ jacobiTheta₂_term
  rw [Complex.ofReal_tsum]
  congr 1
  funext n
  rw [pow_zero, one_mul, Complex.ofReal_exp]
  congr 1
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

/-- The theta functional equation in the `u` variable: `θ₀(u) = e^{−2u} θ₀(−u)`
(from `jacobiTheta₂_functional_equation` at `z = 0`, `τ = i e^{4u}`). -/
lemma thetaMoment_zero_fe (u : ℝ) :
    thetaMoment 0 u = Real.exp (-2 * u) * thetaMoment 0 (-u) := by
  have hx : (0 : ℝ) ≤ Real.exp (4 * u) := (Real.exp_pos _).le
  have hx0 : (Real.exp (4 * u) : ℂ) ≠ 0 := by exact_mod_cast (Real.exp_pos _).ne'
  have h := jacobiTheta₂_functional_equation 0 (Complex.I * (Real.exp (4 * u) : ℂ))
  simp only [zero_pow two_ne_zero, mul_zero, zero_div, Complex.exp_zero, mul_one] at h
  have e1 : -Complex.I * (Complex.I * (Real.exp (4 * u) : ℂ)) = (Real.exp (4 * u) : ℂ) := by
    ring_nf; rw [Complex.I_sq]; ring
  have e2 : ((Real.exp (4 * u) : ℝ) : ℂ) ^ (1 / 2 : ℂ) = (Real.exp (2 * u) : ℂ) := by
    have : ((1 / 2 : ℝ) : ℂ) = (1 / 2 : ℂ) := by push_cast; ring
    rw [← this, ← Complex.ofReal_cpow hx (1 / 2 : ℝ), ← Real.exp_mul]
    congr 2; ring
  have e3 : -1 / (Complex.I * (Real.exp (4 * u) : ℂ)) = Complex.I * (Real.exp (4 * -u) : ℂ) := by
    rw [show Real.exp (4 * -u) = (Real.exp (4 * u))⁻¹ by rw [← Real.exp_neg]; ring_nf]
    push_cast
    field_simp
    ring_nf
    rw [Complex.I_sq]
  rw [e1, e2, e3] at h
  apply Complex.ofReal_injective
  push_cast
  rw [ofReal_thetaMoment_zero, ofReal_thetaMoment_zero, h, Complex.ofReal_exp, Complex.ofReal_exp]
  push_cast
  rw [show (-2 : ℂ) * u = -(2 * u) by ring, Complex.exp_neg]
  ring

/-- First derivative of the functional equation. -/
lemma thetaMoment_fe_deriv1 (u : ℝ) :
    -4 * π * Real.exp (4 * u) * thetaMoment 1 u
      = -2 * Real.exp (-2 * u) * thetaMoment 0 (-u)
        + 4 * π * Real.exp (-6 * u) * thetaMoment 1 (-u) := by
  have hL := hasDerivAt_thetaMoment 0 u
  have hfun : thetaMoment 0 = fun v ↦ Real.exp (-2 * v) * thetaMoment 0 (-v) :=
    funext thetaMoment_zero_fe
  rw [hfun] at hL
  have h1 : HasDerivAt (fun v : ℝ ↦ Real.exp (-2 * v)) (Real.exp (-2 * u) * (-2)) u := by
    have := ((hasDerivAt_id u).const_mul (-2 : ℝ)).exp
    simpa using this
  have h2 : HasDerivAt (fun v : ℝ ↦ thetaMoment 0 (-v))
      ((-4 * π * Real.exp (4 * -u) * thetaMoment 1 (-u)) * (-1)) u :=
    (hasDerivAt_thetaMoment 0 (-u)).comp u (hasDerivAt_neg u)
  have hR := h1.mul h2
  have key := hL.unique hR
  have e : Real.exp (-2 * u) * Real.exp (4 * -u) = Real.exp (-6 * u) := by
    rw [← Real.exp_add]; ring_nf
  rw [key]
  linear_combination (4 * π * thetaMoment 1 (-u)) * e

/-- Second derivative of the functional equation. -/
lemma thetaMoment_fe_deriv2 (u : ℝ) :
    -16 * π * Real.exp (4 * u) * thetaMoment 1 u + 16 * π ^ 2 * Real.exp (8 * u) * thetaMoment 2 u
      = 4 * Real.exp (-2 * u) * thetaMoment 0 (-u)
        - 32 * π * Real.exp (-6 * u) * thetaMoment 1 (-u)
        + 16 * π ^ 2 * Real.exp (-10 * u) * thetaMoment 2 (-u) := by
  -- left side as a function of `v`
  have hexp4 : ∀ c : ℝ, ∀ v : ℝ, HasDerivAt (fun v : ℝ ↦ Real.exp (c * v)) (Real.exp (c * v) * c) v := by
    intro c v
    have := ((hasDerivAt_id v).const_mul c).exp
    simpa using this
  have hL : HasDerivAt (fun v ↦ -4 * π * Real.exp (4 * v) * thetaMoment 1 v)
      ((-4 * π * (Real.exp (4 * u) * 4)) * thetaMoment 1 u
        + (-4 * π * Real.exp (4 * u)) * (-4 * π * Real.exp (4 * u) * thetaMoment 2 u)) u :=
    ((hexp4 4 u).const_mul (-4 * π)).mul (hasDerivAt_thetaMoment 1 u)
  have hneg : ∀ k : ℕ, HasDerivAt (fun v : ℝ ↦ thetaMoment k (-v))
      ((-4 * π * Real.exp (4 * -u) * thetaMoment (k + 1) (-u)) * (-1)) u :=
    fun k ↦ (hasDerivAt_thetaMoment k (-u)).comp u (hasDerivAt_neg u)
  have hR : HasDerivAt (fun v ↦ -2 * Real.exp (-2 * v) * thetaMoment 0 (-v)
      + 4 * π * Real.exp (-6 * v) * thetaMoment 1 (-v))
      ((-2 * (Real.exp (-2 * u) * -2)) * thetaMoment 0 (-u)
        + (-2 * Real.exp (-2 * u)) * ((-4 * π * Real.exp (4 * -u) * thetaMoment 1 (-u)) * (-1))
       + ((4 * π * (Real.exp (-6 * u) * -6)) * thetaMoment 1 (-u)
        + (4 * π * Real.exp (-6 * u)) * ((-4 * π * Real.exp (4 * -u) * thetaMoment 2 (-u)) * (-1)))) u :=
    (((hexp4 (-2) u).const_mul (-2)).mul (hneg 0)).add
      (((hexp4 (-6) u).const_mul (4 * π)).mul (hneg 1))
  have hfun : (fun v ↦ -4 * π * Real.exp (4 * v) * thetaMoment 1 v)
      = fun v ↦ -2 * Real.exp (-2 * v) * thetaMoment 0 (-v)
        + 4 * π * Real.exp (-6 * v) * thetaMoment 1 (-v) := funext thetaMoment_fe_deriv1
  rw [hfun] at hL
  have key := hL.unique hR
  have e1 : Real.exp (-2 * u) * Real.exp (4 * -u) = Real.exp (-6 * u) := by
    rw [← Real.exp_add]; ring_nf
  have e2 : Real.exp (-6 * u) * Real.exp (4 * -u) = Real.exp (-10 * u) := by
    rw [← Real.exp_add]; ring_nf
  have e3 : Real.exp (4 * u) * Real.exp (4 * u) = Real.exp (8 * u) := by
    rw [← Real.exp_add]; ring_nf
  linear_combination key - (8 * π * thetaMoment 1 (-u)) * e1
    + (16 * π ^ 2 * thetaMoment 2 (-u)) * e2 - (16 * π ^ 2 * thetaMoment 2 u) * e3

/-! ### The Polymath15 function `Φ` -/

/-- The Polymath15 / Rodgers-Tao function
`Φ(u) = ∑_{n ≥ 1} (2π²n⁴e^{9u} − 3πn²e^{5u}) exp(−πn²e^{4u})` (indexed by `ℕ+`). -/
noncomputable def Φ (u : ℝ) : ℝ :=
  ∑' n : ℕ+, (2 * Real.pi ^ 2 * (n : ℝ) ^ 4 * Real.exp (9 * u)
      - 3 * Real.pi * (n : ℝ) ^ 2 * Real.exp (5 * u))
    * Real.exp (-Real.pi * (n : ℝ) ^ 2 * Real.exp (4 * u))

/-- The positive-integer part of a theta-moment series is summable. -/
lemma summable_thetaTerm_pnat (k : ℕ) {x : ℝ} (hx : 0 < x) :
    Summable (fun n : ℕ+ ↦ ((n : ℝ) ^ 2) ^ k * Real.exp (-π * (n : ℝ) ^ 2 * x)) := by
  have hinj : Function.Injective (fun n : ℕ+ ↦ (n : ℤ)) :=
    fun a b h ↦ by simpa using h
  have := (summable_thetaTerm k hx).comp_injective hinj
  refine this.congr fun n ↦ ?_
  simp

/-- Summability of the `Φ` series for every `u`. -/
lemma summable_Φ_term (u : ℝ) :
    Summable (fun n : ℕ+ ↦
      (2 * π ^ 2 * (n : ℝ) ^ 4 * Real.exp (9 * u) - 3 * π * (n : ℝ) ^ 2 * Real.exp (5 * u))
        * Real.exp (-π * (n : ℝ) ^ 2 * Real.exp (4 * u))) := by
  have h2 := (summable_thetaTerm_pnat 2 (Real.exp_pos (4 * u))).mul_left (2 * π ^ 2 * Real.exp (9 * u))
  have h1 := (summable_thetaTerm_pnat 1 (Real.exp_pos (4 * u))).mul_left (3 * π * Real.exp (5 * u))
  refine (h2.sub h1).congr fun n ↦ ?_
  ring

/-- For `k ≥ 1` the `ℤ`-moment is twice the `ℕ+`-moment (the `n = 0` term vanishes, terms even). -/
lemma thetaMoment_eq_two_mul_pnat (k : ℕ) (hk : 0 < k) (u : ℝ) :
    thetaMoment k u = 2 * ∑' n : ℕ+, ((n : ℝ) ^ 2) ^ k * Real.exp (-π * (n : ℝ) ^ 2 * Real.exp (4 * u)) := by
  unfold thetaMoment
  rw [tsum_int_eq_zero_add_two_mul_tsum_pnat
    (f := fun n : ℤ ↦ ((n : ℝ) ^ 2) ^ k * Real.exp (-π * (n : ℝ) ^ 2 * Real.exp (4 * u)))
    (fun n ↦ by simp) (summable_thetaMoment k u)]
  simp [zero_pow hk.ne']

/-- `Φ` in terms of the theta moments: `Φ(u) = π² e^{9u} θ₂(u) − (3/2) π e^{5u} θ₁(u)`. -/
lemma Φ_eq (u : ℝ) :
    Φ u = π ^ 2 * Real.exp (9 * u) * thetaMoment 2 u - 3 / 2 * π * Real.exp (5 * u) * thetaMoment 1 u := by
  rw [thetaMoment_eq_two_mul_pnat 2 (by norm_num), thetaMoment_eq_two_mul_pnat 1 (by norm_num)]
  unfold Φ
  have h2 := (summable_thetaTerm_pnat 2 (Real.exp_pos (4 * u))).mul_left (2 * π ^ 2 * Real.exp (9 * u))
  have h1 := (summable_thetaTerm_pnat 1 (Real.exp_pos (4 * u))).mul_left (3 * π * Real.exp (5 * u))
  rw [show π ^ 2 * Real.exp (9 * u) * (2 * ∑' n : ℕ+, ((n : ℝ) ^ 2) ^ 2 * Real.exp (-π * (n : ℝ) ^ 2 * Real.exp (4 * u)))
      - 3 / 2 * π * Real.exp (5 * u) * (2 * ∑' n : ℕ+, ((n : ℝ) ^ 2) ^ 1 * Real.exp (-π * (n : ℝ) ^ 2 * Real.exp (4 * u)))
      = (2 * π ^ 2 * Real.exp (9 * u)) * ∑' n : ℕ+, ((n : ℝ) ^ 2) ^ 2 * Real.exp (-π * (n : ℝ) ^ 2 * Real.exp (4 * u))
      - (3 * π * Real.exp (5 * u)) * ∑' n : ℕ+, ((n : ℝ) ^ 2) ^ 1 * Real.exp (-π * (n : ℝ) ^ 2 * Real.exp (4 * u)) by ring]
  rw [← tsum_mul_left, ← tsum_mul_left, ← h2.tsum_sub h1]
  congr 1
  funext n
  ring

/-- **`Φ` is even.**  A theorem (via the theta functional equation), not an assumption. -/
theorem Φ_neg (u : ℝ) : Φ (-u) = Φ u := by
  rw [Φ_eq, Φ_eq]
  have d1 := thetaMoment_fe_deriv1 u
  have d2 := thetaMoment_fe_deriv2 u
  have e9 : Real.exp (9 * u) = Real.exp u * Real.exp (8 * u) := by rw [← Real.exp_add]; ring_nf
  have e5 : Real.exp (5 * u) = Real.exp u * Real.exp (4 * u) := by rw [← Real.exp_add]; ring_nf
  have e9' : Real.exp (9 * -u) = Real.exp u * Real.exp (-10 * u) := by rw [← Real.exp_add]; ring_nf
  have e5' : Real.exp (5 * -u) = Real.exp u * Real.exp (-6 * u) := by rw [← Real.exp_add]; ring_nf
  rw [e9, e5, e9', e5']
  linear_combination (-(Real.exp u) / 16) * d2 - (Real.exp u / 8) * d1

theorem Φ_even : Function.Even Φ := Φ_neg

@[fun_prop]
lemma continuous_Φ : Continuous Φ := by
  have : Φ = fun u ↦ π ^ 2 * Real.exp (9 * u) * thetaMoment 2 u
      - 3 / 2 * π * Real.exp (5 * u) * thetaMoment 1 u := funext Φ_eq
  rw [this]
  fun_prop

/-! ### Decay of `Φ` -/

/-- The constant `∑_{n ≥ 1} (2π²n⁴ + 3πn²) exp(−πn²/2)` in the decay bound for `Φ`. -/
noncomputable def ΦBoundConst : ℝ :=
  ∑' n : ℕ+, (2 * π ^ 2 * (n : ℝ) ^ 4 + 3 * π * (n : ℝ) ^ 2) * Real.exp (-π * (n : ℝ) ^ 2 * (1 / 2))

lemma ΦBoundConst_nonneg : 0 ≤ ΦBoundConst :=
  tsum_nonneg fun n ↦ by positivity

lemma summable_ΦBoundConst_term :
    Summable (fun n : ℕ+ ↦
      (2 * π ^ 2 * (n : ℝ) ^ 4 + 3 * π * (n : ℝ) ^ 2) * Real.exp (-π * (n : ℝ) ^ 2 * (1 / 2))) := by
  have h2 := (summable_thetaTerm_pnat 2 (by norm_num : (0 : ℝ) < 1 / 2)).mul_left (2 * π ^ 2)
  have h1 := (summable_thetaTerm_pnat 1 (by norm_num : (0 : ℝ) < 1 / 2)).mul_left (3 * π)
  refine (h2.add h1).congr fun n ↦ ?_
  ring

/-- **Super-exponential decay of `Φ`**: for `u ≥ 0`,
`|Φ(u)| ≤ ΦBoundConst · e^{9u} · exp(−(π/2) e^{4u})`. -/
theorem abs_Φ_le {u : ℝ} (hu : 0 ≤ u) :
    |Φ u| ≤ ΦBoundConst * (Real.exp (9 * u) * Real.exp (-(π / 2) * Real.exp (4 * u))) := by
  set K : ℝ := Real.exp (9 * u) * Real.exp (-(π / 2) * Real.exp (4 * u)) with hK
  have hs := summable_Φ_term u
  have he : (1 : ℝ) ≤ Real.exp (4 * u) := Real.one_le_exp (by linarith)
  have h5 : Real.exp (5 * u) ≤ Real.exp (9 * u) := Real.exp_le_exp.mpr (by linarith)
  have hbound : ∀ n : ℕ+,
      |(2 * π ^ 2 * (n : ℝ) ^ 4 * Real.exp (9 * u) - 3 * π * (n : ℝ) ^ 2 * Real.exp (5 * u))
        * Real.exp (-π * (n : ℝ) ^ 2 * Real.exp (4 * u))|
      ≤ K * ((2 * π ^ 2 * (n : ℝ) ^ 4 + 3 * π * (n : ℝ) ^ 2) * Real.exp (-π * (n : ℝ) ^ 2 * (1 / 2))) := by
    intro n
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := Nat.one_le_cast.mpr n.pos
    have hn : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
    have hexp : Real.exp (-π * (n : ℝ) ^ 2 * Real.exp (4 * u))
        ≤ Real.exp (-(π / 2) * Real.exp (4 * u)) * Real.exp (-π * (n : ℝ) ^ 2 * (1 / 2)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith [Real.pi_pos, mul_nonneg (sub_nonneg.mpr hn) (sub_nonneg.mpr he)]
    have hA : |2 * π ^ 2 * (n : ℝ) ^ 4 * Real.exp (9 * u) - 3 * π * (n : ℝ) ^ 2 * Real.exp (5 * u)|
        ≤ Real.exp (9 * u) * (2 * π ^ 2 * (n : ℝ) ^ 4 + 3 * π * (n : ℝ) ^ 2) := by
      refine (abs_sub _ _).trans ?_
      rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left h5 (by positivity : (0 : ℝ) ≤ 3 * π * (n : ℝ) ^ 2)]
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    calc |2 * π ^ 2 * (n : ℝ) ^ 4 * Real.exp (9 * u) - 3 * π * (n : ℝ) ^ 2 * Real.exp (5 * u)|
          * Real.exp (-π * (n : ℝ) ^ 2 * Real.exp (4 * u))
        ≤ (Real.exp (9 * u) * (2 * π ^ 2 * (n : ℝ) ^ 4 + 3 * π * (n : ℝ) ^ 2))
          * (Real.exp (-(π / 2) * Real.exp (4 * u)) * Real.exp (-π * (n : ℝ) ^ 2 * (1 / 2))) :=
          mul_le_mul hA hexp (Real.exp_pos _).le (by positivity)
      _ = _ := by rw [hK]; ring
  calc |Φ u| = ‖∑' n : ℕ+, (2 * π ^ 2 * (n : ℝ) ^ 4 * Real.exp (9 * u) - 3 * π * (n : ℝ) ^ 2 * Real.exp (5 * u))
        * Real.exp (-π * (n : ℝ) ^ 2 * Real.exp (4 * u))‖ := by rw [Real.norm_eq_abs]; rfl
    _ ≤ ∑' n : ℕ+, ‖(2 * π ^ 2 * (n : ℝ) ^ 4 * Real.exp (9 * u) - 3 * π * (n : ℝ) ^ 2 * Real.exp (5 * u))
        * Real.exp (-π * (n : ℝ) ^ 2 * Real.exp (4 * u))‖ := norm_tsum_le_tsum_norm hs.norm
    _ ≤ ∑' n : ℕ+, K * ((2 * π ^ 2 * (n : ℝ) ^ 4 + 3 * π * (n : ℝ) ^ 2)
        * Real.exp (-π * (n : ℝ) ^ 2 * (1 / 2))) := by
        refine hs.norm.tsum_le_tsum (fun n ↦ ?_) (summable_ΦBoundConst_term.mul_left K)
        rw [Real.norm_eq_abs]; exact hbound n
    _ = K * ΦBoundConst := tsum_mul_left
    _ = ΦBoundConst * K := mul_comm _ _

/-! ### Integrability of the heat-flow integrand -/

/-- `exp(a u² + b u) · exp(−(π/2) e^{4u})` is integrable on `(0, ∞)` for every `a, b`
(the double-exponential factor beats any Gaussian growth). -/
lemma integrableOn_exp_quad_mul_exp_neg_exp (a b : ℝ) :
    IntegrableOn (fun u : ℝ ↦ Real.exp (a * u ^ 2 + b * u) * Real.exp (-(π / 2) * Real.exp (4 * u)))
      (Ioi 0) := by
  apply integrable_of_isBigO_exp_neg (b := 1) one_pos
  · exact Continuous.continuousOn (by fun_prop)
  · have hfun : (fun u : ℝ ↦ Real.exp (a * u ^ 2 + b * u) * Real.exp (-(π / 2) * Real.exp (4 * u)))
        = fun u ↦ Real.exp (a * u ^ 2 + b * u + -(π / 2) * Real.exp (4 * u)) := by
      funext u; rw [← Real.exp_add]
    rw [hfun]
    apply Real.isBigO_exp_comp_exp_comp.mpr
    apply Filter.Tendsto.isBoundedUnder_le_atBot
    have hfact : ((fun u : ℝ ↦ a * u ^ 2 + b * u + -(π / 2) * Real.exp (4 * u)) - fun u ↦ -1 * u)
        = fun u ↦ Real.exp (4 * u) *
            (a * (u ^ 2 * Real.exp (-(4 * u))) + (b + 1) * (u * Real.exp (-(4 * u))) - π / 2) := by
      funext u
      simp only [Pi.sub_apply]
      rw [Real.exp_neg]
      field_simp
      ring
    rw [hfact]
    have h4 : Tendsto (fun u : ℝ ↦ 4 * u) atTop atTop := tendsto_id.const_mul_atTop (by norm_num)
    apply Filter.Tendsto.atTop_mul_neg (by linarith [Real.pi_pos] : -(π / 2) < 0)
    · exact Real.tendsto_exp_atTop.comp h4
    · have h2 : Tendsto (fun u : ℝ ↦ u ^ 2 * Real.exp (-(4 * u))) atTop (𝓝 0) := by
        have := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).comp h4).const_mul (1 / 16)
        rw [mul_zero] at this
        refine this.congr fun u ↦ ?_
        simp only [Function.comp]
        ring
      have h1 : Tendsto (fun u : ℝ ↦ u * Real.exp (-(4 * u))) atTop (𝓝 0) := by
        have := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp h4).const_mul (1 / 4)
        rw [mul_zero] at this
        refine this.congr fun u ↦ ?_
        simp only [Function.comp]
        ring
      have := ((h2.const_mul a).add (h1.const_mul (b + 1))).sub_const (π / 2)
      simpa using this

/-- `‖cos w‖ ≤ exp ‖w‖` for complex `w`. -/
lemma norm_cos_le_exp_norm (w : ℂ) : ‖Complex.cos w‖ ≤ Real.exp ‖w‖ := by
  have him := Complex.abs_im_le_norm w
  have h1 : ‖Complex.exp (w * Complex.I)‖ ≤ Real.exp ‖w‖ := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simp only [Complex.mul_re, Complex.I_re, mul_zero, Complex.I_im, mul_one, zero_sub]
    linarith [neg_abs_le w.im]
  have h2 : ‖Complex.exp (-w * Complex.I)‖ ≤ Real.exp ‖w‖ := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simp only [Complex.mul_re, Complex.neg_re, Complex.I_re, mul_zero, Complex.neg_im, Complex.I_im,
      mul_one, zero_sub, neg_neg]
    linarith [le_abs_self w.im]
  calc ‖Complex.cos w‖ = ‖(Complex.exp (w * Complex.I) + Complex.exp (-w * Complex.I)) / 2‖ := rfl
    _ = ‖Complex.exp (w * Complex.I) + Complex.exp (-w * Complex.I)‖ / 2 := by
        rw [norm_div, Complex.norm_two]
    _ ≤ (Real.exp ‖w‖ + Real.exp ‖w‖) / 2 := by
        gcongr
        exact (norm_add_le _ _).trans (add_le_add h1 h2)
    _ = Real.exp ‖w‖ := by ring

/-! ### The heat-flow family `H_t` -/

/-- The `H_t` integrand `e^{t u²} Φ(u) cos(z u)` (Polymath15 / Rodgers-Tao convention). -/
noncomputable def HIntegrand (t : ℝ) (z : ℂ) (u : ℝ) : ℂ :=
  ((Real.exp (t * u ^ 2) : ℝ) : ℂ) * ((Φ u : ℝ) : ℂ) * Complex.cos (z * u)

/-- `H_t(z) := ∫_0^∞ e^{tu²} Φ(u) cos(zu) du`.  For `t = 0` this is, classically,
`(1/8) ξ(1/2 + iz/2)` (registry statement `RH.dbn_H0_eq_xi`, NOT proved here). -/
noncomputable def H (t : ℝ) (z : ℂ) : ℂ := ∫ u in Set.Ioi (0 : ℝ), HIntegrand t z u

@[fun_prop]
lemma continuous_HIntegrand (t : ℝ) (z : ℂ) : Continuous (HIntegrand t z) := by
  unfold HIntegrand
  fun_prop

/-- **The `H_t` integrand is integrable on `(0, ∞)` for every `t ∈ ℝ` and `z ∈ ℂ`.** -/
theorem integrableOn_HIntegrand (t : ℝ) (z : ℂ) : IntegrableOn (HIntegrand t z) (Ioi 0) := by
  have hg := (integrableOn_exp_quad_mul_exp_neg_exp t (9 + ‖z‖)).const_mul ΦBoundConst
  refine hg.mono' (continuous_HIntegrand t z).aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  refine Eventually.of_forall fun u hu ↦ ?_
  have hu0 : (0 : ℝ) ≤ u := le_of_lt hu
  have hcos : ‖Complex.cos (z * u)‖ ≤ Real.exp (‖z‖ * u) := by
    refine (norm_cos_le_exp_norm _).trans ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu0]
  have hΦ := abs_Φ_le hu0
  have hC := ΦBoundConst_nonneg
  unfold HIntegrand
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  calc Real.exp (t * u ^ 2) * |Φ u| * ‖Complex.cos (z * u)‖
      ≤ Real.exp (t * u ^ 2) * (ΦBoundConst * (Real.exp (9 * u) * Real.exp (-(π / 2) * Real.exp (4 * u))))
          * Real.exp (‖z‖ * u) := by gcongr
    _ = ΦBoundConst * (Real.exp (t * u ^ 2 + (9 + ‖z‖) * u) * Real.exp (-(π / 2) * Real.exp (4 * u))) := by
        rw [Real.exp_add, add_mul, Real.exp_add]; ring

/-- `H_t` is even in `z`. -/
theorem H_neg (t : ℝ) (z : ℂ) : H t (-z) = H t z := by
  unfold H HIntegrand
  simp only [neg_mul, Complex.cos_neg]

/-- On the real axis `H_t` is the real integral `∫_0^∞ e^{tu²} Φ(u) cos(xu) du` (cast to `ℂ`). -/
theorem H_ofReal (t x : ℝ) :
    H t x = ((∫ u in Ioi (0 : ℝ), Real.exp (t * u ^ 2) * Φ u * Real.cos (x * u) : ℝ) : ℂ) := by
  have hfun : (fun u ↦ HIntegrand t x u)
      = fun u ↦ ((Real.exp (t * u ^ 2) * Φ u * Real.cos (x * u) : ℝ) : ℂ) := by
    funext u
    unfold HIntegrand
    push_cast
    ring
  unfold H
  rw [hfun]
  exact integral_ofReal

/-- **`H_t(z)` is real for real `z`.** -/
theorem H_ofReal_im (t x : ℝ) : (H t x).im = 0 := by
  rw [H_ofReal]; simp

/-! ### The `ξ` vocabulary bridge -/

/-- The pinned upstream `LiCriterion.riemannXi s = (1/2) s (s−1) Λ₀(s) + 1/2` agrees with the
textbook `ξ(s) = (1/2) s (s−1) Λ(s)`, `Λ = completedRiemannZeta`, away from the poles of `Λ`.
This is the normalization in which `H_0(z) = (1/8) ξ(1/2 + iz/2)` (registry `RH.dbn_H0_eq_xi`). -/
theorem riemannXi_eq_completedRiemannZeta {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    LiCriterion.riemannXi s = (1 / 2 : ℂ) * s * (s - 1) * completedRiemannZeta s := by
  unfold LiCriterion.riemannXi
  rw [completedRiemannZeta_eq]
  have h1' : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  field_simp
  ring

/-! ### `H_t` is entire -/

/-- `‖sin w‖ ≤ exp ‖w‖` for complex `w`. -/
lemma norm_sin_le_exp_norm (w : ℂ) : ‖Complex.sin w‖ ≤ Real.exp ‖w‖ := by
  have him := Complex.abs_im_le_norm w
  have h1 : ‖Complex.exp (w * Complex.I)‖ ≤ Real.exp ‖w‖ := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simp only [Complex.mul_re, Complex.I_re, mul_zero, Complex.I_im, mul_one, zero_sub]
    linarith [neg_abs_le w.im]
  have h2 : ‖Complex.exp (-w * Complex.I)‖ ≤ Real.exp ‖w‖ := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simp only [Complex.mul_re, Complex.neg_re, Complex.I_re, mul_zero, Complex.neg_im, Complex.I_im,
      mul_one, zero_sub, neg_neg]
    linarith [le_abs_self w.im]
  calc ‖Complex.sin w‖
      = ‖(Complex.exp (-w * Complex.I) - Complex.exp (w * Complex.I)) * Complex.I / 2‖ := rfl
    _ = ‖Complex.exp (-w * Complex.I) - Complex.exp (w * Complex.I)‖ / 2 := by
        rw [norm_div, norm_mul, Complex.norm_I, mul_one, Complex.norm_two]
    _ ≤ (Real.exp ‖w‖ + Real.exp ‖w‖) / 2 := by
        gcongr
        exact (norm_sub_le _ _).trans (add_le_add h2 h1)
    _ = Real.exp ‖w‖ := by ring

/-- The `z`-derivative of the `H_t` integrand: `e^{tu²} Φ(u) · (−u sin(zu))`. -/
noncomputable def HIntegrand' (t : ℝ) (z : ℂ) (u : ℝ) : ℂ :=
  ((Real.exp (t * u ^ 2) : ℝ) : ℂ) * ((Φ u : ℝ) : ℂ) * (-Complex.sin (z * u) * u)

lemma hasDerivAt_HIntegrand (t u : ℝ) (z : ℂ) :
    HasDerivAt (fun w ↦ HIntegrand t w u) (HIntegrand' t z u) z := by
  have h : HasDerivAt (fun w : ℂ ↦ Complex.cos (w * u)) (-Complex.sin (z * u) * u) z := by
    have := ((hasDerivAt_id z).mul_const (u : ℂ)).ccos
    simpa using this
  exact h.const_mul _

@[fun_prop]
lemma continuous_HIntegrand' (t : ℝ) (z : ℂ) : Continuous (HIntegrand' t z) := by
  unfold HIntegrand'
  fun_prop

/-- **`H_t` is complex-differentiable at every `z₀`**, with derivative
`∫_0^∞ e^{tu²} Φ(u) (−u sin(z₀u)) du` (differentiation under the integral sign, dominated on
the unit ball around `z₀` by the integrable majorant of `integrableOn_exp_quad_mul_exp_neg_exp`). -/
theorem hasDerivAt_H (t : ℝ) (z₀ : ℂ) :
    HasDerivAt (H t) (∫ u in Set.Ioi (0 : ℝ), HIntegrand' t z₀ u) z₀ := by
  have hC := ΦBoundConst_nonneg
  have hbound := (integrableOn_exp_quad_mul_exp_neg_exp t (11 + ‖z₀‖)).const_mul ΦBoundConst
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Set.Ioi 0))
    (F := fun z u ↦ HIntegrand t z u) (F' := fun z u ↦ HIntegrand' t z u)
    (s := Metric.ball z₀ 1) (Metric.ball_mem_nhds z₀ one_pos)
    (Eventually.of_forall fun z ↦ (continuous_HIntegrand t z).aestronglyMeasurable)
    (integrableOn_HIntegrand t z₀)
    (continuous_HIntegrand' t z₀).aestronglyMeasurable ?_ hbound
    (Eventually.of_forall fun u z _ ↦ hasDerivAt_HIntegrand t u z)).2
  rw [ae_restrict_iff' measurableSet_Ioi]
  refine Eventually.of_forall fun u hu z hz ↦ ?_
  have hu0 : (0 : ℝ) ≤ u := le_of_lt hu
  have hz' : ‖z‖ ≤ ‖z₀‖ + 1 := by
    have := Metric.mem_ball.mp hz
    rw [Complex.dist_eq] at this
    calc ‖z‖ = ‖z₀ + (z - z₀)‖ := by congr 1; ring
      _ ≤ ‖z₀‖ + ‖z - z₀‖ := norm_add_le _ _
      _ ≤ ‖z₀‖ + 1 := by linarith
  have hsin : ‖-Complex.sin (z * u) * u‖ ≤ Real.exp ((‖z₀‖ + 2) * u) := by
    rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu0]
    have h1 : ‖Complex.sin (z * u)‖ ≤ Real.exp ((‖z₀‖ + 1) * u) := by
      refine (norm_sin_le_exp_norm _).trans ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu0]
      exact Real.exp_le_exp.mpr (by nlinarith)
    have h2 : u ≤ Real.exp u := by linarith [Real.add_one_le_exp u]
    calc ‖Complex.sin (z * u)‖ * u ≤ Real.exp ((‖z₀‖ + 1) * u) * Real.exp u :=
          mul_le_mul h1 h2 hu0 (Real.exp_pos _).le
      _ = Real.exp ((‖z₀‖ + 2) * u) := by rw [← Real.exp_add]; ring_nf
  have hΦ := abs_Φ_le hu0
  have e : Real.exp (9 * u) * Real.exp ((‖z₀‖ + 2) * u) = Real.exp ((11 + ‖z₀‖) * u) := by
    rw [← Real.exp_add]; ring_nf
  show ‖HIntegrand' t z u‖ ≤ _
  unfold HIntegrand'
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  calc Real.exp (t * u ^ 2) * |Φ u| * ‖-Complex.sin (z * u) * u‖
      ≤ Real.exp (t * u ^ 2)
          * (ΦBoundConst * (Real.exp (9 * u) * Real.exp (-(π / 2) * Real.exp (4 * u))))
          * Real.exp ((‖z₀‖ + 2) * u) := by gcongr
    _ = ΦBoundConst * (Real.exp (t * u ^ 2 + (11 + ‖z₀‖) * u)
          * Real.exp (-(π / 2) * Real.exp (4 * u))) := by
        rw [Real.exp_add, ← e]; ring

/-- **`H_t` is entire** for every `t ∈ ℝ`. -/
theorem differentiable_H (t : ℝ) : Differentiable ℂ (H t) :=
  fun z ↦ (hasDerivAt_H t z).differentiableAt

end DBN
