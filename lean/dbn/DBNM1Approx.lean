/-
  DBNM1Approx -- lane m1, Route C milestone M1 (telperion/docs/ROUTE_C_SYNTHESIS_2026-09-23.md
  sections 5.2 and 7.2): the de Bruijn approximants REWEIGHTED at an arbitrary base time `t0`.

    m1W t0 δ N z := ∫_0^∞ cosh(δu)^N e^{t0 u²} Φ(u) cos(zu) du,       m1G t0 s N := m1W t0 (√(2s/N)) N.

  For `t0 = 0` it agrees with `DBNHeatApprox.Gδ` (`m1W_zero_base`).  The base weight
  `e^{t0 u²}` is carried inside the integrand (`m1WIntegrand = cosh(δu)^N · HIntegrand t0`), so
  `m1W t0 δ 0 = H t0` by definition.

  What IS proved here (axiom-clean, see AxiomGuardDBN.lean), for EVERY real `t0` (negative
  included):
    * integrability of the integrand; the shift identity `m1W t0 δ (N+1) = T_δ (m1W t0 δ N)`
      (`m1W_succ`), `m1W t0 δ 0 = H t0` (`m1W_zero`), hence `m1W t0 δ N = T_δ^N (H t0)`;
    * `m1W t0 δ N` is entire, even and real (`m1_differentiable_W`, `m1W_neg`, `m1W_conj`), and
      `m1W t0 δ N 0 > 0` (`m1_W_zero_re_pos`, from `Φ_pos`), so it is not identically zero;
    * the order bound `‖m1W t0 δ N z‖ ≤ (ΦBoundConst/π) e^{t0²/π} exp((2/3)((9 + N|δ| + ‖z‖)/2)^{3/2})`
      (`m1_norm_W_le_exp_rpow_norm`): order `≤ 3/2 < 2` for every real `t0`.  The only new input
      over `DBNHeatApprox.norm_Gδ_le_exp_rpow` is `t0 u² ≤ (π/4) e^{4u} + t0²/π`
      (`m1_mul_sq_le_exp`), absorbed by the double-exponential decay of `Φ`;
    * every approximant carries even Hadamard data (`m1_evenHadamardData_W`, via
      `DBNHadamard.evenHadamardData_of_order_lt_two`);
    * for `s ≥ 0`, `m1G t0 s N → H (t0 + s)` locally uniformly on `ℂ` (`m1_tendstoLocallyUniformly_G`).

  Nothing here is about the location of any zero; the parametric de Bruijn theorem is assembled in
  `DBNM1Parametric`.  Nothing here proves RH.  conjecture1_proved = False.
-/
import DBNHeatApprox
import DBNHadamard

open Real MeasureTheory Set Filter Topology ComplexConjugate

namespace DBN

/-! ### The reweighted approximants -/

/-- The integrand `cosh(δu)^N · e^{t0 u²} Φ(u) cos(zu)` of the reweighted approximant: the heat
integrand `HIntegrand t0` times the kernel weight `cosh(δu)^N`. -/
noncomputable def m1WIntegrand (t0 δ : ℝ) (N : ℕ) (z : ℂ) (u : ℝ) : ℂ :=
  ((Real.cosh (δ * u) ^ N : ℝ) : ℂ) * HIntegrand t0 z u

/-- The reweighted approximant `m1W t0 δ N z = ∫_0^∞ cosh(δu)^N e^{t0 u²} Φ(u) cos(zu) du`. -/
noncomputable def m1W (t0 δ : ℝ) (N : ℕ) (z : ℂ) : ℂ := ∫ u in Ioi (0 : ℝ), m1WIntegrand t0 δ N z u

/-- The reweighted de Bruijn approximant for the time increment `s`:
`m1G t0 s N = m1W t0 (√(2s/N)) N`, whose kernel `cosh(u √(2s/N))^N e^{t0 u²}` tends to
`e^{(t0 + s) u²}`. -/
noncomputable def m1G (t0 s : ℝ) (N : ℕ) : ℂ → ℂ := m1W t0 (Real.sqrt (2 * s / N)) N

@[fun_prop]
lemma m1_continuous_WIntegrand (t0 δ : ℝ) (N : ℕ) (z : ℂ) :
    Continuous (m1WIntegrand t0 δ N z) := by
  unfold m1WIntegrand
  fun_prop

/-- Pointwise bound for the heat integrand at an arbitrary real time. -/
lemma m1_norm_HIntegrand_le (t0 : ℝ) (z : ℂ) {u : ℝ} (hu : 0 ≤ u) :
    ‖HIntegrand t0 z u‖ ≤ Real.exp (t0 * u ^ 2) * |Φ u| * Real.exp (|z.im| * u) := by
  unfold HIntegrand
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_left (norm_cos_mul_le hu z) (by positivity)

lemma m1_norm_WIntegrand (t0 δ : ℝ) (N : ℕ) (z : ℂ) (u : ℝ) :
    ‖m1WIntegrand t0 δ N z u‖ = Real.cosh (δ * u) ^ N * ‖HIntegrand t0 z u‖ := by
  unfold m1WIntegrand
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg (Real.cosh_pos _).le N)]

/-- **The reweighted integrand is integrable on `(0, ∞)`** for every `t0`, `δ`, `N`, `z`. -/
theorem m1_integrableOn_WIntegrand (t0 δ : ℝ) (N : ℕ) (z : ℂ) :
    IntegrableOn (m1WIntegrand t0 δ N z) (Ioi 0) := by
  refine (integrableOn_exp_mul_abs_Φ (N * δ ^ 2 / 2 + t0) |z.im|).mono'
    (m1_continuous_WIntegrand t0 δ N z).aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  refine Eventually.of_forall fun u hu ↦ ?_
  have hu0 : 0 ≤ u := le_of_lt hu
  rw [m1_norm_WIntegrand]
  have h1 := m1_norm_HIntegrand_le t0 z hu0
  have h2 := cosh_pow_le_exp δ u N
  calc Real.cosh (δ * u) ^ N * ‖HIntegrand t0 z u‖
      ≤ Real.exp (N * δ ^ 2 / 2 * u ^ 2)
          * (Real.exp (t0 * u ^ 2) * |Φ u| * Real.exp (|z.im| * u)) :=
        mul_le_mul h2 h1 (norm_nonneg _) (Real.exp_pos _).le
    _ = Real.exp ((N * δ ^ 2 / 2 + t0) * u ^ 2 + |z.im| * u) * |Φ u| := by
        rw [add_mul, Real.exp_add, Real.exp_add]; ring

/-! ### The shift identity and the iterate -/

/-- Pointwise shift identity for the reweighted integrand. -/
lemma m1_WIntegrand_succ (t0 δ : ℝ) (N : ℕ) (z : ℂ) (u : ℝ) :
    m1WIntegrand t0 δ (N + 1) z u
      = (m1WIntegrand t0 δ N (z + Complex.I * δ) u
          + m1WIntegrand t0 δ N (z - Complex.I * δ) u) / 2 := by
  have hcos : Complex.cos ((z + Complex.I * δ) * u) + Complex.cos ((z - Complex.I * δ) * u)
      = 2 * Complex.cos (z * u) * ((Real.cosh (δ * u) : ℝ) : ℂ) := by
    rw [Complex.cos_add_cos, Complex.ofReal_cosh]
    have e1 : ((z + Complex.I * δ) * u + (z - Complex.I * δ) * u) / 2 = z * u := by ring
    have e2 : ((z + Complex.I * δ) * u - (z - Complex.I * δ) * u) / 2
        = ((δ * u : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [e1, e2, Complex.cos_mul_I]
  unfold m1WIntegrand HIntegrand
  simp only [Complex.ofReal_pow]
  linear_combination (-(((Real.cosh (δ * u) : ℝ) : ℂ) ^ N * ((Real.exp (t0 * u ^ 2) : ℝ) : ℂ)
    * ((Φ u : ℝ) : ℂ) / 2)) * hcos

/-- **The shift identity**: `m1W t0 δ (N+1) = T_δ (m1W t0 δ N)`. -/
theorem m1W_succ (t0 δ : ℝ) (N : ℕ) : m1W t0 δ (N + 1) = shiftAvg δ (m1W t0 δ N) := by
  funext z
  unfold m1W shiftAvg
  simp_rw [m1_WIntegrand_succ]
  rw [integral_div, integral_add (m1_integrableOn_WIntegrand _ _ _ _)
    (m1_integrableOn_WIntegrand _ _ _ _)]

/-- `m1W t0 δ 0 = H t0` (no kernel weight). -/
theorem m1W_zero (t0 δ : ℝ) : m1W t0 δ 0 = H t0 := by
  funext z
  unfold m1W H m1WIntegrand
  simp

/-- Consistency with the island's base-time-`0` approximants: `m1W 0 δ N = Gδ δ N`. -/
theorem m1W_zero_base (δ : ℝ) (N : ℕ) : m1W 0 δ N = Gδ δ N := by
  funext z
  unfold m1W Gδ m1WIntegrand HIntegrand GδIntegrand
  simp only [zero_mul, Real.exp_zero, Complex.ofReal_one, one_mul]
  congr 1
  funext u
  ring

/-- **The iterate**: `m1W t0 δ N = T_δ^N (H t0)`. -/
theorem m1W_eq_iterate (t0 δ : ℝ) (N : ℕ) : m1W t0 δ N = (shiftAvg δ)^[N] (H t0) := by
  induction N with
  | zero => simp [m1W_zero]
  | succ N ih => rw [m1W_succ, ih, Function.iterate_succ_apply']

/-- **`m1W t0 δ N` is entire.** -/
theorem m1_differentiable_W (t0 δ : ℝ) (N : ℕ) : Differentiable ℂ (m1W t0 δ N) := by
  induction N with
  | zero => rw [m1W_zero]; exact differentiable_H t0
  | succ N ih => rw [m1W_succ]; exact differentiable_shiftAvg ih δ

/-- **`m1W t0 δ N` is even.** -/
theorem m1W_neg (t0 δ : ℝ) (N : ℕ) (z : ℂ) : m1W t0 δ N (-z) = m1W t0 δ N z := by
  unfold m1W m1WIntegrand HIntegrand
  simp only [neg_mul, Complex.cos_neg]

/-- **`m1W t0 δ N` is real**: `m1W t0 δ N (conj z) = conj (m1W t0 δ N z)`. -/
theorem m1W_conj (t0 δ : ℝ) (N : ℕ) (z : ℂ) : m1W t0 δ N (conj z) = conj (m1W t0 δ N z) := by
  unfold m1W
  rw [← integral_conj]
  congr 1
  funext u
  unfold m1WIntegrand HIntegrand
  simp only [map_mul, Complex.conj_ofReal, ← Complex.cos_conj]

/-! ### Positivity at the origin -/

/-- **`m1W t0 δ N 0 > 0`**, so every reweighted approximant is not identically zero. -/
theorem m1_W_zero_re_pos (t0 δ : ℝ) (N : ℕ) : 0 < (m1W t0 δ N 0).re := by
  have hfun : (fun u ↦ m1WIntegrand t0 δ N 0 u)
      = fun u ↦ ((Real.cosh (δ * u) ^ N * Real.exp (t0 * u ^ 2) * Φ u : ℝ) : ℂ) := by
    funext u
    unfold m1WIntegrand HIntegrand
    simp only [zero_mul, Complex.cos_zero, mul_one]
    push_cast
    ring
  have h0 : m1W t0 δ N 0
      = ((∫ u in Ioi (0 : ℝ), Real.cosh (δ * u) ^ N * Real.exp (t0 * u ^ 2) * Φ u : ℝ) : ℂ) := by
    unfold m1W
    rw [hfun]
    exact integral_ofReal
  rw [h0, Complex.ofReal_re]
  refine setIntegral_weight_mul_Φ_pos (w := fun u ↦ Real.cosh (δ * u) ^ N * Real.exp (t0 * u ^ 2))
    (fun u ↦ mul_pos (pow_pos (Real.cosh_pos _) N) (Real.exp_pos _)) ?_
  refine (integrableOn_exp_mul_abs_Φ (N * δ ^ 2 / 2 + t0) 0).mono'
    (by fun_prop : Continuous (fun u : ℝ ↦
      Real.cosh (δ * u) ^ N * Real.exp (t0 * u ^ 2) * Φ u)).aestronglyMeasurable ?_
  refine Eventually.of_forall fun u ↦ ?_
  have h2 := cosh_pow_le_exp δ u N
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (pow_nonneg (Real.cosh_pos _).le N),
    abs_of_pos (Real.exp_pos _)]
  calc Real.cosh (δ * u) ^ N * Real.exp (t0 * u ^ 2) * |Φ u|
      ≤ Real.exp (N * δ ^ 2 / 2 * u ^ 2) * Real.exp (t0 * u ^ 2) * |Φ u| := by gcongr
    _ = Real.exp ((N * δ ^ 2 / 2 + t0) * u ^ 2 + 0 * u) * |Φ u| := by
        rw [zero_mul, add_zero, add_mul, Real.exp_add]

theorem m1_W_zero_ne_zero (t0 δ : ℝ) (N : ℕ) : m1W t0 δ N 0 ≠ 0 := by
  intro h
  have := m1_W_zero_re_pos t0 δ N
  rw [h, Complex.zero_re] at this
  exact lt_irrefl _ this

/-! ### Order bound `≤ 3/2`, uniform in the sign of `t0` -/

/-- `t0 u² ≤ (π/4) e^{4u} + t0²/π` for `u ≥ 0` and EVERY real `t0`
(`u² ≤ e^{2u}` and `|t0| x ≤ (π/4) x² + t0²/π`). -/
lemma m1_mul_sq_le_exp (t0 : ℝ) {u : ℝ} (hu : 0 ≤ u) :
    t0 * u ^ 2 ≤ π / 4 * Real.exp (4 * u) + t0 ^ 2 / π := by
  have hπ := Real.pi_pos
  have h1 : u ≤ Real.exp u := by linarith [Real.add_one_le_exp u]
  have h2 : u ^ 2 ≤ Real.exp (2 * u) := by
    rw [show 2 * u = u + u by ring, Real.exp_add, sq]
    exact mul_le_mul h1 h1 hu (Real.exp_pos _).le
  have h3 : t0 * u ^ 2 ≤ |t0| * Real.exp (2 * u) :=
    calc t0 * u ^ 2 ≤ |t0| * u ^ 2 := mul_le_mul_of_nonneg_right (le_abs_self t0) (sq_nonneg u)
      _ ≤ |t0| * Real.exp (2 * u) := mul_le_mul_of_nonneg_left h2 (abs_nonneg t0)
  have h4 : Real.exp (4 * u) = Real.exp (2 * u) ^ 2 := by
    rw [sq, ← Real.exp_add]; congr 1; ring
  rw [h4]
  set x : ℝ := Real.exp (2 * u)
  have h5 : |t0| * x ≤ π / 4 * x ^ 2 + t0 ^ 2 / π := by
    rw [← sq_abs t0]
    have key : π / 4 * x ^ 2 + |t0| ^ 2 / π - |t0| * x = (π * x - 2 * |t0|) ^ 2 / (4 * π) := by
      field_simp
      ring
    have : 0 ≤ (π * x - 2 * |t0|) ^ 2 / (4 * π) := by positivity
    linarith
  linarith

/-- `(8/3) u³ + π u ≤ (π/4) e^{4u}` for `u ≥ 0` (four terms of the exponential series). -/
lemma m1_cube_add_le_exp {u : ℝ} (hu : 0 ≤ u) :
    8 / 3 * u ^ 3 + π * u ≤ π / 4 * Real.exp (4 * u) := by
  have h := Real.sum_le_exp_of_nonneg (by positivity : (0 : ℝ) ≤ 4 * u) 4
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  norm_num at h
  have hπ : 3 < π := Real.pi_gt_three
  have hu3 : 0 ≤ u ^ 3 := by positivity
  have hu2 : 0 ≤ u ^ 2 := by positivity
  nlinarith [mul_nonneg (le_of_lt Real.pi_pos) hu3, mul_nonneg (le_of_lt Real.pi_pos) hu2,
    mul_nonneg (le_of_lt Real.pi_pos) hu]

/-- Pointwise majorant of the reweighted integrand with integrable, `z`-free decay:
`‖m1WIntegrand t0 δ N z u‖ ≤ ΦBoundConst e^{t0²/π} exp((2/3)(A/2)^{3/2}) e^{−πu}`,
`A = 9 + N|δ| + |Im z|`, for `u ≥ 0`. -/
lemma m1_norm_WIntegrand_le_rpow (t0 δ : ℝ) (N : ℕ) (z : ℂ) {u : ℝ} (hu : 0 ≤ u) :
    ‖m1WIntegrand t0 δ N z u‖ ≤ ΦBoundConst * Real.exp (t0 ^ 2 / π)
      * Real.exp (2 / 3 * ((9 + N * |δ| + |z.im|) / 2) ^ (3 / 2 : ℝ)) * Real.exp (-π * u) := by
  set A : ℝ := 9 + N * |δ| + |z.im| with hA_def
  have hA : 0 ≤ A := by positivity
  have hΦ := abs_Φ_le hu
  have hC := ΦBoundConst_nonneg
  have hch : Real.cosh (δ * u) ^ N ≤ Real.exp (N * |δ| * u) := by
    calc Real.cosh (δ * u) ^ N ≤ Real.exp |δ * u| ^ N :=
          pow_le_pow_left₀ (Real.cosh_pos _).le (cosh_le_exp_abs _) N
      _ = Real.exp (N * |δ| * u) := by
          rw [← Real.exp_nat_mul, abs_mul, abs_of_nonneg hu]; ring_nf
  have hkey : A * u + t0 * u ^ 2 - π / 2 * Real.exp (4 * u)
      ≤ 2 / 3 * (A / 2) ^ (3 / 2 : ℝ) + t0 ^ 2 / π + -π * u := by
    have h1 := mul_le_rpow_add_cube hA hu
    have h2 := m1_cube_add_le_exp hu
    have h3 := m1_mul_sq_le_exp t0 hu
    linarith
  rw [m1_norm_WIntegrand]
  have hH := m1_norm_HIntegrand_le t0 z hu
  have hHΦ : ‖HIntegrand t0 z u‖ ≤ Real.exp (t0 * u ^ 2)
      * (ΦBoundConst * (Real.exp (9 * u) * Real.exp (-(π / 2) * Real.exp (4 * u))))
      * Real.exp (|z.im| * u) := by
    refine hH.trans ?_
    gcongr
  calc Real.cosh (δ * u) ^ N * ‖HIntegrand t0 z u‖
      ≤ Real.exp (N * |δ| * u) * (Real.exp (t0 * u ^ 2)
          * (ΦBoundConst * (Real.exp (9 * u) * Real.exp (-(π / 2) * Real.exp (4 * u))))
          * Real.exp (|z.im| * u)) :=
        mul_le_mul hch hHΦ (norm_nonneg _) (Real.exp_pos _).le
    _ = ΦBoundConst * Real.exp (A * u + t0 * u ^ 2 - π / 2 * Real.exp (4 * u)) := by
        have e : Real.exp (A * u + t0 * u ^ 2 - π / 2 * Real.exp (4 * u))
            = Real.exp (N * |δ| * u) * Real.exp (t0 * u ^ 2) * Real.exp (9 * u)
              * Real.exp (-(π / 2) * Real.exp (4 * u)) * Real.exp (|z.im| * u) := by
          rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add, hA_def]
          ring_nf
        rw [e]
        ring
    _ ≤ ΦBoundConst * Real.exp (2 / 3 * (A / 2) ^ (3 / 2 : ℝ) + t0 ^ 2 / π + -π * u) := by
        gcongr
    _ = ΦBoundConst * Real.exp (t0 ^ 2 / π) * Real.exp (2 / 3 * (A / 2) ^ (3 / 2 : ℝ))
          * Real.exp (-π * u) := by
        rw [Real.exp_add, Real.exp_add]; ring

/-- **Order bound `≤ 3/2` for every real `t0`.**  With `A = 9 + N|δ| + |Im z|`,
`‖m1W t0 δ N z‖ ≤ (ΦBoundConst/π) e^{t0²/π} exp((2/3)(A/2)^{3/2})`. -/
theorem m1_norm_W_le_exp_rpow (t0 δ : ℝ) (N : ℕ) (z : ℂ) :
    ‖m1W t0 δ N z‖ ≤ ΦBoundConst / π * Real.exp (t0 ^ 2 / π)
      * Real.exp (2 / 3 * ((9 + N * |δ| + |z.im|) / 2) ^ (3 / 2 : ℝ)) := by
  set E : ℝ := Real.exp (2 / 3 * ((9 + N * |δ| + |z.im|) / 2) ^ (3 / 2 : ℝ)) with hE
  have hint : IntegrableOn
      (fun u : ℝ ↦ ΦBoundConst * Real.exp (t0 ^ 2 / π) * E * Real.exp (-π * u)) (Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 Real.pi_pos).const_mul _
  unfold m1W
  refine (norm_integral_le_of_norm_le hint ?_).trans (le_of_eq ?_)
  · rw [ae_restrict_iff' measurableSet_Ioi]
    exact Eventually.of_forall fun u hu ↦ m1_norm_WIntegrand_le_rpow t0 δ N z (le_of_lt hu)
  · rw [integral_const_mul, integral_exp_mul_Ioi (by linarith [Real.pi_pos]) 0]
    simp only [mul_zero, Real.exp_zero]
    field_simp

/-- **Order bound `≤ 3/2`, in `‖z‖`.** -/
theorem m1_norm_W_le_exp_rpow_norm (t0 δ : ℝ) (N : ℕ) (z : ℂ) :
    ‖m1W t0 δ N z‖ ≤ ΦBoundConst / π * Real.exp (t0 ^ 2 / π)
      * Real.exp (2 / 3 * ((9 + N * |δ| + ‖z‖) / 2) ^ (3 / 2 : ℝ)) := by
  refine (m1_norm_W_le_exp_rpow t0 δ N z).trans ?_
  have hC : 0 ≤ ΦBoundConst / π * Real.exp (t0 ^ 2 / π) :=
    mul_nonneg (div_nonneg ΦBoundConst_nonneg Real.pi_pos.le) (Real.exp_pos _).le
  gcongr
  exact Complex.abs_im_le_norm z

/-- **Order `3/2` growth bound in the shape the factorisation theorem consumes.** -/
lemma m1_norm_W_le_growth (t0 δ : ℝ) (N : ℕ) :
    ∃ A B : ℝ, 1 ≤ A ∧ 0 ≤ B ∧
      ∀ z, ‖m1W t0 δ N z‖ ≤ A * Real.exp (B * ‖z‖ ^ (3 / 2 : ℝ)) := by
  obtain ⟨c₀, hc₀⟩ : ∃ c : ℝ, c = 9 + N * |δ| := ⟨_, rfl⟩
  have hc₀0 : 0 ≤ c₀ := by rw [hc₀]; positivity
  have hC : 0 ≤ ΦBoundConst / π * Real.exp (t0 ^ 2 / π) :=
    mul_nonneg (div_nonneg ΦBoundConst_nonneg Real.pi_pos.le) (Real.exp_pos _).le
  refine ⟨max 1 (ΦBoundConst / π * Real.exp (t0 ^ 2 / π) * Real.exp (2 / 3 * c₀ ^ (3 / 2 : ℝ))),
    2 / 3, le_max_left _ _, by norm_num, fun z ↦ ?_⟩
  have h := m1_norm_W_le_exp_rpow_norm t0 δ N z
  rw [← hc₀] at h
  have hz0 : 0 ≤ ‖z‖ := norm_nonneg z
  have hmax : ((c₀ + ‖z‖) / 2) ^ (3 / 2 : ℝ) ≤ c₀ ^ (3 / 2 : ℝ) + ‖z‖ ^ (3 / 2 : ℝ) := by
    rcases le_total c₀ ‖z‖ with hle | hle
    · calc ((c₀ + ‖z‖) / 2) ^ (3 / 2 : ℝ) ≤ ‖z‖ ^ (3 / 2 : ℝ) :=
            Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
        _ ≤ c₀ ^ (3 / 2 : ℝ) + ‖z‖ ^ (3 / 2 : ℝ) :=
            le_add_of_nonneg_left (Real.rpow_nonneg hc₀0 _)
    · calc ((c₀ + ‖z‖) / 2) ^ (3 / 2 : ℝ) ≤ c₀ ^ (3 / 2 : ℝ) :=
            Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
        _ ≤ c₀ ^ (3 / 2 : ℝ) + ‖z‖ ^ (3 / 2 : ℝ) :=
            le_add_of_nonneg_right (Real.rpow_nonneg hz0 _)
  calc ‖m1W t0 δ N z‖
      ≤ ΦBoundConst / π * Real.exp (t0 ^ 2 / π)
          * Real.exp (2 / 3 * ((c₀ + ‖z‖) / 2) ^ (3 / 2 : ℝ)) := h
    _ ≤ ΦBoundConst / π * Real.exp (t0 ^ 2 / π)
          * Real.exp (2 / 3 * (c₀ ^ (3 / 2 : ℝ) + ‖z‖ ^ (3 / 2 : ℝ))) := by
        gcongr
    _ = (ΦBoundConst / π * Real.exp (t0 ^ 2 / π) * Real.exp (2 / 3 * c₀ ^ (3 / 2 : ℝ)))
          * Real.exp (2 / 3 * ‖z‖ ^ (3 / 2 : ℝ)) := by
        rw [mul_add, Real.exp_add]; ring
    _ ≤ max 1 (ΦBoundConst / π * Real.exp (t0 ^ 2 / π) * Real.exp (2 / 3 * c₀ ^ (3 / 2 : ℝ)))
          * Real.exp (2 / 3 * ‖z‖ ^ (3 / 2 : ℝ)) := by
        gcongr
        exact le_max_right _ _

/-- **Every reweighted approximant carries even Hadamard data** (for every real `t0`, `δ`, `N`). -/
theorem m1_evenHadamardData_W (t0 δ : ℝ) (N : ℕ) : Nonempty (EvenHadamardData (m1W t0 δ N)) := by
  obtain ⟨A, B, hA, hB, hgrowth⟩ := m1_norm_W_le_growth t0 δ N
  exact evenHadamardData_of_order_lt_two (m1_differentiable_W t0 δ N) (m1W_neg t0 δ N)
    ⟨0, m1_W_zero_ne_zero t0 δ N⟩ hA hB (by norm_num) (by norm_num) hgrowth

/-! ### Convergence `m1G t0 s N → H (t0 + s)` -/

/-- The kernel-error integrand `(e^{su²} − cosh(√(2s/N) u)^N) e^{t0 u²} |Φ(u)| e^{Ru}`. -/
noncomputable def m1ErrIntegrand (t0 s R : ℝ) (N : ℕ) (u : ℝ) : ℝ :=
  (Real.exp (s * u ^ 2) - Real.cosh (Real.sqrt (2 * s / N) * u) ^ N)
    * (Real.exp (t0 * u ^ 2) * |Φ u| * Real.exp (R * u))

/-- The kernel error `∫_0^∞ (e^{su²} − cosh(√(2s/N) u)^N) e^{t0 u²} |Φ(u)| e^{Ru} du`, which
dominates `‖H (t0 + s) z − m1G t0 s N z‖` on the strip `|Im z| ≤ R`. -/
noncomputable def m1Err (t0 s R : ℝ) (N : ℕ) : ℝ := ∫ u in Ioi (0 : ℝ), m1ErrIntegrand t0 s R N u

lemma m1_continuous_ErrIntegrand (t0 s R : ℝ) (N : ℕ) : Continuous (m1ErrIntegrand t0 s R N) := by
  unfold m1ErrIntegrand
  fun_prop

lemma m1_ErrIntegrand_nonneg (t0 : ℝ) {s : ℝ} (hs : 0 ≤ s) (R : ℝ) (N : ℕ) (u : ℝ) :
    0 ≤ m1ErrIntegrand t0 s R N u := by
  unfold m1ErrIntegrand
  have := cosh_sqrt_pow_le hs N u
  have h : 0 ≤ Real.exp (s * u ^ 2) - Real.cosh (Real.sqrt (2 * s / N) * u) ^ N := by linarith
  positivity

lemma m1_ErrIntegrand_le (t0 s R : ℝ) (N : ℕ) (u : ℝ) :
    m1ErrIntegrand t0 s R N u ≤ Real.exp ((t0 + s) * u ^ 2 + R * u) * |Φ u| := by
  unfold m1ErrIntegrand
  have h0 : 0 ≤ Real.cosh (Real.sqrt (2 * s / N) * u) ^ N := pow_nonneg (Real.cosh_pos _).le N
  have h1 : Real.exp (s * u ^ 2) - Real.cosh (Real.sqrt (2 * s / N) * u) ^ N
      ≤ Real.exp (s * u ^ 2) := by linarith
  calc (Real.exp (s * u ^ 2) - Real.cosh (Real.sqrt (2 * s / N) * u) ^ N)
        * (Real.exp (t0 * u ^ 2) * |Φ u| * Real.exp (R * u))
      ≤ Real.exp (s * u ^ 2) * (Real.exp (t0 * u ^ 2) * |Φ u| * Real.exp (R * u)) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = Real.exp ((t0 + s) * u ^ 2 + R * u) * |Φ u| := by
        rw [add_mul, Real.exp_add, Real.exp_add]; ring

lemma m1_integrableOn_ErrIntegrand (t0 : ℝ) {s : ℝ} (hs : 0 ≤ s) (R : ℝ) (N : ℕ) :
    IntegrableOn (m1ErrIntegrand t0 s R N) (Ioi 0) := by
  refine (integrableOn_exp_mul_abs_Φ (t0 + s) R).mono'
    (m1_continuous_ErrIntegrand t0 s R N).aestronglyMeasurable ?_
  refine Eventually.of_forall fun u ↦ ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (m1_ErrIntegrand_nonneg t0 hs R N u)]
  exact m1_ErrIntegrand_le t0 s R N u

/-- **The reweighted kernel error tends to `0`** (dominated convergence, majorant
`e^{(t0+s)u² + Ru} |Φ(u)|`). -/
theorem m1_tendsto_Err (t0 : ℝ) {s : ℝ} (hs : 0 ≤ s) (R : ℝ) :
    Tendsto (m1Err t0 s R) atTop (𝓝 0) := by
  have h := tendsto_integral_of_dominated_convergence (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun N u ↦ m1ErrIntegrand t0 s R N u) (f := fun _ ↦ (0 : ℝ))
    (fun u ↦ Real.exp ((t0 + s) * u ^ 2 + R * u) * |Φ u|)
    (fun N ↦ (m1_continuous_ErrIntegrand t0 s R N).aestronglyMeasurable)
    (integrableOn_exp_mul_abs_Φ (t0 + s) R)
    (fun N ↦ Eventually.of_forall fun u ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (m1_ErrIntegrand_nonneg t0 hs R N u)]
      exact m1_ErrIntegrand_le t0 s R N u)
    (Eventually.of_forall fun u ↦ by
      have hk := tendsto_cosh_sqrt_pow hs u
      have := ((tendsto_const_nhds (x := Real.exp (s * u ^ 2))).sub hk).mul_const
        (Real.exp (t0 * u ^ 2) * |Φ u| * Real.exp (R * u))
      simpa [m1ErrIntegrand] using this)
  simp only [integral_zero] at h
  exact h

/-- The heat integrand at time `t0 + s` minus the reweighted integrand is the kernel difference
times the heat integrand at time `t0`. -/
lemma m1_HIntegrand_sub_WIntegrand (t0 s δ : ℝ) (N : ℕ) (z : ℂ) (u : ℝ) :
    HIntegrand (t0 + s) z u - m1WIntegrand t0 δ N z u
      = ((Real.exp (s * u ^ 2) - Real.cosh (δ * u) ^ N : ℝ) : ℂ) * HIntegrand t0 z u := by
  have he : Real.exp ((t0 + s) * u ^ 2) = Real.exp (s * u ^ 2) * Real.exp (t0 * u ^ 2) := by
    rw [← Real.exp_add]; congr 1; ring
  unfold m1WIntegrand HIntegrand
  rw [he]
  push_cast
  ring

/-- **Pointwise error bound on a strip**: for `s ≥ 0` and `|Im z| ≤ R`,
`‖H (t0 + s) z − m1G t0 s N z‖ ≤ m1Err t0 s R N`. -/
theorem m1_norm_H_sub_G_le (t0 : ℝ) {s : ℝ} (hs : 0 ≤ s) (N : ℕ) {z : ℂ} {R : ℝ}
    (hR : |z.im| ≤ R) : ‖H (t0 + s) z - m1G t0 s N z‖ ≤ m1Err t0 s R N := by
  unfold m1G m1W H m1Err
  rw [← integral_sub (integrableOn_HIntegrand (t0 + s) z) (m1_integrableOn_WIntegrand _ _ N z)]
  refine norm_integral_le_of_norm_le (m1_integrableOn_ErrIntegrand t0 hs R N) ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  refine Eventually.of_forall fun u hu ↦ ?_
  have hu0 : 0 ≤ u := le_of_lt hu
  have h2 : 0 ≤ Real.exp (s * u ^ 2) - Real.cosh (Real.sqrt (2 * s / N) * u) ^ N := by
    linarith [cosh_sqrt_pow_le hs N u]
  rw [m1_HIntegrand_sub_WIntegrand, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg h2]
  unfold m1ErrIntegrand
  refine mul_le_mul_of_nonneg_left ((m1_norm_HIntegrand_le t0 z hu0).trans ?_) h2
  gcongr

/-- **`m1G t0 s N → H (t0 + s)` uniformly on every horizontal strip `|Im z| ≤ R`** (`s ≥ 0`). -/
theorem m1_tendstoUniformlyOn_G (t0 : ℝ) {s : ℝ} (hs : 0 ≤ s) (R : ℝ) :
    TendstoUniformlyOn (m1G t0 s) (H (t0 + s)) atTop {z : ℂ | |z.im| ≤ R} := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [(m1_tendsto_Err t0 hs R).eventually_lt_const hε] with N hN z hz
  rw [dist_eq_norm]
  exact lt_of_le_of_lt (m1_norm_H_sub_G_le t0 hs N hz) hN

/-- **`m1G t0 s N → H (t0 + s)` locally uniformly on `ℂ`** (`s ≥ 0`, every real `t0`). -/
theorem m1_tendstoLocallyUniformly_G (t0 : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    TendstoLocallyUniformly (m1G t0 s) (H (t0 + s)) atTop := by
  intro u hu x
  refine ⟨{z : ℂ | |z.im| < |x.im| + 1}, ?_, ?_⟩
  · apply IsOpen.mem_nhds
    · exact isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const
    · simp
  · filter_upwards [m1_tendstoUniformlyOn_G t0 hs (|x.im| + 1) u hu] with N hN z hz
    exact hN z (le_of_lt hz)

end DBN
