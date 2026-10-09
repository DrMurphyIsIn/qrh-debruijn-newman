/-
  DBNHeatApprox -- the de Bruijn approximants of the heat flow `H_t` (Route C / C3, obligations
  L2a-L2d of telperion/docs/DESIGN_RH_dbn_debruijn_real_zeros_2026-09-22.md, sections 2.2-2.4),
  plus the Hurwitz transfer of "zero-free off the real axis" from the approximants to `H_t`.

  The approximants (memo section 2.2):

    Gδ δ N z := ∫_0^∞ cosh(δu)^N Φ(u) cos(zu) du,          G t N := Gδ (√(2t/N)) N,

  i.e. the heat kernel `e^{tu²}` is replaced by `cosh(u √(2t/N))^N`.  This is the
  vertical-shift-average discretisation, NOT the `(1 + tu²/N)^N` (`1 − ε D²`) one, which only
  preserves a zero strip and does not contract it (memo section 2.3, recorded footgun).

  What IS proved here (axiom-clean, see AxiomGuardDBN.lean):
    * L2a: every `Gδ δ N` integrand is integrable (`integrableOn_GδIntegrand`); `Gδ δ N` is
      entire (`differentiable_Gδ`), even (`Gδ_neg`), real (`Gδ_conj`, `Gδ_ofReal_im`), with the
      growth bound `‖Gδ δ N z‖ ≤ ∫_0^∞ cosh(δu)^N |Φ(u)| e^{|Im z| u} du` (`norm_Gδ_le`), which for
      `G t N` is dominated uniformly in `N` by `∫_0^∞ e^{tu²} |Φ(u)| e^{|Im z| u} du`
      (`norm_G_le`, `t ≥ 0`), and the explicit order bound
      `‖Gδ δ N z‖ ≤ (ΦBoundConst/π) exp((2/3)((9 + N|δ| + ‖z‖)/2)^{3/2})`
      (`norm_Gδ_le_exp_rpow_norm`): every approximant has order `≤ 3/2 < 2`, the growth input
      the Hadamard factorisation (L3) needs;
    * L2b: the shift identity `Gδ δ (N+1) = T_δ (Gδ δ N)` (`Gδ_succ`, `T_δ = DBN.shiftAvg δ`)
      and hence `Gδ δ N = T_δ^N (H 0)` (`Gδ_eq_iterate`);
    * L2c: `1 + x²/2 ≤ cosh x`, `cosh(u√(2t/N))^N → e^{tu²}` (squeeze against
      `(1 + tu²/N)^N`), and `G t N → H t` uniformly on every horizontal strip
      `|Im z| ≤ R` (`tendstoUniformlyOn_G`), hence locally uniformly on `ℂ`
      (`tendstoLocallyUniformly_G`), for every `t ≥ 0`;
    * L2d: `Φ(u) > 0` for every real `u` (`Φ_pos`), so `H t 0 > 0` and `Gδ δ N 0 > 0`
      (`H_zero_re_pos`, `Gδ_zero_re_pos`): the heat flow and the approximants are not identically
      zero.  (This replaces the memo's Fourier-uniqueness route to `H_t ≢ 0`: positivity of `Φ`
      at the single point `z = 0` suffices and needs no zeta input.)
    * Hurwitz transfer (`H_ne_zero_of_approx`): for `t ≥ 0`, if eventually every `G t N` has no
      zero off the real axis, then neither has `H t` (via `DBNHurwitz.hurwitz_ne_zero_of_entire`).

  What is NOT here: that the approximants `G t N` have only real zeros (that needs the zero strip
  of `H_0`, obligation L1, and the Hadamard factorisation, obligation L3, fed into the step lemma of
  `DBNStep.lean`); de Bruijn's theorem itself (registry node `RH.dbn_debruijn_real_zeros`, NOT
  stated here).  Nothing here proves RH.  conjecture1_proved = False.
-/
import DBNDefs
import DBNStep
import DBNHurwitz

open Real MeasureTheory Set Filter Topology ComplexConjugate

namespace DBN

/-! ### Elementary bounds -/

/-- `‖cos w‖ ≤ exp |Im w|`. -/
lemma norm_cos_le_exp_abs_im (w : ℂ) : ‖Complex.cos w‖ ≤ Real.exp |w.im| := by
  have h1 : ‖Complex.exp (w * Complex.I)‖ ≤ Real.exp |w.im| := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simp only [Complex.mul_re, Complex.I_re, mul_zero, Complex.I_im, mul_one, zero_sub]
    linarith [neg_abs_le w.im, le_abs_self w.im]
  have h2 : ‖Complex.exp (-w * Complex.I)‖ ≤ Real.exp |w.im| := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simp only [Complex.mul_re, Complex.neg_re, Complex.I_re, mul_zero, Complex.neg_im,
      Complex.I_im, mul_one, zero_sub, neg_neg]
    linarith [neg_abs_le w.im, le_abs_self w.im]
  calc ‖Complex.cos w‖
      = ‖(Complex.exp (w * Complex.I) + Complex.exp (-w * Complex.I)) / 2‖ := rfl
    _ = ‖Complex.exp (w * Complex.I) + Complex.exp (-w * Complex.I)‖ / 2 := by
        rw [norm_div, Complex.norm_two]
    _ ≤ (Real.exp |w.im| + Real.exp |w.im|) / 2 := by
        gcongr
        exact (norm_add_le _ _).trans (add_le_add h1 h2)
    _ = Real.exp |w.im| := by ring

/-- `‖cos(z u)‖ ≤ exp(|Im z| u)` for `u ≥ 0`. -/
lemma norm_cos_mul_le {u : ℝ} (hu : 0 ≤ u) (z : ℂ) :
    ‖Complex.cos (z * u)‖ ≤ Real.exp (|z.im| * u) := by
  refine (norm_cos_le_exp_abs_im _).trans (le_of_eq ?_)
  have him : (z * (u : ℂ)).im = z.im * u := by simp
  rw [him, abs_mul, abs_of_nonneg hu]

/-- `1 + x²/2 ≤ cosh x` (the first two terms of the cosh series). -/
lemma one_add_sq_div_two_le_cosh (x : ℝ) : 1 + x ^ 2 / 2 ≤ Real.cosh x := by
  have h := sum_le_hasSum (Finset.range 2)
    (fun n _ ↦ div_nonneg (by rw [pow_mul]; positivity) (by positivity)) (Real.hasSum_cosh x)
  simpa [Finset.sum_range_succ] using h

/-- `cosh(δu)^N ≤ exp(N δ² u² / 2)` (from `cosh x ≤ exp(x²/2)`). -/
lemma cosh_pow_le_exp (δ u : ℝ) (N : ℕ) :
    Real.cosh (δ * u) ^ N ≤ Real.exp (N * δ ^ 2 / 2 * u ^ 2) := by
  calc Real.cosh (δ * u) ^ N ≤ Real.exp ((δ * u) ^ 2 / 2) ^ N :=
        pow_le_pow_left₀ (Real.cosh_pos _).le (Real.cosh_le_exp_half_sq _) N
    _ = Real.exp (N * δ ^ 2 / 2 * u ^ 2) := by
        rw [← Real.exp_nat_mul]; congr 1; ring

/-- Integrability of `exp(a u² + b u) |Φ(u)|` on `(0, ∞)` (the island's universal majorant). -/
lemma integrableOn_exp_mul_abs_Φ (a b : ℝ) :
    IntegrableOn (fun u : ℝ ↦ Real.exp (a * u ^ 2 + b * u) * |Φ u|) (Ioi 0) := by
  have hg := (integrableOn_exp_quad_mul_exp_neg_exp a (b + 9)).const_mul ΦBoundConst
  have hcont : Continuous (fun u : ℝ ↦ Real.exp (a * u ^ 2 + b * u) * |Φ u|) := by fun_prop
  refine hg.mono' hcont.aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  refine Eventually.of_forall fun u hu ↦ ?_
  have hΦ := abs_Φ_le (le_of_lt hu)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc Real.exp (a * u ^ 2 + b * u) * |Φ u|
      ≤ Real.exp (a * u ^ 2 + b * u)
          * (ΦBoundConst * (Real.exp (9 * u) * Real.exp (-(π / 2) * Real.exp (4 * u)))) := by
        gcongr
    _ = ΦBoundConst * (Real.exp (a * u ^ 2 + (b + 9) * u)
          * Real.exp (-(π / 2) * Real.exp (4 * u))) := by
        have e : Real.exp (a * u ^ 2 + (b + 9) * u)
            = Real.exp (a * u ^ 2 + b * u) * Real.exp (9 * u) := by
          rw [← Real.exp_add]; ring_nf
        rw [e]
        ring

/-! ### L2a: the approximants `Gδ δ N` and `G t N` -/

/-- The integrand `cosh(δu)^N Φ(u) cos(zu)` of the approximant `Gδ δ N`. -/
noncomputable def GδIntegrand (δ : ℝ) (N : ℕ) (z : ℂ) (u : ℝ) : ℂ :=
  ((Real.cosh (δ * u) ^ N : ℝ) : ℂ) * ((Φ u : ℝ) : ℂ) * Complex.cos (z * u)

/-- `Gδ δ N z = ∫_0^∞ cosh(δu)^N Φ(u) cos(zu) du`. -/
noncomputable def Gδ (δ : ℝ) (N : ℕ) (z : ℂ) : ℂ := ∫ u in Ioi (0 : ℝ), GδIntegrand δ N z u

/-- The de Bruijn approximant `G t N z = ∫_0^∞ cosh(u √(2t/N))^N Φ(u) cos(zu) du`
(memo section 2.2; the kernel `cosh(u √(2t/N))^N` tends to `e^{tu²}`). -/
noncomputable def G (t : ℝ) (N : ℕ) : ℂ → ℂ := Gδ (Real.sqrt (2 * t / N)) N

@[fun_prop]
lemma continuous_GδIntegrand (δ : ℝ) (N : ℕ) (z : ℂ) : Continuous (GδIntegrand δ N z) := by
  unfold GδIntegrand
  fun_prop

/-- Pointwise majorant of the `Gδ` integrand on `u ≥ 0`. -/
lemma norm_GδIntegrand_le (δ : ℝ) (N : ℕ) (z : ℂ) {u : ℝ} (hu : 0 ≤ u) :
    ‖GδIntegrand δ N z u‖ ≤ ΦBoundConst * (Real.exp (N * δ ^ 2 / 2 * u ^ 2 + (9 + |z.im|) * u)
      * Real.exp (-(π / 2) * Real.exp (4 * u))) := by
  have hcos := norm_cos_mul_le hu z
  have hΦ := abs_Φ_le hu
  have hC := ΦBoundConst_nonneg
  have hch := cosh_pow_le_exp δ u N
  have hch0 : 0 ≤ Real.cosh (δ * u) ^ N := pow_nonneg (Real.cosh_pos _).le N
  unfold GδIntegrand
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_nonneg hch0]
  calc Real.cosh (δ * u) ^ N * |Φ u| * ‖Complex.cos (z * u)‖
      ≤ Real.exp (N * δ ^ 2 / 2 * u ^ 2)
          * (ΦBoundConst * (Real.exp (9 * u) * Real.exp (-(π / 2) * Real.exp (4 * u))))
          * Real.exp (|z.im| * u) := by gcongr
    _ = ΦBoundConst * (Real.exp (N * δ ^ 2 / 2 * u ^ 2 + (9 + |z.im|) * u)
          * Real.exp (-(π / 2) * Real.exp (4 * u))) := by
        rw [Real.exp_add, add_mul, Real.exp_add]; ring

/-- **L2a: the `Gδ` integrand is integrable on `(0, ∞)`** for every `δ`, `N`, `z`. -/
theorem integrableOn_GδIntegrand (δ : ℝ) (N : ℕ) (z : ℂ) :
    IntegrableOn (GδIntegrand δ N z) (Ioi 0) := by
  have hg := (integrableOn_exp_quad_mul_exp_neg_exp (N * δ ^ 2 / 2) (9 + |z.im|)).const_mul
    ΦBoundConst
  refine hg.mono' (continuous_GδIntegrand δ N z).aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  exact Eventually.of_forall fun u hu ↦ norm_GδIntegrand_le δ N z (le_of_lt hu)

/-! ### L2b: the shift identity `Gδ δ (N+1) = T_δ (Gδ δ N)` -/

/-- Pointwise shift identity: `cos((z+iδ)u) + cos((z−iδ)u) = 2 cos(zu) cosh(δu)`. -/
lemma GδIntegrand_succ (δ : ℝ) (N : ℕ) (z : ℂ) (u : ℝ) :
    GδIntegrand δ (N + 1) z u
      = (GδIntegrand δ N (z + Complex.I * δ) u + GδIntegrand δ N (z - Complex.I * δ) u) / 2 := by
  have hcos : Complex.cos ((z + Complex.I * δ) * u) + Complex.cos ((z - Complex.I * δ) * u)
      = 2 * Complex.cos (z * u) * ((Real.cosh (δ * u) : ℝ) : ℂ) := by
    rw [Complex.cos_add_cos, Complex.ofReal_cosh]
    have e1 : ((z + Complex.I * δ) * u + (z - Complex.I * δ) * u) / 2 = z * u := by ring
    have e2 : ((z + Complex.I * δ) * u - (z - Complex.I * δ) * u) / 2
        = ((δ * u : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [e1, e2, Complex.cos_mul_I]
  unfold GδIntegrand
  rw [show ((Real.cosh (δ * u) ^ N : ℝ) : ℂ) * ((Φ u : ℝ) : ℂ) * Complex.cos ((z + Complex.I * δ) * u)
      + ((Real.cosh (δ * u) ^ N : ℝ) : ℂ) * ((Φ u : ℝ) : ℂ) * Complex.cos ((z - Complex.I * δ) * u)
      = ((Real.cosh (δ * u) ^ N : ℝ) : ℂ) * ((Φ u : ℝ) : ℂ)
        * (Complex.cos ((z + Complex.I * δ) * u) + Complex.cos ((z - Complex.I * δ) * u)) by ring,
    hcos]
  push_cast
  ring

/-- **L2b: the shift identity.**  Multiplying the kernel by `cosh(δu)` is the vertical-shift
average on the function side: `Gδ δ (N+1) = T_δ (Gδ δ N)`. -/
theorem Gδ_succ (δ : ℝ) (N : ℕ) : Gδ δ (N + 1) = shiftAvg δ (Gδ δ N) := by
  funext z
  unfold Gδ shiftAvg
  simp_rw [GδIntegrand_succ]
  rw [integral_div, integral_add (integrableOn_GδIntegrand _ _ _) (integrableOn_GδIntegrand _ _ _)]

/-- `Gδ δ 0 = H 0` (no kernel weight). -/
theorem Gδ_zero (δ : ℝ) : Gδ δ 0 = H 0 := by
  funext z
  unfold Gδ H GδIntegrand HIntegrand
  congr 1
  funext u
  simp

/-- **L2b, iterated: `Gδ δ N = T_δ^N (H 0)`.** -/
theorem Gδ_eq_iterate (δ : ℝ) (N : ℕ) : Gδ δ N = (shiftAvg δ)^[N] (H 0) := by
  induction N with
  | zero => simp [Gδ_zero]
  | succ N ih => rw [Gδ_succ, ih, Function.iterate_succ_apply']

/-- **L2a: `Gδ δ N` is entire** (by the shift identity, from `differentiable_H 0`). -/
theorem differentiable_Gδ (δ : ℝ) (N : ℕ) : Differentiable ℂ (Gδ δ N) := by
  induction N with
  | zero => rw [Gδ_zero]; exact differentiable_H 0
  | succ N ih => rw [Gδ_succ]; exact differentiable_shiftAvg ih δ

/-- **L2a: `Gδ δ N` is even.** -/
theorem Gδ_neg (δ : ℝ) (N : ℕ) (z : ℂ) : Gδ δ N (-z) = Gδ δ N z := by
  unfold Gδ GδIntegrand
  simp only [neg_mul, Complex.cos_neg]

/-- **L2a: `Gδ δ N` is real**: `Gδ δ N (conj z) = conj (Gδ δ N z)` (Schwarz reflection). -/
theorem Gδ_conj (δ : ℝ) (N : ℕ) (z : ℂ) : Gδ δ N (conj z) = conj (Gδ δ N z) := by
  unfold Gδ
  rw [← integral_conj]
  congr 1
  funext u
  unfold GδIntegrand
  rw [map_mul, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, ← Complex.cos_conj, map_mul,
    Complex.conj_ofReal]

/-- **L2a: `Gδ δ N` is real on the real axis.** -/
theorem Gδ_ofReal_im (δ : ℝ) (N : ℕ) (x : ℝ) : (Gδ δ N x).im = 0 := by
  have h := congrArg Complex.im (Gδ_conj δ N x)
  rw [Complex.conj_ofReal, Complex.conj_im] at h
  linarith

/-- **L2a: growth bound for `Gδ`**: `‖Gδ δ N z‖ ≤ ∫_0^∞ cosh(δu)^N |Φ(u)| e^{|Im z| u} du`. -/
theorem norm_Gδ_le (δ : ℝ) (N : ℕ) (z : ℂ) :
    ‖Gδ δ N z‖ ≤ ∫ u in Ioi (0 : ℝ), Real.cosh (δ * u) ^ N * |Φ u| * Real.exp (|z.im| * u) := by
  unfold Gδ
  refine norm_integral_le_of_norm_le ?_ ?_
  · refine (integrableOn_exp_mul_abs_Φ (N * δ ^ 2 / 2) |z.im|).mono'
      (by fun_prop : Continuous (fun u : ℝ ↦
        Real.cosh (δ * u) ^ N * |Φ u| * Real.exp (|z.im| * u))).aestronglyMeasurable ?_
    refine Eventually.of_forall fun u ↦ ?_
    have hch := cosh_pow_le_exp δ u N
    have hch0 : 0 ≤ Real.cosh (δ * u) ^ N := pow_nonneg (Real.cosh_pos _).le N
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), Real.exp_add]
    calc Real.cosh (δ * u) ^ N * |Φ u| * Real.exp (|z.im| * u)
        ≤ Real.exp (N * δ ^ 2 / 2 * u ^ 2) * |Φ u| * Real.exp (|z.im| * u) := by gcongr
      _ = Real.exp (N * δ ^ 2 / 2 * u ^ 2) * Real.exp (|z.im| * u) * |Φ u| := by ring
  · rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun u hu ↦ ?_
    have hch0 : 0 ≤ Real.cosh (δ * u) ^ N := pow_nonneg (Real.cosh_pos _).le N
    unfold GδIntegrand
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg hch0]
    gcongr
    exact norm_cos_mul_le (le_of_lt hu) z

/-! ### L2a: an explicit order bound (`≤ 3/2`) for the approximants -/

/-- `cosh x ≤ exp |x|`. -/
lemma cosh_le_exp_abs (x : ℝ) : Real.cosh x ≤ Real.exp |x| := by
  rw [Real.cosh_eq]
  have h1 : Real.exp x ≤ Real.exp |x| := Real.exp_le_exp.mpr (le_abs_self x)
  have h2 : Real.exp (-x) ≤ Real.exp |x| := Real.exp_le_exp.mpr (neg_le_abs x)
  linarith

/-- Young's inequality in the form used for the order bound:
`A u ≤ (2/3) (A/2)^{3/2} + (8/3) u³` for `A, u ≥ 0`. -/
lemma mul_le_rpow_add_cube {A u : ℝ} (hA : 0 ≤ A) (hu : 0 ≤ u) :
    A * u ≤ 2 / 3 * (A / 2) ^ (3 / 2 : ℝ) + 8 / 3 * u ^ 3 := by
  have hpq : (3 / 2 : ℝ).HolderConjugate 3 :=
    (Real.holderConjugate_iff_eq_conjExponent (by norm_num)).mpr (by norm_num)
  have h := Real.young_inequality_of_nonneg (by positivity : 0 ≤ A / 2)
    (by positivity : 0 ≤ 2 * u) hpq
  have h3 : (2 * u) ^ (3 : ℝ) = (2 * u) ^ 3 := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [h3] at h
  calc A * u = A / 2 * (2 * u) := by ring
    _ ≤ (A / 2) ^ (3 / 2 : ℝ) / (3 / 2) + (2 * u) ^ 3 / 3 := h
    _ = 2 / 3 * (A / 2) ^ (3 / 2 : ℝ) + 8 / 3 * u ^ 3 := by ring

/-- `(8/3) u³ + π u ≤ (π/2) e^{4u}` for `u ≥ 0` (four terms of the exponential series). -/
lemma cube_add_le_exp {u : ℝ} (hu : 0 ≤ u) :
    8 / 3 * u ^ 3 + π * u ≤ π / 2 * Real.exp (4 * u) := by
  have h := Real.sum_le_exp_of_nonneg (by positivity : (0 : ℝ) ≤ 4 * u) 4
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  norm_num at h
  have hπ : 3 < π := Real.pi_gt_three
  have hu3 : 0 ≤ u ^ 3 := by positivity
  have hu2 : 0 ≤ u ^ 2 := by positivity
  nlinarith [mul_nonneg (le_of_lt Real.pi_pos) hu3, mul_nonneg (le_of_lt Real.pi_pos) hu2,
    mul_nonneg (le_of_lt Real.pi_pos) hu]

/-- Pointwise majorant of the `Gδ` integrand with integrable, `z`-free decay:
`‖GδIntegrand δ N z u‖ ≤ ΦBoundConst · exp((2/3)(A/2)^{3/2}) · e^{−πu}`,
`A = 9 + N |δ| + |Im z|`, for `u ≥ 0`. -/
lemma norm_GδIntegrand_le_rpow (δ : ℝ) (N : ℕ) (z : ℂ) {u : ℝ} (hu : 0 ≤ u) :
    ‖GδIntegrand δ N z u‖ ≤ ΦBoundConst
      * Real.exp (2 / 3 * ((9 + N * |δ| + |z.im|) / 2) ^ (3 / 2 : ℝ)) * Real.exp (-π * u) := by
  set A : ℝ := 9 + N * |δ| + |z.im| with hA_def
  have hA : 0 ≤ A := by positivity
  have hcos := norm_cos_mul_le hu z
  have hΦ := abs_Φ_le hu
  have hC := ΦBoundConst_nonneg
  have hch : Real.cosh (δ * u) ^ N ≤ Real.exp (N * |δ| * u) := by
    calc Real.cosh (δ * u) ^ N ≤ Real.exp |δ * u| ^ N :=
          pow_le_pow_left₀ (Real.cosh_pos _).le (cosh_le_exp_abs _) N
      _ = Real.exp (N * |δ| * u) := by
          rw [← Real.exp_nat_mul, abs_mul, abs_of_nonneg hu]; ring_nf
  have hch0 : 0 ≤ Real.cosh (δ * u) ^ N := pow_nonneg (Real.cosh_pos _).le N
  have hkey : A * u - π / 2 * Real.exp (4 * u)
      ≤ 2 / 3 * (A / 2) ^ (3 / 2 : ℝ) + -π * u := by
    have h1 := mul_le_rpow_add_cube hA hu
    have h2 := cube_add_le_exp hu
    linarith
  unfold GδIntegrand
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_nonneg hch0]
  calc Real.cosh (δ * u) ^ N * |Φ u| * ‖Complex.cos (z * u)‖
      ≤ Real.exp (N * |δ| * u)
          * (ΦBoundConst * (Real.exp (9 * u) * Real.exp (-(π / 2) * Real.exp (4 * u))))
          * Real.exp (|z.im| * u) := by gcongr
    _ = ΦBoundConst * Real.exp (A * u - π / 2 * Real.exp (4 * u)) := by
        have e : Real.exp (A * u - π / 2 * Real.exp (4 * u))
            = Real.exp (N * |δ| * u) * Real.exp (9 * u) * Real.exp (-(π / 2) * Real.exp (4 * u))
              * Real.exp (|z.im| * u) := by
          rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, hA_def]
          ring_nf
        rw [e]
        ring
    _ ≤ ΦBoundConst * Real.exp (2 / 3 * (A / 2) ^ (3 / 2 : ℝ) + -π * u) := by gcongr
    _ = ΦBoundConst * Real.exp (2 / 3 * (A / 2) ^ (3 / 2 : ℝ)) * Real.exp (-π * u) := by
        rw [Real.exp_add]; ring

/-- **L2a: order bound `≤ 3/2`.**  With `A = 9 + N |δ| + |Im z|`,
`‖Gδ δ N z‖ ≤ (ΦBoundConst / π) · exp((2/3) (A/2)^{3/2})`.  So every approximant `Gδ δ N` is an
entire function of order at most `3/2 < 2` -- the growth input of the Hadamard factorisation
(obligation L3; NOT proved here). -/
theorem norm_Gδ_le_exp_rpow (δ : ℝ) (N : ℕ) (z : ℂ) :
    ‖Gδ δ N z‖ ≤ ΦBoundConst / π
      * Real.exp (2 / 3 * ((9 + N * |δ| + |z.im|) / 2) ^ (3 / 2 : ℝ)) := by
  set E : ℝ := Real.exp (2 / 3 * ((9 + N * |δ| + |z.im|) / 2) ^ (3 / 2 : ℝ)) with hE
  have hint : IntegrableOn (fun u : ℝ ↦ ΦBoundConst * E * Real.exp (-π * u)) (Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 Real.pi_pos).const_mul _
  unfold Gδ
  refine (norm_integral_le_of_norm_le hint ?_).trans (le_of_eq ?_)
  · rw [ae_restrict_iff' measurableSet_Ioi]
    exact Eventually.of_forall fun u hu ↦ norm_GδIntegrand_le_rpow δ N z (le_of_lt hu)
  · rw [integral_const_mul, integral_exp_mul_Ioi (by linarith [Real.pi_pos]) 0]
    simp only [mul_zero, Real.exp_zero]
    field_simp

/-- **L2a: order bound `≤ 3/2`, in `‖z‖`**:
`‖Gδ δ N z‖ ≤ (ΦBoundConst / π) · exp((2/3) ((9 + N |δ| + ‖z‖)/2)^{3/2})`. -/
theorem norm_Gδ_le_exp_rpow_norm (δ : ℝ) (N : ℕ) (z : ℂ) :
    ‖Gδ δ N z‖ ≤ ΦBoundConst / π
      * Real.exp (2 / 3 * ((9 + N * |δ| + ‖z‖) / 2) ^ (3 / 2 : ℝ)) := by
  refine (norm_Gδ_le_exp_rpow δ N z).trans ?_
  have hC : 0 ≤ ΦBoundConst / π := div_nonneg ΦBoundConst_nonneg Real.pi_pos.le
  gcongr
  exact Complex.abs_im_le_norm z

/-! ### L2c: convergence of the kernels and of the approximants -/

/-- For `t ≥ 0`: `cosh(√(2t/N) u)^N ≤ exp(t u²)` (for every `N`, including `N = 0`). -/
lemma cosh_sqrt_pow_le {t : ℝ} (ht : 0 ≤ t) (N : ℕ) (u : ℝ) :
    Real.cosh (Real.sqrt (2 * t / N) * u) ^ N ≤ Real.exp (t * u ^ 2) := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    simp only [pow_zero]
    exact Real.one_le_exp (by positivity)
  · refine (cosh_pow_le_exp _ u N).trans (le_of_eq ?_)
    have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    rw [Real.sq_sqrt (by positivity)]
    congr 1
    field_simp

/-- For `t ≥ 0`: `(1 + t u²/N)^N ≤ cosh(√(2t/N) u)^N` (from `1 + x²/2 ≤ cosh x`). -/
lemma one_add_div_pow_le_cosh_sqrt_pow {t : ℝ} (ht : 0 ≤ t) (N : ℕ) (u : ℝ) :
    (1 + t * u ^ 2 / N) ^ N ≤ Real.cosh (Real.sqrt (2 * t / N) * u) ^ N := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    simp
  · apply pow_le_pow_left₀ (by positivity)
    refine le_trans (le_of_eq ?_) (one_add_sq_div_two_le_cosh _)
    have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    field_simp

/-- **L2c: the kernels converge**: `cosh(√(2t/N) u)^N → e^{tu²}` for `t ≥ 0`. -/
theorem tendsto_cosh_sqrt_pow {t : ℝ} (ht : 0 ≤ t) (u : ℝ) :
    Tendsto (fun N : ℕ ↦ Real.cosh (Real.sqrt (2 * t / N) * u) ^ N) atTop
      (𝓝 (Real.exp (t * u ^ 2))) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le (Real.tendsto_one_add_div_pow_exp (t * u ^ 2))
    tendsto_const_nhds (fun N ↦ one_add_div_pow_le_cosh_sqrt_pow ht N u)
    (fun N ↦ cosh_sqrt_pow_le ht N u)

/-- The kernel-error integrand `(e^{tu²} − cosh(√(2t/N) u)^N) |Φ(u)| e^{Ru}`. -/
noncomputable def approxErrIntegrand (t R : ℝ) (N : ℕ) (u : ℝ) : ℝ :=
  (Real.exp (t * u ^ 2) - Real.cosh (Real.sqrt (2 * t / N) * u) ^ N) * |Φ u| * Real.exp (R * u)

/-- The kernel error `∫_0^∞ (e^{tu²} − cosh(√(2t/N) u)^N) |Φ(u)| e^{Ru} du`, which dominates
`‖H t z − G t N z‖` on the strip `|Im z| ≤ R`. -/
noncomputable def approxErr (t R : ℝ) (N : ℕ) : ℝ :=
  ∫ u in Ioi (0 : ℝ), approxErrIntegrand t R N u

lemma continuous_approxErrIntegrand (t R : ℝ) (N : ℕ) : Continuous (approxErrIntegrand t R N) := by
  unfold approxErrIntegrand
  fun_prop

lemma approxErrIntegrand_nonneg {t : ℝ} (ht : 0 ≤ t) (R : ℝ) (N : ℕ) (u : ℝ) :
    0 ≤ approxErrIntegrand t R N u := by
  unfold approxErrIntegrand
  have := cosh_sqrt_pow_le ht N u
  have h : 0 ≤ Real.exp (t * u ^ 2) - Real.cosh (Real.sqrt (2 * t / N) * u) ^ N := by linarith
  positivity

lemma approxErrIntegrand_le {t : ℝ} (ht : 0 ≤ t) (R : ℝ) (N : ℕ) (u : ℝ) :
    approxErrIntegrand t R N u ≤ Real.exp (t * u ^ 2 + R * u) * |Φ u| := by
  unfold approxErrIntegrand
  have h0 : 0 ≤ Real.cosh (Real.sqrt (2 * t / N) * u) ^ N := pow_nonneg (Real.cosh_pos _).le N
  have h1 : Real.exp (t * u ^ 2) - Real.cosh (Real.sqrt (2 * t / N) * u) ^ N
      ≤ Real.exp (t * u ^ 2) := by linarith
  have h2 : 0 ≤ Real.exp (t * u ^ 2) - Real.cosh (Real.sqrt (2 * t / N) * u) ^ N := by
    linarith [cosh_sqrt_pow_le ht N u]
  calc (Real.exp (t * u ^ 2) - Real.cosh (Real.sqrt (2 * t / N) * u) ^ N) * |Φ u|
        * Real.exp (R * u)
      ≤ Real.exp (t * u ^ 2) * |Φ u| * Real.exp (R * u) := by gcongr
    _ = Real.exp (t * u ^ 2 + R * u) * |Φ u| := by rw [Real.exp_add]; ring

lemma integrableOn_approxErrIntegrand {t : ℝ} (ht : 0 ≤ t) (R : ℝ) (N : ℕ) :
    IntegrableOn (approxErrIntegrand t R N) (Ioi 0) := by
  refine (integrableOn_exp_mul_abs_Φ t R).mono'
    (continuous_approxErrIntegrand t R N).aestronglyMeasurable ?_
  refine Eventually.of_forall fun u ↦ ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (approxErrIntegrand_nonneg ht R N u)]
  exact approxErrIntegrand_le ht R N u

/-- **L2c: the kernel error tends to `0`** (dominated convergence, majorant
`e^{tu² + Ru} |Φ(u)|`). -/
theorem tendsto_approxErr {t : ℝ} (ht : 0 ≤ t) (R : ℝ) :
    Tendsto (approxErr t R) atTop (𝓝 0) := by
  have h := tendsto_integral_of_dominated_convergence (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun N u ↦ approxErrIntegrand t R N u) (f := fun _ ↦ (0 : ℝ))
    (fun u ↦ Real.exp (t * u ^ 2 + R * u) * |Φ u|)
    (fun N ↦ (continuous_approxErrIntegrand t R N).aestronglyMeasurable)
    (integrableOn_exp_mul_abs_Φ t R)
    (fun N ↦ Eventually.of_forall fun u ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (approxErrIntegrand_nonneg ht R N u)]
      exact approxErrIntegrand_le ht R N u)
    (Eventually.of_forall fun u ↦ by
      have hk := tendsto_cosh_sqrt_pow ht u
      have := ((tendsto_const_nhds (x := Real.exp (t * u ^ 2))).sub hk).mul_const (|Φ u|)
        |>.mul_const (Real.exp (R * u))
      simpa [approxErrIntegrand] using this)
  simp only [integral_zero] at h
  exact h

/-- **L2c: pointwise error bound on a strip**: for `t ≥ 0` and `|Im z| ≤ R`,
`‖H t z − G t N z‖ ≤ approxErr t R N`. -/
theorem norm_H_sub_G_le {t : ℝ} (ht : 0 ≤ t) (N : ℕ) {z : ℂ} {R : ℝ} (hR : |z.im| ≤ R) :
    ‖H t z - G t N z‖ ≤ approxErr t R N := by
  unfold G Gδ H approxErr
  rw [← integral_sub (integrableOn_HIntegrand t z) (integrableOn_GδIntegrand _ N z)]
  refine norm_integral_le_of_norm_le (integrableOn_approxErrIntegrand ht R N) ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  refine Eventually.of_forall fun u hu ↦ ?_
  have hu0 : 0 ≤ u := le_of_lt hu
  have h2 : 0 ≤ Real.exp (t * u ^ 2) - Real.cosh (Real.sqrt (2 * t / N) * u) ^ N := by
    linarith [cosh_sqrt_pow_le ht N u]
  have hdiff : HIntegrand t z u - GδIntegrand (Real.sqrt (2 * t / N)) N z u
      = (((Real.exp (t * u ^ 2) - Real.cosh (Real.sqrt (2 * t / N) * u) ^ N : ℝ)) : ℂ)
        * ((Φ u : ℝ) : ℂ) * Complex.cos (z * u) := by
    unfold HIntegrand GδIntegrand
    push_cast
    ring
  rw [hdiff, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_nonneg h2]
  unfold approxErrIntegrand
  gcongr
  refine (norm_cos_mul_le hu0 z).trans (Real.exp_le_exp.mpr ?_)
  exact mul_le_mul_of_nonneg_right hR hu0

/-- **L2c: `G t N → H t` uniformly on every horizontal strip `|Im z| ≤ R`** (`t ≥ 0`). -/
theorem tendstoUniformlyOn_G {t : ℝ} (ht : 0 ≤ t) (R : ℝ) :
    TendstoUniformlyOn (G t) (H t) atTop {z : ℂ | |z.im| ≤ R} := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [(tendsto_approxErr ht R).eventually_lt_const hε] with N hN z hz
  rw [dist_eq_norm]
  exact lt_of_le_of_lt (norm_H_sub_G_le ht N hz) hN

/-- **L2c: `G t N → H t` locally uniformly on `ℂ`** (`t ≥ 0`). -/
theorem tendstoLocallyUniformly_G {t : ℝ} (ht : 0 ≤ t) :
    TendstoLocallyUniformly (G t) (H t) atTop := by
  intro u hu x
  refine ⟨{z : ℂ | |z.im| < |x.im| + 1}, ?_, ?_⟩
  · apply IsOpen.mem_nhds
    · exact isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const
    · simp
  · filter_upwards [tendstoUniformlyOn_G ht (|x.im| + 1) u hu] with N hN z hz
    exact hN z (le_of_lt hz)

/-- **L2a: growth bound uniform in `N`** (`t ≥ 0`):
`‖G t N z‖ ≤ ∫_0^∞ e^{tu²} |Φ(u)| e^{|Im z| u} du`. -/
theorem norm_G_le {t : ℝ} (ht : 0 ≤ t) (N : ℕ) (z : ℂ) :
    ‖G t N z‖ ≤ ∫ u in Ioi (0 : ℝ), Real.exp (t * u ^ 2) * |Φ u| * Real.exp (|z.im| * u) := by
  refine (norm_Gδ_le _ N z).trans (setIntegral_mono_on ?_ ?_ measurableSet_Ioi ?_)
  · refine (integrableOn_exp_mul_abs_Φ (N * Real.sqrt (2 * t / N) ^ 2 / 2) |z.im|).mono'
      (by fun_prop : Continuous (fun u : ℝ ↦ Real.cosh (Real.sqrt (2 * t / N) * u) ^ N * |Φ u|
        * Real.exp (|z.im| * u))).aestronglyMeasurable ?_
    refine Eventually.of_forall fun u ↦ ?_
    have hch := cosh_pow_le_exp (Real.sqrt (2 * t / N)) u N
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), Real.exp_add]
    calc Real.cosh (Real.sqrt (2 * t / N) * u) ^ N * |Φ u| * Real.exp (|z.im| * u)
        ≤ Real.exp (N * Real.sqrt (2 * t / N) ^ 2 / 2 * u ^ 2) * |Φ u| * Real.exp (|z.im| * u) := by
          gcongr
      _ = Real.exp (N * Real.sqrt (2 * t / N) ^ 2 / 2 * u ^ 2) * Real.exp (|z.im| * u) * |Φ u| := by
          ring
  · refine (integrableOn_exp_mul_abs_Φ t |z.im|).congr_fun (fun u _ ↦ ?_) measurableSet_Ioi
    dsimp only
    rw [Real.exp_add]; ring
  · intro u _
    gcongr
    exact cosh_sqrt_pow_le ht N u

/-! ### L2d: positivity of `Φ`; `H t` and `Gδ δ N` are not identically zero -/

/-- The terms of the `Φ` series are positive for `u ≥ 0`
(`2π²n⁴e^{9u} − 3πn²e^{5u} = πn²e^{5u}(2πn²e^{4u} − 3)` and `2π > 3`). -/
lemma Φ_term_pos {u : ℝ} (hu : 0 ≤ u) (n : ℕ+) :
    0 < (2 * π ^ 2 * (n : ℝ) ^ 4 * Real.exp (9 * u) - 3 * π * (n : ℝ) ^ 2 * Real.exp (5 * u))
      * Real.exp (-π * (n : ℝ) ^ 2 * Real.exp (4 * u)) := by
  apply mul_pos _ (Real.exp_pos _)
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := Nat.one_le_cast.mpr n.pos
  have hn2 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have he : Real.exp (9 * u) = Real.exp (4 * u) * Real.exp (5 * u) := by
    rw [← Real.exp_add]; ring_nf
  have h4 : 1 ≤ Real.exp (4 * u) := Real.one_le_exp (by linarith)
  have hπ : 3 < π := Real.pi_gt_three
  have hprod : 1 ≤ (n : ℝ) ^ 2 * Real.exp (4 * u) := by nlinarith
  have key : 0 < 2 * π * ((n : ℝ) ^ 2 * Real.exp (4 * u)) - 3 := by nlinarith
  have hfac : 2 * π ^ 2 * (n : ℝ) ^ 4 * Real.exp (9 * u) - 3 * π * (n : ℝ) ^ 2 * Real.exp (5 * u)
      = (π * (n : ℝ) ^ 2 * Real.exp (5 * u)) * (2 * π * ((n : ℝ) ^ 2 * Real.exp (4 * u)) - 3) := by
    rw [he]; ring
  rw [hfac]
  have : 0 < π * (n : ℝ) ^ 2 * Real.exp (5 * u) := by positivity
  positivity

/-- **`Φ` is positive** on all of `ℝ` (termwise for `u ≥ 0`, then by evenness). -/
theorem Φ_pos (u : ℝ) : 0 < Φ u := by
  wlog hu : 0 ≤ u generalizing u
  · rw [← Φ_neg]
    exact this (-u) (by linarith)
  unfold Φ
  exact (summable_Φ_term u).tsum_pos (fun n ↦ (Φ_term_pos hu n).le) 1 (Φ_term_pos hu 1)

/-- Positivity of a real weighted `Φ`-integral. -/
lemma setIntegral_weight_mul_Φ_pos {w : ℝ → ℝ} (hwpos : ∀ u, 0 < w u)
    (hint : IntegrableOn (fun u ↦ w u * Φ u) (Ioi 0)) :
    0 < ∫ u in Ioi (0 : ℝ), w u * Φ u := by
  rw [setIntegral_pos_iff_support_of_nonneg_ae
    (Eventually.of_forall fun u ↦ (mul_pos (hwpos u) (Φ_pos u)).le) hint]
  have hsupp : Function.support (fun u ↦ w u * Φ u) = univ := by
    ext u
    simp only [Function.mem_support, mem_univ, iff_true]
    exact (mul_pos (hwpos u) (Φ_pos u)).ne'
  rw [hsupp, univ_inter, Real.volume_Ioi]
  exact ENNReal.zero_lt_top

/-- **L2d: `H t 0 > 0`**, so `H t` is not identically zero (every real `t`). -/
theorem H_zero_re_pos (t : ℝ) : 0 < (H t 0).re := by
  have h0 : H t 0 = ((∫ u in Ioi (0 : ℝ), Real.exp (t * u ^ 2) * Φ u : ℝ) : ℂ) := by
    have := H_ofReal t 0
    simp only [Complex.ofReal_zero, zero_mul, Real.cos_zero, mul_one] at this
    exact this
  rw [h0, Complex.ofReal_re]
  refine setIntegral_weight_mul_Φ_pos (fun u ↦ Real.exp_pos _) ?_
  refine (integrableOn_exp_mul_abs_Φ t 0).congr_fun (fun u _ ↦ ?_) measurableSet_Ioi
  dsimp only
  rw [abs_of_pos (Φ_pos u), zero_mul, add_zero]

theorem H_zero_ne_zero (t : ℝ) : H t 0 ≠ 0 := by
  intro h
  have := H_zero_re_pos t
  rw [h, Complex.zero_re] at this
  exact lt_irrefl _ this

/-- **L2d: `Gδ δ N 0 > 0`**, so every approximant is not identically zero. -/
theorem Gδ_zero_re_pos (δ : ℝ) (N : ℕ) : 0 < (Gδ δ N 0).re := by
  have hfun : (fun u ↦ GδIntegrand δ N 0 u)
      = fun u ↦ ((Real.cosh (δ * u) ^ N * Φ u : ℝ) : ℂ) := by
    funext u
    unfold GδIntegrand
    push_cast
    simp
  have h0 : Gδ δ N 0 = ((∫ u in Ioi (0 : ℝ), Real.cosh (δ * u) ^ N * Φ u : ℝ) : ℂ) := by
    unfold Gδ
    rw [hfun]
    exact integral_ofReal
  rw [h0, Complex.ofReal_re]
  refine setIntegral_weight_mul_Φ_pos (fun u ↦ pow_pos (Real.cosh_pos _) N) ?_
  refine (integrableOn_exp_mul_abs_Φ (N * δ ^ 2 / 2) 0).mono'
    (by fun_prop : Continuous (fun u : ℝ ↦ Real.cosh (δ * u) ^ N * Φ u)).aestronglyMeasurable ?_
  refine Eventually.of_forall fun u ↦ ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg (Real.cosh_pos _).le N), zero_mul,
    add_zero]
  gcongr
  exact cosh_pow_le_exp δ u N

/-! ### The Hurwitz transfer to `H t` -/

/-- **Closure step (memo section 2.4, Hurwitz), general open set**: for `t ≥ 0` and an open set
`U`, if eventually (in `N`) every approximant `G t N` has no zero in `U`, then `H t` has no zero
in `U`.  CONDITIONAL transfer; see `H_ne_zero_of_approx`. -/
theorem H_ne_zero_of_approx_on {t : ℝ} (ht : 0 ≤ t) {U : Set ℂ} (hU : IsOpen U)
    (hG : ∀ᶠ N in atTop, ∀ z ∈ U, G t N z ≠ 0) {z : ℂ} (hz : z ∈ U) : H t z ≠ 0 :=
  hurwitz_ne_zero_of_entire hU (fun N ↦ differentiable_Gδ _ N) hG (differentiable_H t)
    (tendstoLocallyUniformly_G ht) ⟨0, H_zero_ne_zero t⟩ hz

/-- **Closure step (memo section 2.4, Hurwitz)**: for `t ≥ 0`, if eventually (in `N`) every
approximant `G t N` has no zero off the real axis, then `H t` has no zero off the real axis.

This is a CONDITIONAL transfer: that the approximants have only real zeros is the step lemma of
`DBNStep.lean` fed with the zero strip of `H_0` (L1) and Hadamard data (L3), neither of which is
proved on this island.  It is NOT de Bruijn's theorem and NOT the registry node. -/
theorem H_ne_zero_of_approx {t : ℝ} (ht : 0 ≤ t)
    (hG : ∀ᶠ N in atTop, ∀ z : ℂ, z.im ≠ 0 → G t N z ≠ 0) {z : ℂ} (hz : z.im ≠ 0) :
    H t z ≠ 0 :=
  H_ne_zero_of_approx_on ht (U := {z : ℂ | z.im ≠ 0})
    (isOpen_ne_fun Complex.continuous_im continuous_const) (hG.mono fun _ hN w hw ↦ hN w hw) hz

end DBN
