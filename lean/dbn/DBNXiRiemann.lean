/-
  DBNXiRiemann -- Route C / C2, module A of the design memo
  telperion/docs/DESIGN_RH_dbn_H0_eq_xi_2026-09-22.md (section 5, new work N1, N2, N5).

  Riemann's symmetric integral for Mathlib's ENTIRE completed zeta function:

    completedRiemannZeta₀ s = ∫_1^∞ ψ(x) (x^{s/2 - 1} + x^{(1-s)/2 - 1}) dx     for EVERY s ∈ ℂ,

  where ψ(x) = ∑_{n ≥ 1} exp(-π n² x) (`DBN.psi`).  No strip restriction: `Λ₀` is the Mellin
  transform of the modified theta kernel `f_modif`, which decays at both ends.

  What IS proved here (axiom-clean, see AxiomGuardDBN.lean):
    * N5: `θ(x) = 1 + 2 ψ(x)` for the `ℤ`-indexed theta sum, in both the Mathlib vocabulary
      (`evenKernel 0 x = 1 + 2 ψ(x)`) and the island's (`thetaMoment 0 u = 1 + 2 ψ(e^{4u})`),
      plus the bridge `evenKernel 0 (e^{4u}) = thetaMoment 0 u`;
    * N1 + N2 for an ARBITRARY weak FE-pair `P`: `P.Λ₀ w` is the sum of two `Ioi 1` integrals,
      the second one obtained from the `Ioo 0 1` piece of `f_modif` by the inversion `x ↦ 1/x`
      (done at the level of Mellin transforms: `mellin_comp_inv`, `mellin_cpow_smul`), together
      with the integrability of both `Ioi 1` integrands for every `w`;
    * the specialisation to `hurwitzEvenFEPair 0`, i.e. the displayed formula above.

  ROUTE (the memo flagged step (iv) as the shape risk).  The memo's primary route is kept for
  steps (i)-(iii): Mellin convergence of `f_modif` at every `w` from
  `(isStrongFEPair_toStrongFEPair P).hasMellin` (Mathlib's `mellinConvergent` is private), then
  `f_modif = A + B` split with `hasMellin_add`.  Step (iv) is NOT done by pushing the `Ioo 0 1`
  indicator through `integral_comp_rpow_Ioi` (p = -1) by hand.  Instead the pointwise identity
  `B x = ε x^{-k} A_g(1/x)` on `Ioi 0` (a three-case trichotomy using `P.h_feq`, where
  `A_g = (Ioi 1).indicator (g - g₀)`) turns the inversion into Mathlib's Mellin-level lemmas
  `mellin_const_smul`, `mellin_cpow_smul`, `mellin_comp_inv` (the last one is
  `integral_comp_rpow_Ioi` at p = -1, packaged).  No indicator is ever transported through a
  substitution, so the memo's fallback (substitute `x = e^v` on all of `Ioi 0`) was not needed.

  SCOPE.  This is a classical identity (Riemann 1859; Titchmarsh, The Theory of the Riemann
  Zeta-Function, 2nd ed., section 2.6; the memo cites section 10.1 for H_0) and one input to the
  representation theorem H_0 = ξ/8 (registry node RH.dbn_H0_eq_xi), which is NOT proved here and
  is itself not RH-equivalent.  Nothing here says anything about zeros of ζ, ξ or H_t.
  Nothing here proves RH.  conjecture1_proved = False.
-/
import DBNDefs

open Real MeasureTheory Set Filter Topology HurwitzZeta

namespace DBN

/-! ### `ψ(x) = ∑_{n ≥ 1} exp(-π n² x)` and the theta kernel (N5) -/

/-- Riemann's `ψ(x) = ∑_{n ≥ 1} exp(-π n² x)` (the positive half of the Jacobi theta sum). -/
noncomputable def psi (x : ℝ) : ℝ :=
  ∑' n : ℕ+, Real.exp (-Real.pi * (n : ℝ) ^ 2 * x)

lemma summable_psi_term {x : ℝ} (hx : 0 < x) :
    Summable (fun n : ℕ+ ↦ Real.exp (-π * (n : ℝ) ^ 2 * x)) := by
  simpa using summable_thetaTerm_pnat 0 hx

/-- N5, series form: the `ℤ`-indexed theta sum is `1 + 2 ψ(x)` (the `n = 0` term is `1`). -/
lemma tsum_int_exp_eq_one_add_two_mul_psi {x : ℝ} (hx : 0 < x) :
    ∑' n : ℤ, Real.exp (-π * (n : ℝ) ^ 2 * x) = 1 + 2 * psi x := by
  rw [tsum_int_eq_zero_add_two_mul_tsum_pnat
    (f := fun n : ℤ ↦ Real.exp (-π * (n : ℝ) ^ 2 * x)) (fun n ↦ by simp)
    (by simpa using summable_thetaTerm 0 hx)]
  simp [psi]

/-- N5 in the island's variable: `thetaMoment 0 u = 1 + 2 ψ(e^{4u})` (the `k = 0` sibling of
`thetaMoment_eq_two_mul_pnat`). -/
lemma thetaMoment_zero_eq_one_add_two_mul_psi (u : ℝ) :
    thetaMoment 0 u = 1 + 2 * psi (Real.exp (4 * u)) := by
  unfold thetaMoment
  simpa using tsum_int_exp_eq_one_add_two_mul_psi (Real.exp_pos (4 * u))

/-- N5 with the `ℕ+` series written out: the `k = 0` sibling of `thetaMoment_eq_two_mul_pnat`
(for `k = 0` the `n = 0` term is `1`, not `0`). -/
lemma thetaMoment_zero_eq_one_add_two_mul_pnat (u : ℝ) :
    thetaMoment 0 u
      = 1 + 2 * ∑' n : ℕ+, ((n : ℝ) ^ 2) ^ 0 * Real.exp (-π * (n : ℝ) ^ 2 * Real.exp (4 * u)) := by
  rw [thetaMoment_zero_eq_one_add_two_mul_psi]
  simp [psi]

/-- `ψ(e^{4u}) = (θ₀(u) - 1)/2` in the island's vocabulary. -/
lemma psi_exp_eq_thetaMoment (u : ℝ) : psi (Real.exp (4 * u)) = (thetaMoment 0 u - 1) / 2 := by
  rw [thetaMoment_zero_eq_one_add_two_mul_psi]
  ring

lemma psi_nonneg (x : ℝ) : 0 ≤ psi x :=
  tsum_nonneg fun _ ↦ (Real.exp_pos _).le

/-- Mathlib's even Hurwitz kernel at `a = 0` is the `ℤ`-indexed theta sum (for `x > 0`). -/
lemma evenKernel_zero_eq_tsum {x : ℝ} (hx : 0 < x) :
    evenKernel 0 x = ∑' n : ℤ, Real.exp (-π * (n : ℝ) ^ 2 * x) := by
  have h := (hasSum_int_evenKernel 0 hx).tsum_eq
  simp only [QuotientAddGroup.mk_zero, add_zero] at h
  exact h.symm

/-- `evenKernel 0 x = 1 + 2 ψ(x)` for `x > 0`. -/
lemma evenKernel_zero_eq_one_add_two_mul_psi {x : ℝ} (hx : 0 < x) :
    evenKernel 0 x = 1 + 2 * psi x := by
  rw [evenKernel_zero_eq_tsum hx, tsum_int_exp_eq_one_add_two_mul_psi hx]

/-- **Vocabulary bridge**: Mathlib's `evenKernel 0` at `x = e^{4u}` is the island's zeroth theta
moment `thetaMoment 0 u`. -/
theorem evenKernel_zero_eq_thetaMoment (u : ℝ) :
    evenKernel 0 (Real.exp (4 * u)) = thetaMoment 0 u := by
  rw [evenKernel_zero_eq_one_add_two_mul_psi (Real.exp_pos _),
    thetaMoment_zero_eq_one_add_two_mul_psi]

/-- `ψ(x) = (θ(x) - 1)/2` in Mathlib's vocabulary. -/
lemma psi_eq_evenKernel {x : ℝ} (hx : 0 < x) : psi x = (evenKernel 0 x - 1) / 2 := by
  rw [evenKernel_zero_eq_one_add_two_mul_psi hx]
  ring

lemma continuousOn_psi : ContinuousOn psi (Ioi 0) := by
  have h : ContinuousOn (fun x ↦ (evenKernel 0 x - 1) / 2) (Ioi 0) :=
    ((continuousOn_evenKernel 0).sub continuousOn_const).div_const 2
  exact h.congr fun x hx ↦ psi_eq_evenKernel hx

/-! ### Riemann's two-`Ioi 1`-integral formula for an arbitrary weak FE-pair (N1, N2) -/

section FEPair

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The modified kernel `f_modif` of any weak FE-pair is Mellin-convergent at EVERY `w`
(Mathlib's `IsStrongFEPair.mellinConvergent` is private; we go through `hasMellin`). -/
lemma weakFEPair_mellinConvergent_f_modif (P : WeakFEPair E) (w : ℂ) :
    MellinConvergent P.f_modif w :=
  (P.isStrongFEPair_toStrongFEPair.hasMellin w).1

/-- On `Ioi 1` the modified kernel is `f - f₀`. -/
lemma weakFEPair_f_modif_of_one_lt (P : WeakFEPair E) {x : ℝ} (hx : 1 < x) :
    P.f_modif x = P.f x - P.f₀ := by
  simp [WeakFEPair.f_modif, indicator_of_mem (mem_Ioi.mpr hx),
    indicator_of_notMem (notMem_Ioo_of_ge hx.le)]

/-- The `Ioi 1` integrand `x^{w-1} (f(x) - f₀)` is integrable for EVERY `w ∈ ℂ`. -/
theorem weakFEPair_integrableOn_Ioi_one (P : WeakFEPair E) (w : ℂ) :
    IntegrableOn (fun x : ℝ ↦ (x : ℂ) ^ (w - 1) • (P.f x - P.f₀)) (Ioi 1) := by
  have hconv : IntegrableOn (fun x : ℝ ↦ (x : ℂ) ^ (w - 1) • P.f_modif x) (Ioi 0) :=
    weakFEPair_mellinConvergent_f_modif P w
  refine (hconv.mono_set (Ioi_subset_Ioi zero_le_one)).congr_fun (fun x hx ↦ ?_)
    measurableSet_Ioi
  simp only [weakFEPair_f_modif_of_one_lt P hx]

/-- Mellin transform of a function supported on `Ioi 1`, as an `Ioi 1` integral (no
integrability needed). -/
lemma mellin_indicator_Ioi_one (F : ℝ → E) (v : ℂ) :
    mellin ((Ioi 1).indicator F) v = ∫ x in Ioi (1 : ℝ), (x : ℂ) ^ (v - 1) • F x := by
  have h : ∀ x : ℝ, (x : ℂ) ^ (v - 1) • (Ioi 1).indicator F x
      = (Ioi 1).indicator (fun x : ℝ ↦ (x : ℂ) ^ (v - 1) • F x) x :=
    fun x ↦ (indicator_smul_apply (Ioi 1) (fun x : ℝ ↦ (x : ℂ) ^ (v - 1)) F x).symm
  simp only [mellin, h]
  rw [setIntegral_indicator measurableSet_Ioi, inter_eq_right.mpr (Ioi_subset_Ioi zero_le_one)]

/-- **N1 + N2 for an arbitrary weak FE-pair.**  For every `w ∈ ℂ`,
`P.Λ₀ w = ∫_1^∞ x^{w-1} (f(x) - f₀) dx + ε ∫_1^∞ x^{k-w-1} (g(x) - g₀) dx`.
The second integral is the `Ioo 0 1` piece of `f_modif` after the inversion `x ↦ 1/x`, performed
on the Mellin transform (`mellin_comp_inv`) using the functional equation `P.h_feq`. -/
theorem weakFEPair_Λ₀_eq (P : WeakFEPair E) (w : ℂ) :
    P.Λ₀ w = (∫ x in Ioi (1 : ℝ), (x : ℂ) ^ (w - 1) • (P.f x - P.f₀))
      + P.ε • ∫ x in Ioi (1 : ℝ), (x : ℂ) ^ ((P.k : ℂ) - w - 1) • (P.g x - P.g₀) := by
  set A : ℝ → E := (Ioi 1).indicator (fun x ↦ P.f x - P.f₀) with hA
  set B : ℝ → E := (Ioo 0 1).indicator (fun x ↦ P.f x - (P.ε * ↑(x ^ (-P.k))) • P.g₀) with hB
  set Ag : ℝ → E := (Ioi 1).indicator (fun x ↦ P.g x - P.g₀) with hAg
  have hfm : P.f_modif = A + B := rfl
  have hconv := weakFEPair_mellinConvergent_f_modif P w
  -- the `Ioi 1` piece converges
  have hAconv : MellinConvergent A w := by
    have h1 : IntegrableOn ((Ioi (1 : ℝ)).indicator (fun x : ℝ ↦ (x : ℂ) ^ (w - 1) • P.f_modif x))
        (Ioi 0) := IntegrableOn.indicator hconv measurableSet_Ioi
    refine h1.congr_fun (fun x _ ↦ ?_) measurableSet_Ioi
    by_cases hx : x ∈ Ioi (1 : ℝ)
    · rw [indicator_of_mem hx, weakFEPair_f_modif_of_one_lt P hx, hA, indicator_of_mem hx]
    · rw [indicator_of_notMem hx, hA, indicator_of_notMem hx, smul_zero]
  -- hence so does the `Ioo 0 1` piece
  have hBconv : MellinConvergent B w := by
    have h1 : IntegrableOn (fun x : ℝ ↦ (x : ℂ) ^ (w - 1) • P.f_modif x
        - (x : ℂ) ^ (w - 1) • A x) (Ioi 0) := IntegrableOn.sub hconv hAconv
    refine h1.congr_fun (fun x _ ↦ ?_) measurableSet_Ioi
    simp only [hfm, Pi.add_apply, smul_add, add_sub_cancel_left]
  -- split the Mellin integral
  have hsplit : P.Λ₀ w = mellin A w + mellin B w := by
    show mellin P.f_modif w = _
    rw [hfm]
    exact (hasMellin_add hAconv hBconv).2
  -- the `Ioo 0 1` piece is the inverted `g`-piece
  have hBeq : ∀ x ∈ Ioi (0 : ℝ), B x = P.ε • ((x : ℂ) ^ (-(P.k : ℂ)) • Ag x⁻¹) := by
    intro x hx
    have hx0 : 0 < x := hx
    have hxk : ((x ^ (-P.k) : ℝ) : ℂ) = (x : ℂ) ^ (-(P.k : ℂ)) := by
      rw [Complex.ofReal_cpow hx0.le, Complex.ofReal_neg]
    rcases lt_trichotomy x 1 with hx1 | rfl | hx1
    · have hxi : 1 < x⁻¹ := (one_lt_inv₀ hx0).mpr hx1
      rw [hB, indicator_of_mem (mem_Ioo.mpr ⟨hx0, hx1⟩), hAg, indicator_of_mem (mem_Ioi.mpr hxi)]
      have hfe := P.h_feq x⁻¹ (inv_pos.mpr hx0)
      rw [one_div, inv_inv, Real.inv_rpow hx0.le, ← Real.rpow_neg hx0.le, hxk] at hfe
      rw [hfe, hxk, smul_sub, smul_sub, mul_smul, mul_smul]
    · simp [hB, hAg]
    · have hxi : x⁻¹ < 1 := inv_lt_one_of_one_lt₀ hx1
      rw [hB, indicator_of_notMem (notMem_Ioo_of_ge hx1.le), hAg,
        indicator_of_notMem (notMem_Ioi.mpr hxi.le), smul_zero, smul_zero]
  have hBmellin : mellin B w = P.ε • mellin Ag ((P.k : ℂ) - w) := by
    have h1 : mellin B w = mellin (fun x : ℝ ↦ P.ε • ((x : ℂ) ^ (-(P.k : ℂ)) • Ag x⁻¹)) w :=
      setIntegral_congr_fun measurableSet_Ioi (fun x hx ↦ by simp only [hBeq x hx])
    rw [h1, mellin_const_smul, mellin_cpow_smul (fun x : ℝ ↦ Ag x⁻¹) w (-(P.k : ℂ)),
      mellin_comp_inv]
    congr 2
    ring
  rw [hsplit, hBmellin, hA, hAg, mellin_indicator_Ioi_one, mellin_indicator_Ioi_one]

end FEPair

/-! ### Specialisation to the Riemann zeta function (`hurwitzEvenFEPair 0`) -/

/-- Pointwise, for `x > 0`: `x^{v-1} (θ(x) - 1) = 2 ψ(x) x^{v-1}`, where `θ = evenKernel 0` is
the kernel `f` of `hurwitzEvenFEPair 0` and `1` is its constant term `f₀`. -/
lemma hurwitzEvenFEPair_zero_integrand (v : ℂ) {x : ℝ} (hx : 0 < x) :
    (x : ℂ) ^ (v - 1) • ((hurwitzEvenFEPair 0).f x - (hurwitzEvenFEPair 0).f₀)
      = 2 * ((psi x : ℂ) * (x : ℂ) ^ (v - 1)) := by
  have hf : (hurwitzEvenFEPair 0).f x = (evenKernel 0 x : ℂ) := rfl
  have hf₀ : (hurwitzEvenFEPair 0).f₀ = 1 := by simp [hurwitzEvenFEPair]
  rw [hf, hf₀, evenKernel_zero_eq_one_add_two_mul_psi hx, smul_eq_mul]
  push_cast
  ring

/-- The integrand `ψ(x) x^{v-1}` is integrable on `(1, ∞)` for EVERY `v ∈ ℂ`. -/
theorem integrableOn_psi_mul_cpow (v : ℂ) :
    IntegrableOn (fun x : ℝ ↦ (psi x : ℂ) * (x : ℂ) ^ (v - 1)) (Ioi 1) := by
  have h : IntegrableOn (fun x : ℝ ↦ (1 / 2 : ℂ) * ((x : ℂ) ^ (v - 1) •
      ((hurwitzEvenFEPair 0).f x - (hurwitzEvenFEPair 0).f₀))) (Ioi 1) :=
    (weakFEPair_integrableOn_Ioi_one (hurwitzEvenFEPair 0) v).const_mul (1 / 2 : ℂ)
  refine IntegrableOn.congr_fun h (fun x hx ↦ ?_) measurableSet_Ioi
  rw [hurwitzEvenFEPair_zero_integrand v (zero_lt_one.trans hx)]
  ring

/-- `∫_1^∞ x^{v-1} (θ(x) - 1) dx = 2 ∫_1^∞ ψ(x) x^{v-1} dx` (no integrability needed). -/
lemma integral_hurwitzEvenFEPair_zero (v : ℂ) :
    ∫ x in Ioi (1 : ℝ), (x : ℂ) ^ (v - 1) • ((hurwitzEvenFEPair 0).f x - (hurwitzEvenFEPair 0).f₀)
      = 2 * ∫ x in Ioi (1 : ℝ), (psi x : ℂ) * (x : ℂ) ^ (v - 1) := by
  rw [← integral_const_mul]
  exact setIntegral_congr_fun measurableSet_Ioi fun x hx ↦
    hurwitzEvenFEPair_zero_integrand v (zero_lt_one.trans hx)

/-- **Riemann's symmetric integral for `Λ₀`, valid for EVERY `s ∈ ℂ`** (design memo row A, N1):
`completedRiemannZeta₀ s = ∫_1^∞ ψ(x) (x^{s/2 - 1} + x^{(1-s)/2 - 1}) dx`.
A classical identity (Riemann 1859); nothing here concerns the zeros of `ζ`.
conjecture1_proved = False. -/
theorem completedRiemannZeta₀_eq_integral_psi (s : ℂ) :
    completedRiemannZeta₀ s = ∫ x in Ioi (1 : ℝ),
      (psi x : ℂ) * ((x : ℂ) ^ (s / 2 - 1) + (x : ℂ) ^ ((1 - s) / 2 - 1)) := by
  have hsymm : (hurwitzEvenFEPair 0).symm = hurwitzEvenFEPair 0 := hurwitzEvenFEPair_zero_symm
  have hg : (hurwitzEvenFEPair 0).g = (hurwitzEvenFEPair 0).f := congrArg WeakFEPair.f hsymm
  have hg₀ : (hurwitzEvenFEPair 0).g₀ = (hurwitzEvenFEPair 0).f₀ := congrArg WeakFEPair.f₀ hsymm
  have hε : (hurwitzEvenFEPair 0).ε = 1 := rfl
  have hk : ((hurwitzEvenFEPair 0).k : ℂ) - s / 2 - 1 = (1 - s) / 2 - 1 := by
    show ((1 / 2 : ℝ) : ℂ) - s / 2 - 1 = (1 - s) / 2 - 1
    push_cast
    ring
  have hmain := weakFEPair_Λ₀_eq (hurwitzEvenFEPair 0) (s / 2)
  rw [hg, hg₀, hε, one_smul, hk, integral_hurwitzEvenFEPair_zero (s / 2),
    integral_hurwitzEvenFEPair_zero ((1 - s) / 2)] at hmain
  show (hurwitzEvenFEPair 0).Λ₀ (s / 2) / 2 = _
  rw [hmain, ← mul_add, mul_div_cancel_left₀ _ two_ne_zero,
    ← integral_add (integrableOn_psi_mul_cpow (s / 2)) (integrableOn_psi_mul_cpow ((1 - s) / 2))]
  simp only [mul_add]

end DBN
