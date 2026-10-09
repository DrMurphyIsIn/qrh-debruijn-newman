/-
  DBNM1Parametric -- lane m1, Route C milestone M1a/M1b (telperion/docs/ROUTE_C_SYNTHESIS_2026-09-23.md
  sections 5.2 rank 1 and 7.2): de Bruijn's heat-flow contraction in PARAMETRIC form
  (de Bruijn, Duke Math. J. 17 (1950), Thm 13; Polymath15 arXiv:1904.12438, Thm 3.2), and the
  up-set property of the real-zero times.

    M1a  `dbn_debruijn_parametric`: for every real `t0` and `Y`, if every zero of `H_{t0}` has
         `(Im z)² ≤ Y`, then for every `t ≥ t0` every zero of `H_t` has
         `(Im z)² ≤ max (Y − 2(t − t0)) 0`.
    M1b  `dbn_real_zeros_upset`: if every zero of `H_{t0}` is real, so is every zero of `H_t` for
         every `t ≥ t0` (the `Y = 0` case).

  RANGE OF `t0`.  All real `t0`, negative included: the reweighted approximants of
  `DBNM1Approx` have order `≤ 3/2` for every real `t0` (`m1_norm_W_le_growth`; the base weight
  `e^{t0 u²}` is absorbed by the double-exponential decay of `Φ`), so no `0 ≤ t0` side condition
  is needed.

  Proof.  Fix `s = t − t0 > 0`, `N ≥ 1`, `δ = √(2s/N)`.  The approximants `F k = m1W t0 δ k`
  satisfy `F 0 = H t0`, `F (k+1) = T_δ (F k)`, are real, and carry even Hadamard data
  (`m1_evenHadamardData_W`); the iterated step lemma `zero_im_sq_le_of_shiftAvg_iterate`
  (DBNStep) puts the zeros of `F N = m1G t0 s N` in `(Im z)² ≤ max (Y − Nδ²) 0 = max (Y − 2s) 0`.
  Hurwitz (`hurwitz_ne_zero_of_entire`) transfers this to the locally uniform limit `H (t0 + s)`
  (`m1_tendstoLocallyUniformly_G`), which is not identically zero (`H_zero_ne_zero`).

  IMPORT CLOSURE.  {DBNDefs, DBNStep, DBNHurwitz, DBNHeatApprox, DBNHadamard*, DBNM1Approx,
  Mathlib, Lc.LiCriterion.Basic}.  No DBNStrip, no DBNXi, no registry theorem: the strip of `H_0`
  is not an input (it only instantiates the hypothesis at `t0 = 0`, `Y = 1`; see
  `DBNM1Controls`).

  SCOPE.  Both theorems are CONDITIONAL on information about `H_{t0}` supplied by the caller;
  neither says anything about where the zeros of `H_0` lie inside the strip, and the de
  Bruijn-Newman constant is not defined on this island.  `Λ ≤ 0` is RH; nothing here proves it.
  conjecture1_proved = False.
-/
import DBNM1Approx

open Set Filter Topology ComplexConjugate

namespace DBN

/-- **Zeros of the reweighted approximants**: if every zero of `H_{t0}` has `(Im z)² ≤ Y`, then
for `s > 0` and `N ≥ 1` every zero of `m1G t0 s N` has `(Im z)² ≤ max (Y − 2s) 0`. -/
theorem m1_G_zero_im_sq_le {t0 Y : ℝ} (h0 : ∀ z : ℂ, H t0 z = 0 → z.im ^ 2 ≤ Y) {s : ℝ}
    (hs : 0 < s) {N : ℕ} (hN : 1 ≤ N) {z : ℂ} (hz : m1G t0 s N z = 0) :
    z.im ^ 2 ≤ max (Y - 2 * s) 0 := by
  set δ : ℝ := Real.sqrt (2 * s / N) with hδ_def
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hδ : 0 < δ := Real.sqrt_pos.mpr (by positivity)
  have hδsq : (N : ℝ) * δ ^ 2 = 2 * s := by
    rw [hδ_def, Real.sq_sqrt (by positivity)]
    field_simp
  have hF0 : ∀ w : ℂ, m1W t0 δ 0 w = 0 → w.im ^ 2 ≤ Y := by
    intro w hw
    rw [m1W_zero] at hw
    exact h0 w hw
  have hiter := zero_im_sq_le_of_shiftAvg_iterate (F := m1W t0 δ) hδ (fun k ↦ m1W_succ t0 δ k)
    (fun k ↦ m1_evenHadamardData_W t0 δ k) (fun k w ↦ m1W_conj t0 δ k w) hF0 N z hz
  rwa [hδsq] at hiter

/-- **Parametric de Bruijn contraction, island form**: if every zero of `H_{t0}` has
`(Im z)² ≤ Y`, then for `s ≥ 0` every zero of `H (t0 + s)` has `(Im z)² ≤ max (Y − 2s) 0`.
Every real `t0` and `Y`. -/
theorem m1_H_zero_im_sq_le {t0 Y : ℝ} (h0 : ∀ z : ℂ, H t0 z = 0 → z.im ^ 2 ≤ Y) {s : ℝ}
    (hs : 0 ≤ s) {z : ℂ} (hz : H (t0 + s) z = 0) : z.im ^ 2 ≤ max (Y - 2 * s) 0 := by
  rcases eq_or_lt_of_le hs with hs0 | hspos
  · -- `s = 0`: the hypothesis itself
    subst hs0
    rw [add_zero] at hz
    rw [mul_zero, sub_zero]
    exact le_max_of_le_left (h0 z hz)
  · -- `s > 0`: step lemma on the approximants, then Hurwitz
    by_contra hlt
    have hlt' : max (Y - 2 * s) 0 < z.im ^ 2 := lt_of_not_ge hlt
    have hU : IsOpen {w : ℂ | max (Y - 2 * s) 0 < w.im ^ 2} :=
      isOpen_lt continuous_const (Complex.continuous_im.pow 2)
    refine hurwitz_ne_zero_of_entire hU (fun N ↦ m1_differentiable_W t0 _ N) ?_
      (differentiable_H (t0 + s)) (m1_tendstoLocallyUniformly_G t0 hs)
      ⟨0, H_zero_ne_zero (t0 + s)⟩ hlt' hz
    filter_upwards [eventually_ge_atTop 1] with N hN w hw hGw
    exact absurd (m1_G_zero_im_sq_le h0 hspos hN hGw) (not_le.mpr hw)

/-- The `t ≥ t0` form of `m1_H_zero_im_sq_le`. -/
theorem m1_H_zero_im_sq_le_of_le {t0 Y : ℝ} (h0 : ∀ z : ℂ, H t0 z = 0 → z.im ^ 2 ≤ Y) {t : ℝ}
    (ht : t0 ≤ t) {z : ℂ} (hz : H t z = 0) : z.im ^ 2 ≤ max (Y - 2 * (t - t0)) 0 :=
  m1_H_zero_im_sq_le h0 (sub_nonneg.mpr ht) (by rwa [add_sub_cancel])

/-- **Up-set property, island form**: real zeros at time `t0` stay real at every `t ≥ t0`. -/
theorem m1_H_real_zeros_of_le {t0 t : ℝ} (ht : t0 ≤ t) (h0 : ∀ z : ℂ, H t0 z = 0 → z.im = 0)
    {z : ℂ} (hz : H t z = 0) : z.im = 0 := by
  have h := m1_H_zero_im_sq_le_of_le (Y := 0) (fun w hw ↦ by rw [h0 w hw]; norm_num) ht hz
  rw [max_eq_right (by linarith)] at h
  exact (pow_eq_zero_iff two_ne_zero).mp (le_antisymm h (sq_nonneg _))

/-- **Real zeros once the strip has closed**: if every zero of `H_{t0}` has `(Im z)² ≤ Y` and
`t0 ≤ t`, `Y ≤ 2 (t − t0)`, then every zero of `H_t` is real. -/
theorem m1_H_real_zeros_of_im_sq_le {t0 Y t : ℝ} (h0 : ∀ z : ℂ, H t0 z = 0 → z.im ^ 2 ≤ Y)
    (ht : t0 ≤ t) (hY : Y ≤ 2 * (t - t0)) {z : ℂ} (hz : H t z = 0) : z.im = 0 := by
  have h := m1_H_zero_im_sq_le_of_le h0 ht hz
  rw [max_eq_right (by linarith)] at h
  exact (pow_eq_zero_iff two_ne_zero).mp (le_antisymm h (sq_nonneg _))

/-- A zero-free upper region `Im z ≥ y0` of `H_{t0}` puts every zero of `H_{t0}` in
`(Im z)² ≤ y0²` (evenness `H_neg` handles `Im z ≤ −y0`). -/
theorem m1_im_sq_le_of_upper_zero_free {t0 y0 : ℝ}
    (hfree : ∀ z : ℂ, y0 ≤ z.im → H t0 z ≠ 0) {z : ℂ} (hz : H t0 z = 0) : z.im ^ 2 ≤ y0 ^ 2 := by
  have h1 : z.im < y0 := lt_of_not_ge fun h ↦ hfree z h hz
  have h2 : -y0 < z.im := by
    refine lt_of_not_ge fun h ↦ hfree (-z) ?_ (by rw [H_neg]; exact hz)
    rw [Complex.neg_im]
    linarith
  nlinarith

/-- **The closing step of Polymath15 Thm 1.2** (their Prop 3.3 conclusion fed into de Bruijn's
Thm 3.2, P15 p.16), sInf-free: if `H_{t0}` has no zero with `Im z ≥ y0`, then for every
`t ≥ t0 + y0²/2` every zero of `H_t` is real.  (Classically: `Λ ≤ t0 + y0²/2`.)  The
hypothesis about `H_{t0}` is the caller's; nothing here supplies it. -/
theorem m1_real_zeros_of_upper_zero_free {t0 y0 : ℝ}
    (hfree : ∀ z : ℂ, y0 ≤ z.im → H t0 z ≠ 0) {t : ℝ} (ht : t0 + y0 ^ 2 / 2 ≤ t) {z : ℂ}
    (hz : H t z = 0) : z.im = 0 :=
  m1_H_real_zeros_of_im_sq_le (fun _ hw ↦ m1_im_sq_le_of_upper_zero_free hfree hw)
    (by nlinarith [sq_nonneg y0]) (by linarith) hz

end DBN

/-- **M1a** (proposed registry node `RH_dbn_debruijn_parametric`, statement as sketched in
ROUTE_C_SYNTHESIS_2026-09-23.md section 7.2): de Bruijn's parametric heat-flow contraction
(de Bruijn 1950 Thm 13; Polymath15 Thm 3.2).  If every zero of `H_{t0}` satisfies
`(Im z)² ≤ Y`, then for every `t ≥ t0` every zero of `H_t` satisfies
`(Im z)² ≤ max (Y − 2(t − t0)) 0`.  Every real `t0` (negative included) and every real `Y`.
Conditional on the caller's information about `H_{t0}`; it says nothing about the zeros of
`H_0` inside the strip.  Nothing here proves RH.  conjecture1_proved = False. -/
theorem dbn_debruijn_parametric :
    ∀ t0 Y : ℝ, (∀ z : ℂ, DBN.H t0 z = 0 → z.im ^ 2 ≤ Y) →
    ∀ t : ℝ, t0 ≤ t → ∀ z : ℂ, DBN.H t z = 0 → z.im ^ 2 ≤ max (Y - 2 * (t - t0)) 0 :=
  fun _ _ h0 _ ht _ hz ↦ DBN.m1_H_zero_im_sq_le_of_le h0 ht hz

/-- **M1b** (proposed registry node `RH_dbn_real_zeros_upset`, statement as sketched in
ROUTE_C_SYNTHESIS_2026-09-23.md section 7.2): the up-set property.  If every zero of `H_{t0}`
is real, then for every `t ≥ t0` every zero of `H_t` is real (the `Y = 0` case of
`dbn_debruijn_parametric`).  So `{t | every zero of H_t is real}` is an up-set; it does NOT
define the de Bruijn-Newman constant and bounds nothing.  Nothing here proves RH.
conjecture1_proved = False. -/
theorem dbn_real_zeros_upset :
    ∀ t0 t : ℝ, t0 ≤ t → (∀ z : ℂ, DBN.H t0 z = 0 → z.im = 0) →
    ∀ z : ℂ, DBN.H t z = 0 → z.im = 0 := by
  intro t0 t ht h0 z hz
  have h := dbn_debruijn_parametric t0 0 (fun w hw ↦ by rw [h0 w hw]; norm_num) t ht z hz
  rw [max_eq_right (by linarith)] at h
  exact (pow_eq_zero_iff two_ne_zero).mp (le_antisymm h (sq_nonneg _))
