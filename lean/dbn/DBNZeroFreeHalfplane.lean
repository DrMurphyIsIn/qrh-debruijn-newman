/-
  DBNZeroFreeHalfplane -- Route C: a zero-free half-plane for zeta bounds the de Bruijn-Newman
  real-zero time.  CONDITIONAL corollary of the parametric de Bruijn theorem
  (`dbn_debruijn_parametric`, DBNM1Parametric) and the representation theorem
  `dbn_H0_eq_xi` (DBNXi).

    `dbn_real_zeros_of_zeta_halfplane`: for every real `θ`, if `ζ(s) ≠ 0` whenever `θ < Re s`,
        then for every `t ≥ (2θ − 1)²/2 = 2(θ − 1/2)²` every zero of `H_t` is real.
    `dbn_real_zeros_of_qrh`: the instance `θ = 7/8`, threshold `t ≥ 9/32`, with the hypothesis
        stated EXACTLY as OpenAI's quasi-Riemann-hypothesis theorem
        `OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re` (github.com/openai/math, lean/, family
        003, Apache-2.0), closed over its implicit binder:
        `∀ s : ℂ, (7 / 8 : ℝ) < s.re → riemannZeta s ≠ 0`.

  Coordinates.  `H_0(z) = ξ(1/2 + iz/2)/8` (`dbn_H0_eq_xi`), so a zero `z` of `H_0` gives a strip
  zero `s = 1/2 + iz/2` of ζ (`riemannXi_eq_zero_iff_strip_zero`) with `Re s = 1/2 − Im z/2`
  (`xiArg_re`).  The half-plane hypothesis gives `Re s ≤ θ`, i.e. `−Im z ≤ 2θ − 1`; evenness
  `H_neg` gives the other side.  So `(Im z)² ≤ (2θ − 1)²`, and `m1_H_real_zeros_of_im_sq_le`
  (heat-flow contraction + Hurwitz) closes the strip at `t = (2θ − 1)²/2`.

  No side condition on `θ` is needed: for `θ < 1/2` the two one-sided bounds are contradictory,
  so `H_0` has no zeros and the conclusion holds for the stated `t`.  (By Hardy, ζ has zeros on
  `Re s = 1/2`, so the hypothesis is false for `θ < 1/2`; that is not used.)

  SCOPE.  The hypothesis is a zero-free HALF-PLANE, not RH: RH is the case `θ = 1/2` (threshold
  `t ≥ 0`, i.e. `Λ ≤ 0`).  The island does not define the de Bruijn-Newman constant (sInf trap,
  see DBNDefs), so "Λ ≤ 9/32" is stated here sInf-free: every zero of `H_t` is real for every
  `t ≥ 9/32`.  This module does NOT prove the 7/8 half-plane; it carries it as an explicit
  hypothesis.  A discharge lives on a separate island pinned to OpenAI's toolchain
  (telperion/examples/oai_qrh_bridge, theorem `qrh_seven_eighths`); the two islands use different
  Mathlib pins, and the cross-pin identity of `riemannZeta` is documented in
  telperion/docs/QRH_DBN_BRIDGE_2026-10-07.md, not kernel-checked across pins.
  Nothing here proves RH.  conjecture1_proved = False.
-/
import DBNM1Parametric
import DBNRealZerosIffFinal

namespace DBN

/-- One-sided bound: if ζ has no zero with `θ < Re s`, every zero `w` of `H_0` has
`−Im w ≤ 2θ − 1`. -/
theorem H0_neg_im_le_of_zeta_halfplane {θ : ℝ}
    (hfree : ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0) {w : ℂ} (hw : H 0 w = 0) :
    -w.im ≤ 2 * θ - 1 := by
  obtain ⟨hζ, -, -⟩ := (riemannXi_eq_zero_iff_strip_zero _).mp
    ((H_zero_eq_zero_iff_of_H0_eq_xi dbn_H0_eq_xi w).mp hw)
  have h : (1 / 2 + Complex.I * w / 2).re ≤ θ := not_lt.mp fun h ↦ hfree _ h hζ
  rw [xiArg_re] at h
  linarith

/-- A zero-free half-plane `θ < Re s` for ζ puts every zero of `H_0` in
`(Im z)² ≤ (2θ − 1)²`.  Not RH unless `θ = 1/2`. -/
theorem H0_im_sq_le_of_zeta_halfplane {θ : ℝ}
    (hfree : ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0) {z : ℂ} (hz : H 0 z = 0) :
    z.im ^ 2 ≤ (2 * θ - 1) ^ 2 := by
  have h1 := H0_neg_im_le_of_zeta_halfplane hfree hz
  have h2 := H0_neg_im_le_of_zeta_halfplane hfree (w := -z) (by rw [H_neg]; exact hz)
  rw [Complex.neg_im, neg_neg] at h2
  nlinarith

end DBN

/-- **Zero-free half-plane ⇒ real zeros of `H_t`** (de Bruijn 1950 Thm 13 with the strip read off
a zero-free half-plane).  For every real `θ`: if `ζ(s) ≠ 0` whenever `θ < Re s`, then every zero
of `H_t` is real for every `t ≥ 2(θ − 1/2)²`.  Classically `Λ ≤ 2(θ − 1/2)²`; the island does not
define `Λ`.  The hypothesis is the caller's; a zero-free half-plane is NOT RH (RH is `θ = 1/2`).
Nothing here proves RH.  conjecture1_proved = False. -/
theorem dbn_real_zeros_of_zeta_halfplane (θ : ℝ)
    (hfree : ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0) :
    ∀ t : ℝ, 2 * (θ - 1 / 2) ^ 2 ≤ t → ∀ z : ℂ, DBN.H t z = 0 → z.im = 0 := by
  intro t ht z hz
  have h0 : 0 ≤ t := le_trans (by positivity) ht
  exact DBN.m1_H_real_zeros_of_im_sq_le (t0 := 0) (Y := (2 * θ - 1) ^ 2)
    (fun _ hw ↦ DBN.H0_im_sq_le_of_zeta_halfplane hfree hw) h0 (by nlinarith) hz

/-- **`Λ ≤ 9/32` from the quasi-Riemann hypothesis, conditional form.**  If `ζ(s) ≠ 0` for
`Re s > 7/8` (hypothesis stated verbatim as OpenAI's
`OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re`, github.com/openai/math, Apache-2.0, closed over
its implicit binder), then every zero of `H_t` is real for every `t ≥ 9/32`.  The hypothesis is
NOT proved on this island; it is a zero-free half-plane, not RH.  Nothing here proves RH.
conjecture1_proved = False. -/
theorem dbn_real_zeros_of_qrh
    (hqrh : ∀ s : ℂ, (7 / 8 : ℝ) < s.re → riemannZeta s ≠ 0) :
    ∀ t : ℝ, 9 / 32 ≤ t → ∀ z : ℂ, DBN.H t z = 0 → z.im = 0 := by
  intro t ht z hz
  exact dbn_real_zeros_of_zeta_halfplane (7 / 8) hqrh t (by norm_num; linarith) z hz

/-- Every zero of `H_0` has `|Im z| ≤ 3/4`, given the 7/8 half-plane (hypothesis as above). -/
theorem dbn_H0_im_sq_le_of_qrh
    (hqrh : ∀ s : ℂ, (7 / 8 : ℝ) < s.re → riemannZeta s ≠ 0) :
    ∀ z : ℂ, DBN.H 0 z = 0 → z.im ^ 2 ≤ 9 / 16 := by
  intro z hz
  have h := DBN.H0_im_sq_le_of_zeta_halfplane hqrh hz
  norm_num at h
  linarith
