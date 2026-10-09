/-
  DBNRealZerosIff -- Route C / C4 bridge on the de Bruijn-Newman island
  (telperion/docs/RH_ROUTES_ROADMAP_2026-09-16.md section 4, registry node
  RH.dbn_rh_iff_H0_real_zeros).

  The classical equivalence (de Bruijn 1950; Polymath15 arXiv:1904.12438 eq. (3); Titchmarsh 10.1)

    RH  <->  every zero of H_0 is real,

  with RH written in the registry's AND-ladder strip grammar
  (forall rho, zeta rho = 0 -> 0 < Re rho -> Re rho < 1 -> Re rho = 1/2), is proved here
  CONDITIONALLY on the C2 representation theorem

    H_0(z) = (1/8) xi(1/2 + i z/2)        (registry node RH.dbn_H0_eq_xi),

  which is NOT proved in THIS module.  (It is proved on the island as `dbn_H0_eq_xi` in DBNXi.lean,
  modules A-E of DESIGN_RH_dbn_H0_eq_xi_2026-09-22.md; this module does not import it.)  C2 enters
  every conditional statement below as an explicit hypothesis `hC2`, and is also packaged once as
  the named Prop obligation `DBN.H0EqXi` so the input has one canonical name.

  What IS proved here, axiom-clean (AxiomGuardDBN.lean):
    * the C4 change of variables z |-> 1/2 + i z/2: its real part, the fact that it carries
      the real axis EXACTLY onto the critical line, its explicit inverse s |-> -2 i (s - 1/2),
      and the imaginary part of that inverse (xiArg_re, xiArg_re_eq_half_iff, xiArg_surj,
      xiArgInv_im -- re-derived here; a sibling branch has the same four lemmas unmerged),
    * xi(s) = 0 <-> (zeta s = 0 and 0 < Re s < 1), unpacked from the pinned upstream
      LiCriterion.xi_zeros_are_nontrivial_zeros (discharged upstream via Lc/XiZeros, no axiom),
    * GIVEN C2: H_0 z = 0 <-> xi(1/2 + i z/2) = 0 (the factor 1/8 is a nonzero constant),
    * GIVEN C2: dbn_rh_iff_H0_real_zeros_of_H0_eq_xi, whose conclusion is the registry
      statement of RH.dbn_rh_iff_H0_real_zeros verbatim.

  The registry theorem `dbn_rh_iff_H0_real_zeros` itself is deliberately NOT stated in this
  module: its registry statement is unconditional.  It is stated in DBNRealZerosIffFinal.lean as
  the one-line specialisation `dbn_rh_iff_H0_real_zeros_of_H0_eq_xi dbn_H0_eq_xi`.

  SCOPE.  The equivalence is a BRIDGE between two grammars of the same open conjecture: proving
  it proves NOTHING about RH in either direction, bounds nothing about the de Bruijn-Newman
  constant, and does not prove C2.  Nothing here proves RH.  conjecture1_proved = False.
-/
import DBNDefs

namespace DBN

/-- The C2 representation theorem `H_0(z) = (1/8) xi(1/2 + i z/2)` (registry node
`RH.dbn_H0_eq_xi`) as a named Prop obligation: the single input that every conditional theorem
below consumes.  Not proved in this module; it is discharged as `DBN.H0EqXi_holds` in
DBNRealZerosIffFinal.lean (from `dbn_H0_eq_xi`, DBNXi.lean).  conjecture1_proved = False. -/
def H0EqXi : Prop :=
  ∀ z : ℂ, DBN.H 0 z = (1 / 8 : ℂ) * LiCriterion.riemannXi (1 / 2 + Complex.I * z / 2)

/-! ### The C4 change of variables `z ↦ 1/2 + i z/2` (unconditional) -/

/-- Real part of the C4 reindexing `z ↦ 1/2 + i z/2`. -/
theorem xiArg_re (z : ℂ) : (1 / 2 + Complex.I * z / 2).re = 1 / 2 - z.im / 2 := by
  simp only [Complex.add_re, Complex.div_ofNat_re, Complex.I_mul_re, Complex.one_re]
  ring

/-- The C4 reindexing carries the real axis exactly onto the critical line. -/
theorem xiArg_re_eq_half_iff (z : ℂ) :
    (1 / 2 + Complex.I * z / 2).re = 1 / 2 ↔ z.im = 0 := by
  rw [xiArg_re]
  constructor <;> intro h <;> linarith

/-- The C4 reindexing is surjective, with explicit inverse `s ↦ -2 i (s - 1/2)`. -/
theorem xiArg_surj (s : ℂ) :
    1 / 2 + Complex.I * (-2 * Complex.I * (s - 1 / 2)) / 2 = s := by
  linear_combination (1 / 2 - s) * Complex.I_mul_I

/-- The inverse reindexing carries the critical line onto the real axis. -/
theorem xiArgInv_im (s : ℂ) : (-2 * Complex.I * (s - 1 / 2)).im = -2 * (s.re - 1 / 2) := by
  simp only [Complex.mul_im, Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.neg_re,
    Complex.neg_im, Complex.I_re, Complex.I_im, Complex.re_ofNat, Complex.im_ofNat,
    Complex.div_ofNat_re, Complex.div_ofNat_im, Complex.one_re, Complex.one_im]
  ring

/-! ### Zeros of xi are exactly the strip zeros of zeta (upstream, unpacked) -/

/-- `LiCriterion.xi_zeros_are_nontrivial_zeros` with the subtype `NontrivialZero` unpacked into
the AND-ladder strip grammar used by the registry statement. -/
theorem riemannXi_eq_zero_iff_strip_zero (s : ℂ) :
    LiCriterion.riemannXi s = 0 ↔ riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 := by
  rw [LiCriterion.xi_zeros_are_nontrivial_zeros s]
  constructor
  · rintro ⟨ρ, rfl⟩
    exact ρ.property
  · intro h
    exact ⟨⟨s, h⟩, rfl⟩

/-! ### The conditional bridge -/

/-- GIVEN C2: `H_0 z = 0 ↔ xi(1/2 + i z/2) = 0`, because `1/8 ≠ 0`. -/
theorem H_zero_eq_zero_iff_of_H0_eq_xi
    (hC2 : ∀ z : ℂ, DBN.H 0 z = (1 / 8 : ℂ) * LiCriterion.riemannXi (1 / 2 + Complex.I * z / 2))
    (z : ℂ) :
    DBN.H 0 z = 0 ↔ LiCriterion.riemannXi (1 / 2 + Complex.I * z / 2) = 0 := by
  rw [hC2 z]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h8 | hxi
    · norm_num at h8
    · exact hxi
  · intro h
    rw [h, mul_zero]

end DBN

/-- Route C / C4, CONDITIONAL on C2.  The conclusion is the registry statement of
`RH.dbn_rh_iff_H0_real_zeros` verbatim; the hypothesis `hC2` is the registry statement of
`RH.dbn_H0_eq_xi` (`dbn_H0_eq_xi`), so the unconditional registry theorem is the one-line
specialisation `dbn_rh_iff_H0_real_zeros_of_H0_eq_xi dbn_H0_eq_xi` (DBNRealZerosIffFinal.lean).

Forward: a zero `z` of `H_0` gives `xi(1/2 + i z/2) = 0`, hence a strip zero `ρ = 1/2 + i z/2`
of `ζ`; strip-RH puts `Re ρ = 1/2`, i.e. `Im z = 0`.  Backward: a strip zero `ρ` of `ζ` is a
zero of `xi`, so `z := -2 i (ρ - 1/2)` is a zero of `H_0` (as `1/2 + i z/2 = ρ`), hence real,
i.e. `Re ρ = 1/2`.  Nothing here proves RH.  conjecture1_proved = False. -/
theorem dbn_rh_iff_H0_real_zeros_of_H0_eq_xi
    (hC2 : ∀ z : ℂ, DBN.H 0 z = (1 / 8 : ℂ) * LiCriterion.riemannXi (1 / 2 + Complex.I * z / 2)) :
    (∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re = 1 / 2)
      ↔ ∀ z : ℂ, DBN.H 0 z = 0 → z.im = 0 := by
  constructor
  · -- forward: strip-RH implies every zero of H_0 is real
    intro hRH z hz
    have hxi := (DBN.H_zero_eq_zero_iff_of_H0_eq_xi hC2 z).mp hz
    obtain ⟨hζ, hpos, hlt⟩ := (DBN.riemannXi_eq_zero_iff_strip_zero _).mp hxi
    exact (DBN.xiArg_re_eq_half_iff z).mp (hRH _ hζ hpos hlt)
  · -- backward: every zero of H_0 real implies every strip zero of zeta is on the line
    intro hreal ρ hζ hpos hlt
    have hxi : LiCriterion.riemannXi ρ = 0 :=
      (DBN.riemannXi_eq_zero_iff_strip_zero ρ).mpr ⟨hζ, hpos, hlt⟩
    have hzH : DBN.H 0 (-2 * Complex.I * (ρ - 1 / 2)) = 0 := by
      rw [DBN.H_zero_eq_zero_iff_of_H0_eq_xi hC2, DBN.xiArg_surj]
      exact hxi
    have him := hreal _ hzH
    rw [DBN.xiArgInv_im] at him
    linarith

/-- The same conditional bridge with C2 consumed as the named obligation `DBN.H0EqXi`. -/
theorem dbn_rh_iff_H0_real_zeros_of_obligation (hC2 : DBN.H0EqXi) :
    (∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re = 1 / 2)
      ↔ ∀ z : ℂ, DBN.H 0 z = 0 → z.im = 0 :=
  dbn_rh_iff_H0_real_zeros_of_H0_eq_xi hC2
