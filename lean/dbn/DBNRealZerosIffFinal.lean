/-
  DBNRealZerosIffFinal -- Route C / C4, the UNCONDITIONAL bridge on the de Bruijn-Newman island
  (registry node RH.dbn_rh_iff_H0_real_zeros, statement verbatim).

    RH (in the registry's AND-ladder strip grammar)  <->  every zero of H_0 is real.

  DBNRealZerosIff proves this CONDITIONALLY on the C2 representation theorem
  H_0(z) = (1/8) ξ(1/2 + iz/2) (`dbn_rh_iff_H0_real_zeros_of_H0_eq_xi`, hypothesis `hC2`).  C2 is
  now the island theorem `dbn_H0_eq_xi` (DBNXi.lean, modules A-E of
  DESIGN_RH_dbn_H0_eq_xi_2026-09-22.md), so the registry statement is the one-line
  specialisation below, and the named obligation `DBN.H0EqXi` is discharged as `DBN.H0EqXi_holds`.

  What IS proved here (axiom-clean, see AxiomGuardDBN.lean): `DBN.H0EqXi_holds` and
  `dbn_rh_iff_H0_real_zeros` (unconditional; no hypothesis, no new axiom).

  SCOPE.  The equivalence is a BRIDGE between two grammars of the SAME open conjecture: it proves
  NOTHING about RH in either direction.  Neither side is established here: RH is open, and "every
  zero of H_0 is real" is RH restated.  Nothing here bounds the de Bruijn-Newman constant or
  proves de Bruijn's t ≥ 1/2 theorem (registry node RH.dbn_debruijn_real_zeros).  Nothing here
  proves RH.  conjecture1_proved = False.
-/
import DBNXi
import DBNRealZerosIff

/-- The named C2 obligation of DBNRealZerosIff (`DBN.H0EqXi`), discharged by `dbn_H0_eq_xi`. -/
theorem DBN.H0EqXi_holds : DBN.H0EqXi := dbn_H0_eq_xi

/-- **Route C / C4, unconditional** (registry node RH.dbn_rh_iff_H0_real_zeros, statement
verbatim): strip-RH holds iff every zero of `H_0` is real.  The one-line specialisation of
`dbn_rh_iff_H0_real_zeros_of_H0_eq_xi` at the C2 theorem `dbn_H0_eq_xi`.  An equivalence between
two restatements of the same OPEN conjecture: it proves neither side.  Nothing here proves RH.
conjecture1_proved = False. -/
theorem dbn_rh_iff_H0_real_zeros :
    (∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re = 1 / 2)
      ↔ ∀ z : ℂ, DBN.H 0 z = 0 → z.im = 0 :=
  dbn_rh_iff_H0_real_zeros_of_H0_eq_xi dbn_H0_eq_xi
