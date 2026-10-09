/- Fidelity root, dbn island side (Lean v4.34.0-rc1, Mathlib de5ce8a9).  `QRHFidelity.stmt` is
   the elaborated hypothesis of `dbn_real_zeros_of_qrh`, copied as a definition so lean4export can
   root an export at it.  `QRHFidelity.stmtMathlib` is the same text elaborated afresh.
   conjecture1_proved = False. -/
import DBNZeroFreeHalfplane
open Lean Meta in
run_meta do
  let ci ← getConstInfo ``dbn_real_zeros_of_qrh
  let .forallE _ dom _ _ := ci.type | throwError "unexpected shape"
  let d : DefinitionVal :=
    { name := `QRHFidelity.stmt, levelParams := [], type := Expr.sort 0,
      value := dom, hints := ReducibilityHints.abbrev, safety := DefinitionSafety.safe }
  addDecl (Declaration.defnDecl d)
def QRHFidelity.stmtMathlib : Prop := ∀ s : ℂ, (7 / 8 : ℝ) < s.re → riemannZeta s ≠ 0
