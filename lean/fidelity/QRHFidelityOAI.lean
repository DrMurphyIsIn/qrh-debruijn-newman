/- Fidelity root, bridge side (Lean v4.34.1, Mathlib d13f23b, inside openai/math adc7f124).
   `QRHFidelity.stmt` is the elaborated statement of `qrh_seven_eighths`; `QRHFidelity.stmtMathlib`
   is the same text elaborated afresh.  conjecture1_proved = False. -/
import ArdaQRHBridge
open Lean Meta in
run_meta do
  let ci ← getConstInfo ``qrh_seven_eighths
  let d : DefinitionVal :=
    { name := `QRHFidelity.stmt, levelParams := [], type := Expr.sort 0,
      value := ci.type, hints := ReducibilityHints.abbrev, safety := DefinitionSafety.safe }
  addDecl (Declaration.defnDecl d)
def QRHFidelity.stmtMathlib : Prop := ∀ s : ℂ, (7 / 8 : ℝ) < s.re → riemannZeta s ≠ 0
