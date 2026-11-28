import RequestProject.Slr.GwbMultilingualOffice
open Lean

/-! Read the kernel environment, not source text or an actor's digest.
The representation is deliberately tied to this Lean toolchain; no claim
of equivalence between differently elaborated statement encodings. -/
run_cmd do
  let env ← getEnv
  let name := `Wikidata.Slr.GwbMultilingualOffice.exactPairAnswer
  match env.find? name with
  | some (.thmInfo info) =>
    let result := Json.mkObj [
      ("schema", toJson ("slr.golden-elaborated-theorem.v1" : String)),
      ("declaration", toJson name.toString),
      ("level_params", toJson (info.levelParams.map Name.toString)),
      ("type_expr_repr", toJson (reprStr info.type))]
    liftIO (IO.println ("GWB_ELABORATED_THEOREM " ++ result.compress))
  | _ => throwError "expected checked theorem not found"
