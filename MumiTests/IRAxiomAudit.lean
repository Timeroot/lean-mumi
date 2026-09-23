import MumiTests.IRUpper
import MumiTests.IRLower
import MumiTests.IRMutual
import MumiTests.IRShapes
import MumiTests.IRImport
import Lean

set_option Elab.async false

open Lean in
run_meta do
  let env ← getEnv
  let some (.axiomInfo info) := env.find? ``IR.mahlo | throwError "missing IR.mahlo"
  let [u] := info.levelParams | throwError "IR.mahlo must have one universe parameter"
  unless info.type == mkConst ``IR.Reflection [.param u, .succ (.param u)] do
    throwError "IR.mahlo must have exactly the successor-universe reflection type"
  let upper := #[`IRUpper, `IRPatternsUpper, `IRMutualUpper, `IRShapesUpper, `IRModuleUpper]
  let lower := #[`IRLower, `IRMutualLower, `IRShapesLower, `IRModuleLower]
  let names := env.constants.fold (init := #[]) fun acc n _ =>
    let userName := privateToUserName n
    if (upper ++ lower).any (·.isPrefixOf userName) then acc.push n else acc
  unless names.size > 200 do throwError "IR audit did not find the generated declarations"
  let mut mahloUsers : Nat := 0
  for n in names do
    let axioms ← collectAxioms n
    let isLower := lower.any (·.isPrefixOf (privateToUserName n))
    let stockInjectivity := n.getString! == "injEq" && env.isConstructor n.getPrefix
    for a in axioms do
      unless (isLower && a == ``IR.mahlo) || (stockInjectivity && a == ``propext) do
        throwError "Unexpected axiom {a} in generated IR declaration {n}"
    if axioms.contains ``IR.mahlo then mahloUsers := mahloUsers + 1
  unless mahloUsers > 0 do throwError "IR audit missed the lower mode"
  logInfo m!"Audited {names.size} IR declarations; {mahloUsers} use the single IR.mahlo axiom. Upper mode is axiom-free apart from stock constructor injEq lemmas."

/-- info: 'IRUpper.U.rec' does not depend on any axioms -/
#guard_msgs in
#print axioms IRUpper.U.rec

/-- info: 'IRLower.U.rec' depends on axioms: [IR.mahlo] -/
#guard_msgs in
#print axioms IRLower.U.rec

/-- info: 'IRMutualLower.Ctx.casesOn' depends on axioms: [IR.mahlo] -/
#guard_msgs in
#print axioms IRMutualLower.Ctx.casesOn
