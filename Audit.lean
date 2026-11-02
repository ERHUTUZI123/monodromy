module

import Monodromy
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-! Run `lake env lean Audit.lean` to check the axioms of every exported
Monodromy declaration, including its transitive proof dependencies. -/

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Quot.sound, `Classical.choice]
  let mut checked : Nat := 0
  for (name, _) in (← getEnv).constants.toList do
    if (`Monodromy).isPrefixOf name then
      checked := checked + 1
      for dependency in ← collectAxioms name do
        unless allowed.contains dependency do
          throwError "{name} depends on unexpected axiom {dependency}"
  logInfo m!"Audited {checked} Monodromy declarations: only standard Lean axioms."
