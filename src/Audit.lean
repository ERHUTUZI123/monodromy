module

import Monodromy
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-! Run `lake env lean src/Audit.lean` to check the axioms of every exported
Monodromy declaration, including its transitive proof dependencies, and the
definition dependencies of the native executor and reversible compiler. -/

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

open Lean Elab Command in
run_cmd do
  let forbidden : Array Name := #[
    `Turing.TM0.step, `Turing.TM1.step, `Turing.TM2.step, `Nat.Partrec.Code.eval,
    `Monodromy.Counter.step, `Monodromy.Counter.Recorded.step,
    `Monodromy.Counter.Reversible.step, `Monodromy.Counter.Reversible.eval,
    `Monodromy.Counter.Reversible.Action.apply, `Monodromy.Counter.Reversible.Action.enabled,
    `Monodromy.ReversibleControl.enabled, `Monodromy.CoupledContinuation.Program.indexInt,
    `Monodromy.CoupledContinuation.Word.evalInt, `Monodromy.CoupledContinuation.Program.nextInt]
  let mut pending := [
    `Monodromy.CoupledContinuation.Program.advance,
    `Monodromy.CoupledContinuation.Program.runDriver,
    `Monodromy.ReversibleCompilation.haltingProgram,
    `Monodromy.ReversibleCompilation.reverseProgram,
    `Monodromy.Counter.Reversible.Recording.table,
    `Monodromy.Counter.Reversible.RadixObservation.table,
    `Monodromy.Counter.Reversible.PrimeCompression.table,
    `Monodromy.ReversibleTuring.table,
    `Monodromy.ReversibleTuring.Compression.table,
    `Monodromy.ReversibleNativeTuring.program,
    `Monodromy.ReversibleNativeTuring.reverseProgram,
    `Monodromy.ReversibleNativeTuring.boundaryProgram,
    `Monodromy.ReversibleNativeTuring.macroStep,
    `Monodromy.ReversibleNativeTuring.reverseMacro]
  let environment ← getEnv
  for name in pending do
    unless (environment.find? name).isSome do
      throwError "Missing native definition audit root {name}"
  let mut visited : NameSet := {}
  while !pending.isEmpty do
    let name := pending.head!
    pending := pending.tail!
    unless visited.contains name do
      visited := visited.insert name
      if forbidden.contains name || (`Monodromy.AnalyticComparison).isPrefixOf name then
        throwError "Native definition depends on proof-side interpreter {name}"
      if let some declaration := environment.find? name then
        if let some body := declaration.value? then
          pending := body.getUsedConstants.toList ++ pending
  for required in #[`Monodromy.CoupledContinuation.lower,
      `Monodromy.CoupledContinuation.feed, `Monodromy.CoupledContinuation.upper,
      `Monodromy.Counter.Reversible.PrimeCompression.rawTable,
      `Monodromy.Counter.Reversible.Radix.table,
      `Monodromy.Counter.Reversible.PortNetwork.relationLink] do
    unless visited.contains required do
      throwError "Native definition no longer reaches actual lift component {required}"
  logInfo "Native definition audit: actual lifts present; source interpreters absent."
