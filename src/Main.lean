module

import Monodromy.Execution
meta import all Monodromy.Execution

open Monodromy

private def usage : String :=
  "Monodromy — four roots\n\n" ++
  "Usage: monodromy [--inverse] [--trace] ROOT PROGRAM\n" ++
  "Roots: 1, -1, sqrt3, -sqrt3 (also √3 and −√3)\n" ++
  "Instructions: A flip, C conditional control, W conditional write\n" ++
  "--inverse  run the inverse program; --trace  show turns and roots\n" ++
  "With no arguments, demonstrate 1 → −√3 → 1.\n\n" ++
  "Example: monodromy --trace 1 CWC"

private def rootName : Execution.Root → String
  | (false, false) => "√3"
  | (true, false) => "−√3"
  | (false, true) => "1"
  | (true, true) => "−1"

private def parseRoot : String → Except String Execution.Root
  | "1" => .ok (false, true)
  | "-1" | "−1" => .ok (true, true)
  | "sqrt3" | "√3" => .ok (false, false)
  | "-sqrt3" | "−sqrt3" | "-√3" | "−√3" => .ok (true, false)
  | text => .error s!"Unknown root: {text}. Use 1, -1, sqrt3, or -sqrt3."

private def instructionName : Program.Instruction → String
  | .flip => "A"
  | .control => "C"
  | .write => "W"

private def parseInstruction : Char → Except String Program.Instruction
  | 'A' | 'a' => .ok .flip
  | 'C' | 'c' => .ok .control
  | 'W' | 'w' => .ok .write
  | letter => .error s!"Unknown instruction: {letter}. Use A, C, or W."

private def parseProgram (text : String) : Except String (List Program.Instruction) :=
  text.toList.mapM parseInstruction

private structure Options where
  inverse : Bool := false
  trace : Bool := false
  positional : List String := []

private def readOptions : List String → Options → Except String Options
  | [], options => .ok options
  | "--inverse" :: rest, options => readOptions rest { options with inverse := true }
  | "--trace" :: rest, options => readOptions rest { options with trace := true }
  | argument :: rest, options =>
      if argument.startsWith "--" then .error s!"Unknown option: {argument}"
      else readOptions rest { options with positional := options.positional ++ [argument] }

private def execute (inverse trace : Bool) (program : List Program.Instruction)
    (initial : Execution.Root) : IO Execution.Root := do
  if !trace then return Execution.run inverse program initial
  let mut root := initial
  for instruction in program do
    let turns := Execution.turns inverse instruction root
    let next := Execution.step inverse instruction root
    let direction := if inverse then "⁻¹" else ""
    IO.println s!"{instructionName instruction}{direction}  {rootName root}  turns(u,theta) {reprStr turns}  → {rootName next}"
    root := next
  return root

private def fail (message : String) : IO UInt32 := do
  IO.eprintln s!"{message}\n\n{usage}"
  return 2

private def launch (options : Options) : IO UInt32 := do
  match options.positional with
  | [] =>
      let program : List Program.Instruction := [.control, .write, .control]
      let program := if options.inverse then program.reverse else program
      let initial : Execution.Root := (false, true)
      let result ← execute options.inverse options.trace program initial
      let restored ← execute (!options.inverse) options.trace program.reverse result
      IO.println s!"{rootName initial} → {rootName result} → {rootName restored}"
      return 0
  | [rootText, programText] =>
      let request := do
        let root ← parseRoot rootText
        let program ← parseProgram programText
        pure (root, program)
      match request with
      | .error message => fail message
      | .ok (root, program) =>
          let program := if options.inverse then program.reverse else program
          let result ← execute options.inverse options.trace program root
          IO.println s!"{rootName root} → {rootName result}"
          return 0
  | _ => fail "Expected ROOT and PROGRAM together."

public def main (args : List String) : IO UInt32 := do
  if args.contains "--help" || args.contains "-h" then
    IO.println usage
    return 0
  match readOptions args {} with
  | .error message => fail message
  | .ok options => launch options
