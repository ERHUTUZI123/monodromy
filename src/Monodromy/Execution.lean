module

/-!
# Exact execution

Only integer winding numbers are needed at returning instruction boundaries.
The continuous lifting proof is in `Monodromy.Lifting`.
-/

@[expose] public section

namespace Monodromy.Program

inductive Instruction where
  | flip
  | control
  | write
  deriving Repr, BEq

def operation : Instruction → Bool × Bool → Bool × Bool
  | .flip, (a, b) => (!a, b)
  | .control, (a, b) => (if b then a else !a, b)
  | .write, (a, b) => (a, if a then b else !b)

def run : List Instruction → Bool × Bool → Bool × Bool
  | [], state => state
  | instruction :: rest, state => run rest (operation instruction state)

end Monodromy.Program

namespace Monodromy.Execution

abbrev Root := Bool × Bool

/-- Winding numbers of the two base circles, selected by the current root. -/
def winding : Program.Instruction → Root → Int × Int
  | .flip, (_, b) => (if b then -1 else 1, 0)
  | .control, (_, b) => (if b then 0 else 1, 0)
  | .write, (a, _) => (0, if a then 0 else 1)

/-- Each full base turn contributes a half turn to the carried phase. -/
def follow (root : Root) (turns : Int × Int) : Root :=
  (if turns.1 % 2 == 0 then root.1 else !root.1,
   if turns.2 % 2 == 0 then root.2 else !root.2)

def turns (inverse : Bool) (instruction : Program.Instruction) (root : Root) : Int × Int :=
  let w := winding instruction root
  if inverse then (-w.1, -w.2) else w

def step (inverse : Bool) (instruction : Program.Instruction) (root : Root) : Root :=
  follow root (turns inverse instruction root)

def run (inverse : Bool) : List Program.Instruction → Root → Root
  | [], root => root
  | instruction :: rest, root => run inverse rest (step inverse instruction root)

end Monodromy.Execution
