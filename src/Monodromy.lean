module

public import Monodromy.Lifting
public import Monodromy.Finite
public import Monodromy.Observation
public import Monodromy.Logarithm
public import Monodromy.Choice
public import Monodromy.Autonomy
public import Monodromy.Cubic
public import Monodromy.Counter
public import Monodromy.ProgramCounter
public import Monodromy.Lattice
public import Monodromy.Control
public import Monodromy.Radix
public import Monodromy.Tower
public import Monodromy.TwoStacks
public import Monodromy.Machine
public import Monodromy.Universality

/-!
# Monodromy

A root is memory; continuation carries it through a computation.

The quartic is a fixed finite example. Finite persistent state has precise
computational bounds; logarithmic branches provide integer memory.
A marked regular root gives an analytic fiber selector. Internal feedback
uses it to generate paths, write state, and change subsequent selection.
Every finite run of the return system agrees with actual path transport.

An exponential power-cover tower gives ordered word memory. Two word branches
and a finite analytic controller simulate every finite TM0 table, preserving
the complete tape, halting, and divergence. Native finite runs are realized
by their own generated continuation paths.

The cubic supplies a second mechanism: one fixed loop acts selectively on
different roots, as proved from its explicit continuous lifts.
-/
