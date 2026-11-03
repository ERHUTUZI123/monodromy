A try on Computation using Monodromy in Topology

When playing around with monodromy, I observed that a closed path may return to its starting point while its analytic continuation reaches a different branch.

AKA like, you have one circle, it changes, another circle, it changes back.

I think that is pretty interesting and beautiful.

So, I generate an idea:

Can this phenomenon support computation?
More accurately, can such structure of analytic continuation itself account for memory, conditional execution, and computational universality?

Since think about it: every time one operation = a path winds once around a point, that means even the path can be stretched, compressed or distroted, as long as its topological relationship of winding around the point unchanged, the operation will be unchanged.

If we have such computation model and we have a computer using such computation model (for sure needs corresponding hardware design, and also does this hardware need to be electricity things? what about a wave, a wind, a light or any other physical obejct that compiles with such computational model?), technically it will be very stable and reverseable because of homotopy invariance.

So, I tried to construct.

The exponential covering provides an integer-valued memory through winding. Compositions of analytic coverings introduce hierarchical structure, while analytic selectors distinguish branches and guide subsequent paths.

A particularly simple identity is

\[
K_r^{g\circ f}(z)
=
K_{f(r)}^g(f(z))K_r^f(z).
\]

It expresses hierarchical selection through ordinary function composition.

With assitance of AI, Lean 4 and refereces of analytic simulations by Koiran–Moore and Graça et al., I have proven two theorems:

Theorem I — Turing Universality of such Monodromy Computation

A monodromy-based computational model is constructed with formally verified simulation of arbitrary Turing machines, preserving execution, termination, and divergence.

Theorem II — Structural Characterization of Computational Universality in Analytic Continuation

Under fixed, effective input and output encodings, the finite computational calculus constructed from logarithmic branch memory, analytic selection, state updates, covering-level descent, and program composition computes exactly the partial recursive functions:

\[
\mathcal C_{\mathrm{Mono}}=\mathcal R_{\mathrm{partial}}.
\]

The construction uses a fixed degree-three covering for finite branch queries. Removing the descent operation leaves a restricted Forward language with decidable halting, establishing a strict separation in computational power.

The characterization applies to this defined finite covering calculus.

Proof Ideas

So, basically

The first thing is that winding in the exponential covering gives us an integer memory. The interesting question is how to read it and use it to decide the next operation.

A fixed cubic covering can be used to read digits. Analytic selectors distinguish the branches, and path lifting executes the resulting state changes.

But reading a fixed number of digits only gives limited information. Descending through the covering hierarchy lets the next hidden digit become readable.

With memory, selection, writing and descent, finite programs can simulate the two stacks of a Turing machine.

For the other direction, each finite expression and transition rule is effectively computable, so its complete execution is partial recursive.

Finally, without descent, Forward programs remain governed by a finite observation quotient, and their halting problem is decidable. This gives the strict separation.

The constructions and proofs are formalized in Lean 4. 
I have saved them to the Open Science Framework (OSF) connected to my ORCID.
And the whole process I keep commiting to my github repo.

If you could provide any feedback on these ideas, I will appreciate a lot.

If you are interested, I can share more proof on them.