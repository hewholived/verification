Inferring program invariants that hold at particular program points is useful
proposition, and has applications in automated assertion proving, program optimizations
etc. In this project, we are interested in inferring a particular kind of
program invariant, which we call logical qualifiers, a term inspired from Liquid
Types. Restricting ourselves to inferring logical qualifiers allows us to discover
interesting program invariants, yet have a terminating algorithm, using the theory
of abstract interpretation and monotone framework.

In this work, we describe the underpinnings of logical qualifier inference for
a simple imperative language. We implemented a flow-sensitive logical qualifier
inference engine for this language, and we show how we leverage the automated
theorem prover Z3 in order to implement our tool. We also show how we can
handle certain theories (in particular, multiplication) not handled by Z3, when we
restrict ourselves to a particular set of logical qualifiers. Using a crafted example,
we show how and what program invariants are discovered by our tool.
