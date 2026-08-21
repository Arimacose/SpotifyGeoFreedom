# Verification status

The source files contain no proof placeholders. The authoritative status is the
GitHub Actions run on the dedicated research branch.

A green run must satisfy all of the following:

1. `lake build` succeeds;
2. Lean's environment checker succeeds;
3. the axiom audit finds only `propext`, `Classical.choice`, and `Quot.sound`;
4. `RiemannCvs/PrintAxioms.lean` elaborates and prints the dependency set of
   every headline theorem;
5. a textual placeholder guard finds no `sorry` or `admit` token in the Lean
   source directory.

Passing this package certifies only the finite-dimensional lemmas stated in the
source. It does not certify any unformalized analytic bridge or any claim about
zeta zeros.
