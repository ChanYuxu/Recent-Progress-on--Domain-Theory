# The Fubini Problem for Continuous Valuations on dcpos: A Counterexample under the Continuum Hypothesis

## Source index

The buildable project is in [ch-fubini-counterexample-lean](ch-fubini-counterexample-lean/README.md).

- [Main statement](ch-fubini-counterexample-lean/CHFubini/MainStatement.lean)
- [Main proof and the two integrals](ch-fubini-counterexample-lean/CHFubini/MainTheorems.lean)
- [Named source objects](ch-fubini-counterexample-lean/CHFubini/SourceConstruction.lean)
- [Full recursive existence theorem](ch-fubini-counterexample-lean/CHFubini/CHConstruction.lean)
- [Arbitrary-union null defect and limiting valuation](ch-fubini-counterexample-lean/CHFubini/LimitingValuation.lean)
- [Choquet definition](ch-fubini-counterexample-lean/CHFubini/Foundations.lean)
- [Direct type and axiom probe](ch-fubini-counterexample-lean/Verification.lean)
- [Verification boundaries](ch-fubini-counterexample-lean/VERIFICATION.md)

The main theorem is conditional on CH. It is proved without project-local mathematical axioms, but uses the standard Lean foundations `propext`, `Classical.choice`, and `Quot.sound`. The full categorical monad bridge, the final positive boundary, and the complete recursive specification of the fixed named sequence remain outside the verified scope described here. Human review is pending.

This is a curated Lean source distribution, not the original working directory. The paper TeX source, historical audit automation, deliberate bad-proof fixtures, local paths, and build caches are not included.
