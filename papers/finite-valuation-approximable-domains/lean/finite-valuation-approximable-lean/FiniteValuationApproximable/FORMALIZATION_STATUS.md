# Finite-valuation approximable domains: final formalization status

## Source and delivery boundary

- Source: private source manuscript (not included in this public Lean package)
- Title: *A Solution to the Jung--Tix Problem: Finite-Valuation Approximable Domains*
- Source SHA-256:
  `4b2e65f0f96347bea4df7571e8993ad6e888c0ff7181c1305c5056880365ac94`
- Lean/mathlib toolchain: `v4.30.0-rc2`
- Standalone project: this package root

The standalone project depends only on mathlib. Its local
`OrderTheory.lean` supplies the dcpo, Scott-continuity, basis,
function-space and retraction interfaces used by this manuscript. No module
from the surrounding textbook or any other local project is imported.

## Final result

The main theorem is proved without any paper-internal assumption.

The original public endpoints are in `Final.lean`, and all headline endpoints
are collected with explicit proof terms in `MainTheorems.lean`:

- `thm_main_objectwise : MainTheoremObjectwise` proves all four numbered
  clauses of `thm:main`.
- `thm_main_categorical_consequences` supplies the genuine terminal,
  product and exponential universal properties of the full local FVA
  subcategory, and restrictions of both valuation monads.
- `thm_main` is a single propositional endpoint combining the numbered
  clauses with existence of that categorical and monadic structure.

The categorical endpoint is not an object-closure proposition under another
name. `CategoricalConsequences.lean` defines:

- objects carrying `IsFVA`, with homs definitionally equal to bundled
  Scott-continuous maps;
- identity, composition and their laws;
- a terminal object and its uniqueness property;
- binary products with projections, pairing and uniqueness;
- exponentials with evaluation, curry, uncurry, both inverse equations and
  uniqueness;
- a Kleisli-monad restriction record containing object and arrow actions,
  unit, multiplication, extension, unit laws and associativity;
- derived unit/multiplication naturality and the usual multiplication laws;
- concrete restrictions for both `ContinuousValuation.VSub` and
  `ContinuousValuation.VOne`.

## Main proof chain

| Source step | Principal Lean endpoint | Module |
| --- | --- | --- |
| finite monotone-table polytope | `finite_monotone_table_isFVA` | `FinitePolytopeHaar.lean` |
| genuine finite probability kernels | `finitePolytopeKernelApproximation` | `FinitePolytopeKernel.lean` |
| kernel lifting | `kernel_lifting_of_approximation` and its two component theorems | `KernelLifting.lean` |
| finite generators | `finiteGeneratorsAreFVA` | `ConcreteGenerators.lean` |
| finite generator products | `global_product` | `FiniteProductContinuity.lean` |
| function-space transfer | `global_functionSpace_of_finite_generators` | `GlobalFunction.lean` |
| subprobability transfer | `global_vSub_of_finite_double_generators` | `GlobalValuation.lean` |
| probability transfer | `global_vOne_of_finite_double_generators` | `GlobalVOne.lean` |
| four numbered clauses | `thm_main_objectwise` | `Final.lean` |
| Cartesian closedness and monad restriction | `thm_main_categorical_consequences` | `Final.lean` |
| combined endpoint | `thm_main` | `Final.lean` |

The empty finite-column case is not hidden behind a nonemptiness assumption.
`ConcreteGenerators.lean` constructs a constant Dirac probability kernel
on a singleton stage and proves it is exactly the unit kernel. The nonempty
case uses the concrete Haar randomized-rounding law.

The valuation conclusions use the genuine Scott-open continuous-valuation
types, not finite-vector substitutes. Finite atomic probability laws are
transported to genuine `VOne` values through the proved finite-poset order
isomorphism.

## Proof-debt audit

The manuscript-specific modules contain no `sorry`, `admit`, local
paper theorem axiom, `opaque` proof, or `unsafe` declaration used to close
the result. The concrete Haar construction, the genuine-kernel bridge,
kernel lifting, generator specialization, global transfers, main assembly
and categorical package all compile.

There are no non-foundational axioms reachable from `thm_main`.  The two
formerly isolated literature boundaries have both been discharged by
internal Lean proofs.

### Gierz source theorem

`External.gierz_II_2_18_fs_exponential`

- Gierz et al., *Continuous Lattices and Domains* (2003),
  Proposition II-2.18, printed p. 168.
- Exact content: exponentials of FS-domains are FS-domains.
- Internal proof: `External/GierzInternal.lean`; the `External` declaration
  is an ordinary theorem alias.

### Jones--Plotkin/Jones source theorems

The source-facing declarations are:

- `External.jonesIntegral`
- `External.jonesIntegral_indicator`
- `External.jonesIntegral_mono`
- `External.jones_1990_thm_3_13_DMC`
- `External.jonesKleisli`
- `External.jonesKleisli_apply`
- `External.jonesKleisli_scottContinuous_input`
- `External.jonesKleisli_dirac`
- `External.jonesKleisli_unit`
- `External.jonesKleisli_assoc`
- `External.jonesKleisli_unit_comp_eq_pushforward`
- `External.jones_1990_cor_5_4_vSub_continuous`

They correspond to Jones--Plotkin (LICS 1989, Sections 2--4, especially
Theorems 2.1, 3.1 and 3.3) and Jones's 1990 thesis (Theorem 3.13,
Theorems 4.3/4.5 and Corollary 5.4).  All are now definitions or theorems over
the internal modules `JonesIntegralCore` through `JonesContinuity`.
Corollary 5.4 is proved via certified finite atomic approximants: each is
below and genuinely way below its source, the family is directed, and its
supremum is the source valuation, including the empty-carrier case.

`AxiomAudit.lean` verifies that `#print axioms` for every source-facing
headline endpoint reports only Lean's foundational `propext`,
`Classical.choice` and `Quot.sound`.

## Verification

From the package root, run:

```sh
lake build
lake env lean FiniteValuationApproximable/AxiomAudit.lean
```

These commands check compilation and the headline results' transitive axioms. They do not replace manuscript-to-Lean semantic-fidelity assessment or human mathematical review.

## Explicitly unformalized or excluded material

The mathematical remarks, including the directed-FVA extension and category-size countability remark, are outside the formalized scope.

The post-main-theorem comparison appendix is not part of the final theorem's
dependency graph. `FiniteBC*.lean` and `Comparison.lean` contain genuine
partial results, but this delivery does **not** claim complete formalizations
of:

- the full countably based bc-domain inclusion theorem;
- the complete `B_5 \notin FVA` comparison chain;
- the final strict category-size/incomparability theorem;
- the Chen--Kou--Lyu finite-poset classification.

Explanatory prose, duplicated/alternative proof paragraphs, and commented-out
source material are also not mirrored as separate declarations. These
omissions do not occur in the dependency graph of `thm_main`.

The local categorical package proves all relevant category and monad laws,
but is intentionally standalone rather than an instance of mathlib's
`CategoryTheory` hierarchy. This is an integration boundary, not an
unproved mathematical assertion.
