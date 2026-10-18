import PointCentralFubini.ValuationLimits
set_option autoImplicit false
open Set Topology TopologicalSpace
open scoped ENNReal
universe u v
namespace PointCentralFubini

/-- Source contract: `thm:heckmann-approximation` (theorem 2.1).
Version: SHA-256 `134da69fa816824e5fefcb93a4e77a8cd5158c8aaab5ffd288ece2372e55d4e6`.
Locator: `source/manuscript.tex`, lines 138--141; no PDF was supplied.
Formalization status: `external_axiom`; human review is pending.

Strict source TeX:
```latex
\begin{theorem}\label{thm:heckmann-approximation}
\cite[Theorem~4.2]{Heckmann1996}
On a $T_0$ space, every continuous valuation is a directed supremum of bounded continuous valuations, and every point-continuous valuation is a directed supremum of bounded point-continuous valuations.
\end{theorem}
```
-/
axiom heckmann_approximation (X : Type u) [TopologicalSpace X] [T0Space X]
    (μ : Valuation X) :
    (∃ A : Set (Valuation X), A.Nonempty ∧ DirectedOn (· ≤ ·) A ∧
      (∀ ν ∈ A, ν.Finite) ∧ ∀ U, μ U = ⨆ ν : A, ν.val U) ∧
    (PointContinuous μ → ∃ A : Set (Valuation X), A.Nonempty ∧ DirectedOn (· ≤ ·) A ∧
      (∀ ν ∈ A, ν.Finite ∧ PointContinuous ν) ∧ ∀ U, μ U = ⨆ ν : A, ν.val U)

 theorem heckmann_bounded_approximation (X : Type u) [TopologicalSpace X] [T0Space X]
    (μ : Valuation X) :
    ∃ A : Set (Valuation X), A.Nonempty ∧ DirectedOn (· ≤ ·) A ∧
      (∀ ν ∈ A, ν.Finite) ∧ ∀ U, μ U = ⨆ ν : A, ν.val U :=
  (heckmann_approximation X μ).1

 theorem heckmann_point_bounded_approximation (X : Type u) [TopologicalSpace X] [T0Space X]
    (μ : Valuation X) (hμ : PointContinuous μ) :
    ∃ A : Set (Valuation X), A.Nonempty ∧ DirectedOn (· ≤ ·) A ∧
      (∀ ν ∈ A, ν.Finite ∧ PointContinuous ν) ∧ ∀ U, μ U = ⨆ ν : A, ν.val U :=
  (heckmann_approximation X μ).2 hμ

/-- Source contract: `thm:point-central-subprob` (theorem 2.4).
Version: SHA-256 `134da69fa816824e5fefcb93a4e77a8cd5158c8aaab5ffd288ece2372e55d4e6`.
Locator: `source/manuscript.tex`, lines 159--162; no PDF was supplied.
Formalization status: `external_axiom`; human review is pending.

Strict source TeX:
```latex
\begin{theorem}\label{thm:point-central-subprob}
\cite[Theorem~21]{JLMZ2021}
Let $P,Q$ be dcpos, $\mu\in\Point(P)\cap\ValSub(P)$ and $\nu\in\ValSub(Q)$. For every Scott-open $W\subseteq P\times Q$, $\int_P\nu(W_x)\dd\mu(x)=\int_Q\mu(W^y)\dd\nu(y)$, where $W_x=\{y:(x,y)\in W\}$ and $W^y=\{x:(x,y)\in W\}$.
\end{theorem}
```
-/
axiom jlmz_open_fubini (P : Type u) (Q : Type v) [PartialOrder P] [PartialOrder Q]
    (hP : IsDcpo P) (hQ : IsDcpo Q) (μ : DValuation P) (ν : DValuation Q)
    (hpoint : PointContinuous μ) (hμ : μ.Subprobability) (hν : ν.Subprobability) :
    OpenCommute μ ν
end PointCentralFubini
