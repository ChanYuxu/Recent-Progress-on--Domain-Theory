import PointCentralFubini.IncidenceLower
import PointCentralFubini.IncidenceUpper

/-! The complete measure-source incidence theorem from Section 4. -/
set_option autoImplicit false
open Set Topology TopologicalSpace MeasureTheory
open scoped ENNReal
universe u
namespace PointCentralFubini

/-- Source contract: `prop:measure-source-incidence` (proposition 4.2).
Version: SHA-256 `134da69fa816824e5fefcb93a4e77a8cd5158c8aaab5ffd288ece2372e55d4e6`.
Locator: `source/manuscript.tex`, lines 346--357; no PDF was supplied.
Formalization status: `proved`; human review is pending.

Strict source TeX:
```latex
\begin{proposition}\label{prop:measure-source-incidence}
Let $X$ be a first-countable space and let $m$ be a finite $\tau$-smooth Borel measure on $X$. Suppose that a countable family $\mathcal C\subseteq\OO(X)$ satisfies
\begin{equation}\label{eq:countable-inner-approximation}
 m(U)=\sup\{m(C):C\in\mathcal C,\ C\subseteq U\}
 \qquad(U\in\OO(X)),
\end{equation}
where the supremum of the empty set is $0$. Put $L=\OO(X)$ and $M_x=\{U\in L:x\in U\}$. Then, for every finite $\eta\in\Val(L)$, the function $x\mapsto\eta(M_x)$ is lower semicontinuous and
\begin{equation}\label{eq:measure-source-incidence}
 \int_L m(U)\dd\eta(U)
 =\int_X\eta(M_x)\dd m(x).
\end{equation}
\end{proposition}
```
-/
theorem measure_source_incidence : MeasureSourceIncidenceStatement.{u} := by
  intro X _ _ m C hC η hη
  exact ⟨incidence_evaluation_isLSC η,
    le_antisymm (incidence_integral_upper m C hC η hη) (incidence_integral_lower m η hη)⟩

end PointCentralFubini
