import PointCentralFubini.MeasureSource
import PointCentralFubini.VietorisLift

/-! The source Section 4 conclusion, with every manuscript-internal dependency
proved. Registered external literature axioms remain visible in the audit. -/
set_option autoImplicit false
universe v
namespace PointCentralFubini

/-- Source contract: `thm:sorgenfrey-fubini` (theorem 4.7).
Version: SHA-256 `134da69fa816824e5fefcb93a4e77a8cd5158c8aaab5ffd288ece2372e55d4e6`.
Locator: `source/manuscript.tex`, lines 619--621; no PDF was supplied.
Formalization status: `proved`; human review is pending.

Strict source TeX:
```latex
\begin{theorem}\label{thm:sorgenfrey-fubini}
The dcpo $D=\mathcal Q(\mathbb R_\ell)$ is a Fubini object.
\end{theorem}
```
-/
theorem sorgenfrey_fubini : SorgenfreyFubiniStatement.{v} :=
  sorgenfrey_fubini_of_measure_dependencies measure_source_incidence full_vietoris_lift

end PointCentralFubini
