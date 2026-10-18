import PointCentralFubini.OpenFubini
set_option autoImplicit false
open Set Topology TopologicalSpace
open scoped ENNReal
universe u v
namespace PointCentralFubini
variable {P : Type u} [PartialOrder P]

/-- Source equation `eq:incidence`. -/
def IncidenceIdentity (μ : DValuation P) (ξ : DValuation (ScottOpens P)) : Prop :=
  integral ξ (fun U => μ (WithScott.ofScott U)) =
    integral μ (fun x => ξ (neighbourhoodMap P (WithScott.ofScott x)))

/-- Necessity in source proposition 2.8 (`prop:incidence`). -/
theorem incidence_of_central (μ : DValuation P) (hμ : Central.{u,u} μ)
    (ξ : DValuation (ScottOpens P)) : IncidenceIdentity μ ξ := by
  have ho := (commute_iff_openCommute μ ξ).mp
    (hμ (ScottOpens P) (completeLattice_isDcpo _) ξ) (incidenceOpen P)
  have hl : integral μ (fun x => ξ (sliceRight (incidenceOpen P) (WithScott.ofScott x))) =
      integral μ (fun x => ξ (neighbourhoodMap P (WithScott.ofScott x))) := by
    apply integral_congr μ; intro x
    congr 1
  have hr : integral ξ (fun U => μ (sectionMap (incidenceOpen P) (WithScott.ofScott U))) =
      integral ξ (fun U => μ (WithScott.ofScott U)) := by
    apply integral_congr ξ; intro U
    congr 1
  exact (hl.symm.trans (ho.trans hr)).symm

/-- Sufficiency of canonical incidence, with arbitrary partner universe. -/
theorem central_of_incidence (μ : DValuation P)
    (hμ : ∀ ξ : DValuation (ScottOpens P), IncidenceIdentity μ ξ) : Central.{u,v} μ := by
  intro Q _ _ ν
  apply (commute_iff_openCommute μ ν).mpr
  intro W
  let t : WithScott Q → WithScott (ScottOpens P) :=
    fun y => WithScott.toScott (sectionMap W (WithScott.ofScott y))
  have ht : Continuous t := (scott_continuous_iff _).mp (sectionMap_scott W)
  have he := hμ (ν.push t ht)
  unfold IncidenceIdentity at he
  rw [integral_push ν t ht _ (scott_isLSC μ.continuous)] at he
  have hr : integral μ (fun x => (ν.push t ht)
      (neighbourhoodMap P (WithScott.ofScott x))) =
      integral μ (fun x => ν (sliceRight W (WithScott.ofScott x))) := by
    apply integral_congr μ; intro x
    change ν (Opens.comap ⟨t,ht⟩ (neighbourhoodMap P (WithScott.ofScott x))) = _
    congr 1
  rw [hr] at he
  exact he.symm

/-- Source contract: `prop:incidence` (proposition 2.8).
Version: SHA-256 `134da69fa816824e5fefcb93a4e77a8cd5158c8aaab5ffd288ece2372e55d4e6`.
Locator: `source/manuscript.tex`, lines 208--214; no PDF was supplied.
Formalization status: `proved`; human review is pending.

Strict source TeX:
```latex
\begin{proposition}\label{prop:incidence}
A valuation $\mu\in\Val(P)$ is central if and only if every $\xi\in\Val(\sigma(P))$ satisfies

\begin{equation}\label{eq:incidence}
 \int_{\sigma(P)}\mu(U)\dd\xi(U)=\int_P\xi(M_x)\dd\mu(x).
\end{equation}
\end{proposition}
```
-/
theorem central_iff_incidence (μ : DValuation P) :
    Central.{u,u} μ ↔ ∀ ξ : DValuation (ScottOpens P), IncidenceIdentity μ ξ :=
  ⟨incidence_of_central μ, central_of_incidence μ⟩

/-- Source contract: `thm:descent` (proposition 5.1).
Version: SHA-256 `134da69fa816824e5fefcb93a4e77a8cd5158c8aaab5ffd288ece2372e55d4e6`.
Locator: `source/manuscript.tex`, lines 659--661; no PDF was supplied.
Formalization status: `proved`; human review is pending.

Strict source TeX:
```latex
\begin{proposition}\label{thm:descent}
If $\sigma(P)$ is a Fubini object, then so is $P$.
\end{proposition}
```
-/
theorem fubini_descent (hL : FubiniObject.{u,u} (ScottOpens P)) : FubiniObject.{u,v} P := by
  intro μ
  apply central_of_incidence μ
  intro ξ
  let n : WithScott P → WithScott (ScottOpens (ScottOpens P)) :=
    fun x => WithScott.toScott (neighbourhoodMap P (WithScott.ofScott x))
  have hn : Continuous n := (scott_continuous_iff _).mp (neighbourhoodMap_scott P)
  have he := incidence_of_central ξ (hL ξ) (μ.push n hn)
  unfold IncidenceIdentity at he
  rw [integral_push μ n hn _ (scott_isLSC ξ.continuous)] at he
  have hl : integral ξ (fun U => (μ.push n hn)
      (neighbourhoodMap (ScottOpens P) (WithScott.ofScott U))) =
      integral ξ (fun U => μ (WithScott.ofScott U)) := by
    apply integral_congr ξ; intro U
    change μ (Opens.comap ⟨n,hn⟩ (neighbourhoodMap (ScottOpens P) (WithScott.ofScott U))) = _
    congr 1
  rw [hl] at he
  exact he.symm
end PointCentralFubini
