import PointCentralFubini.Basic

set_option autoImplicit false
open Set Topology TopologicalSpace
open scoped ENNReal
universe u v
namespace PointCentralFubini

/-- Bridge to mathlib's Scott topology, without installing an order topology. -/
theorem scott_continuous_iff {P : Type u} {Q : Type v} [Preorder P] [Preorder Q]
    (f : P → Q) : ScottContinuous f ↔
    Continuous (fun x : WithScott P => WithScott.toScott (f (WithScott.ofScott x))) := by
  change ScottContinuous (fun x : WithScott P => WithScott.toScott (f (WithScott.ofScott x))) ↔ _
  rw [← scottContinuousOn_univ]
  exact Topology.IsScott.scottContinuousOn_iff_continuous (fun _ _ _ => mem_univ _)

theorem scott_isLSC {P : Type u} [Preorder P] {f : P → ℝ≥0∞}
    (hf : ScottContinuous f) : IsLSC (fun x : WithScott P => f (WithScott.ofScott x)) := by
  intro r
  exact (scott_Ioi_open r).preimage ((scott_continuous_iff f).mp hf)

/-- Membership at a fixed point is a Scott-open subset of the open lattice. -/
def pointOpen {X : Type u} [TopologicalSpace X] (x : X) : ScottOpens (Opens X) := by
  refine ⟨{U | x ∈ WithScott.ofScott U}, ?_⟩
  rw [Topology.IsScott.isOpen_iff_isUpperSet_and_dirSupInaccOn (D := Set.univ)]
  refine ⟨?_, ?_⟩
  · intro U V hUV hx; exact hUV hx
  · intro A _ hn hd p hp hx
    have he : p = sSup A := hp.unique (isLUB_sSup A)
    rw [he] at hx
    have hx' : x ∈ (sSup A : Opens X) := hx
    obtain ⟨U, hUA, hxU⟩ := Opens.mem_sSup.mp hx' 
    exact ⟨U, hUA, hxU⟩

@[simp] theorem mem_pointOpen {X : Type u} [TopologicalSpace X]
    (x : X) (U : Opens X) : WithScott.toScott U ∈ pointOpen x ↔ x ∈ U := Iff.rfl

/-- Source `lem:membership`: the evaluation transpose `n_P`. -/
def neighbourhoodMap (P : Type u) [PartialOrder P] (x : P) : ScottOpens (ScottOpens P) :=
  pointOpen (WithScott.toScott x)

theorem neighbourhoodMap_scott (P : Type u) [PartialOrder P] :
    ScottContinuous (neighbourhoodMap P) := by
  intro A hn hd p hp
  constructor
  · rintro H ⟨x, hx, rfl⟩ U hxU
    exact (Topology.IsScott.isUpperSet_of_isOpen (D := Set.univ) U.isOpen) (hp.1 hx) hxU
  · intro H hH U hpU
    have hu := ((Topology.IsScott.isOpen_iff_isUpperSet_and_dirSupInaccOn (D := Set.univ)).mp U.isOpen).2
    obtain ⟨x, hxA, hxU⟩ := hu (Set.mem_univ _) hn hd hp hpU
    exact hH ⟨x, hxA, rfl⟩ hxU

def incidenceOpen (P : Type u) [PartialOrder P] : ScottOpens (P × ScottOpens P) := by
  refine ⟨{z | WithScott.toScott (WithScott.ofScott z).1 ∈ (WithScott.ofScott z).2}, ?_⟩
  rw [Topology.IsScott.isOpen_iff_isUpperSet_and_dirSupInaccOn (D := Set.univ)]
  refine ⟨?_, ?_⟩
  · intro a b hab ha
    exact hab.2 ((Topology.IsScott.isUpperSet_of_isOpen (D := Set.univ) a.2.isOpen) hab.1 ha)
  · intro A _ hn hd p hp hpU
    have hp' := hp
    change IsLUB (show Set (P × ScottOpens P) from A) (WithScott.ofScott p) at hp'
    rw [isLUB_prod] at hp'
    have he : p.2 = sSup (Prod.snd '' A) := hp'.2.unique (isLUB_sSup _)
    change WithScott.toScott p.1 ∈ p.2 at hpU
    rw [he] at hpU
    simp only [Opens.mem_sSup, Set.mem_image] at hpU
    obtain ⟨U, ⟨i, hi, rfl⟩, hpUi⟩ := hpU
    have hu := ((Topology.IsScott.isOpen_iff_isUpperSet_and_dirSupInaccOn (D := Set.univ)).mp i.2.isOpen).2
    obtain ⟨x, ⟨j, hj, rfl⟩, hxU⟩ :=
      hu (mem_univ _) (hn.image _) (directedOn_image.mpr (hd.mono monotone_fst)) hp'.1 hpUi
    obtain ⟨k, hk, hik, hjk⟩ := hd i hi j hj
    exact ⟨k, hk, hik.2 ((Topology.IsScott.isUpperSet_of_isOpen (D := Set.univ) i.2.isOpen) hjk.1 hxU)⟩

/-- Source contract: `lem:membership` (lemma 2.7).
Version: SHA-256 `134da69fa816824e5fefcb93a4e77a8cd5158c8aaab5ffd288ece2372e55d4e6`.
Locator: `source/manuscript.tex`, lines 187--189; no PDF was supplied.
Formalization status: `proved`; human review is pending.

Strict source TeX:
```latex
\begin{lemma}\label{lem:membership}
The relation $E_P$ is Scott open in $P\times\sigma(P)$, and $n_P:P\to\sigma(\sigma(P))$, $n_P(x)=M_x$, is Scott-continuous.
\end{lemma}
```
-/
theorem membership (P : Type u) [PartialOrder P] :
    IsOpen (incidenceOpen P : Set (WithScott (P × ScottOpens P))) ∧
      ScottContinuous (neighbourhoodMap P) :=
  ⟨(incidenceOpen P).isOpen,neighbourhoodMap_scott P⟩

/-- The continuous section map used in the converse incidence implication. -/
def sectionMap {P : Type u} {Q : Type v} [PartialOrder P] [PartialOrder Q]
    (W : ScottOpens (P × Q)) (y : Q) : ScottOpens P := by
  refine ⟨{x | WithScott.toScott (WithScott.ofScott x, y) ∈ W}, ?_⟩
  have hf : ScottContinuous (fun x : P => (x,y)) :=
    ScottContinuous.id.prodMk (ScottContinuous.const y)
  exact W.isOpen.preimage ((scott_continuous_iff _).mp hf)

theorem sectionMap_scott {P : Type u} {Q : Type v} [PartialOrder P] [PartialOrder Q]
    (W : ScottOpens (P × Q)) : ScottContinuous (sectionMap W) := by
  intro A hn hd p hp
  constructor
  · rintro H ⟨y, hy, rfl⟩ x hx
    have hle : WithScott.toScott (WithScott.ofScott x,y) ≤
        WithScott.toScott (WithScott.ofScott x,p) := ⟨le_rfl, hp.1 hy⟩
    exact (Topology.IsScott.isUpperSet_of_isOpen (D := Set.univ) W.isOpen) hle hx
  · intro H hH x hx
    have hf : ScottContinuous (fun y : Q => (WithScott.ofScott x,y)) :=
      (ScottContinuous.const _).prodMk ScottContinuous.id
    have hw := ((Topology.IsScott.isOpen_iff_isUpperSet_and_dirSupInaccOn (D := Set.univ)).mp W.isOpen).2
    have hAp := hf hn hd hp
    obtain ⟨z, ⟨y, hyA, rfl⟩, hzy⟩ := hw (mem_univ _) (hn.image _)
      (directedOn_image.mpr (hd.mono hf.monotone)) hAp hx
    exact hH ⟨y, hyA, rfl⟩ hzy

end PointCentralFubini
