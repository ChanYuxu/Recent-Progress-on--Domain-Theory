import CHFubini.Foundations
import Mathlib.Topology.Sets.Compacts
import Mathlib.Topology.Sets.Opens
import Mathlib.Topology.Order.ScottTopology
import Mathlib.Topology.Order.Compact

/-!
Independent, mathlib-only candidates for Sections 5 and 6 of the CH Fubini paper.

The dcpo intersection proof is adapted from
`PointCentralFubini_Lean/PointCentralFubini/SmythDcpo.lean`, SHA-256
`bb2d886133aa408c6c1e3a03925d5feb85b3c3b05b8657ab71412c9d7b2d9140`.
All topology statements below use the actual `WithScott` topology. No upper
Vietoris/Scott identification, sobriety, or well-filteredness is assumed.
-/

set_option autoImplicit false

open Set Topology TopologicalSpace

universe u v w

namespace CHFubini

abbrev Smyth (X : Type u) [TopologicalSpace X] := OrderDual (NonemptyCompacts X)


def carrier {X : Type u} [TopologicalSpace X] (C : Smyth X) : Set X :=
  (OrderDual.ofDual C : NonemptyCompacts X)

@[simp] theorem le_iff_carrier_subset {X : Type u} [TopologicalSpace X]
    (C D : Smyth X) : C ≤ D ↔ carrier D ⊆ carrier C := Iff.rfl

/-- Source Lemma `lem:filtered-intersection`, including its open-test equivalence. -/
theorem filtered_compact_intersection {X : Type u} {I : Type v}
    [TopologicalSpace X] [T2Space X] [Nonempty I]
    (F : I → Set X) (hF : Directed (· ⊇ ·) F)
    (hne : ∀ i, (F i).Nonempty) (hc : ∀ i, IsCompact (F i)) :
    (⋂ i, F i).Nonempty ∧ IsCompact (⋂ i, F i) ∧
      ∀ U : Set X, IsOpen U → ((⋂ i, F i) ⊆ U ↔ ∃ i, F i ⊆ U) := by
  refine ⟨IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    F hF hne hc (fun i => (hc i).isClosed), ?_, ?_⟩
  · let i₀ : I := Classical.choice inferInstance
    exact (hc i₀).of_isClosed_subset
      (isClosed_iInter (fun i => (hc i).isClosed)) (iInter_subset F i₀)
  · intro U hU
    constructor
    · intro hsub
      exact exists_subset_nhds_of_isCompact' hF hc (fun i => (hc i).isClosed)
        (fun x hx => hU.mem_nhds (hsub hx))
    · rintro ⟨i, hi⟩
      exact (iInter_subset F i).trans hi

private theorem directed_carriers {X : Type u} [TopologicalSpace X]
    {A : Set (Smyth X)} (hd : DirectedOn (· ≤ ·) A) :
    Directed (· ⊇ ·) (fun C : A => carrier C.val) := by
  intro C D
  obtain ⟨E, hE, hCE, hDE⟩ := hd C.val C.property D.val D.property
  exact ⟨⟨E, hE⟩, hCE, hDE⟩

noncomputable def directedInter {X : Type u} [TopologicalSpace X] [T2Space X]
    (A : Set (Smyth X)) (hn : A.Nonempty) (hd : DirectedOn (· ≤ ·) A) : Smyth X := by
  letI : Nonempty A := hn.to_subtype
  have h := filtered_compact_intersection (fun C : A => carrier C.val)
    (directed_carriers hd)
    (fun C => (OrderDual.ofDual C.val : NonemptyCompacts X).nonempty)
    (fun C => (OrderDual.ofDual C.val : NonemptyCompacts X).isCompact)
  exact OrderDual.toDual ⟨⟨⋂ C : A, carrier C.val, h.2.1⟩, h.1⟩

@[simp] theorem carrier_directedInter {X : Type u}
    [TopologicalSpace X] [T2Space X] (A : Set (Smyth X))
    (hn : A.Nonempty) (hd : DirectedOn (· ≤ ·) A) :
    carrier (directedInter A hn hd) = ⋂ C : A, carrier C.val := rfl

theorem directedInter_isLUB {X : Type u} [TopologicalSpace X] [T2Space X]
    (A : Set (Smyth X)) (hn : A.Nonempty) (hd : DirectedOn (· ≤ ·) A) :
    IsLUB A (directedInter A hn hd) := by
  constructor
  · intro C hC
    exact iInter_subset (fun D : A => carrier D.val) ⟨C, hC⟩
  · intro C hC
    exact subset_iInter (fun D => hC D.property)

/-- Source assertion following `lem:filtered-intersection`: the actual reverse
inclusion poset is a dcpo. This does not add a bottom element. -/
theorem smyth_isDcpo (X : Type u) [TopologicalSpace X] [T2Space X] :
    ∀ A : Set (Smyth X), A.Nonempty → DirectedOn (· ≤ ·) A →
      ∃ C, IsLUB A C := by
  intro A hn hd
  exact ⟨directedInter A hn hd, directedInter_isLUB A hn hd⟩

theorem carrier_isLUB_eq_iInter {X : Type u} [TopologicalSpace X] [T2Space X]
    {A : Set (Smyth X)} (hn : A.Nonempty) (hd : DirectedOn (· ≤ ·) A)
    {C : Smyth X} (hC : IsLUB A C) :
    carrier C = ⋂ D : A, carrier D.val := by
  rw [hC.unique (directedInter_isLUB A hn hd)]
  rfl

theorem isLUB_open_test {X : Type u} [TopologicalSpace X] [T2Space X]
    {A : Set (Smyth X)} (hn : A.Nonempty) (hd : DirectedOn (· ≤ ·) A)
    {C : Smyth X} (hC : IsLUB A C) (U : Opens X) :
    carrier C ⊆ U ↔ ∃ D ∈ A, carrier D ⊆ U := by
  letI : Nonempty A := hn.to_subtype
  rw [carrier_isLUB_eq_iInter hn hd hC]
  have h := (filtered_compact_intersection (fun D : A => carrier D.val)
    (directed_carriers hd)
    (fun D => (OrderDual.ofDual D.val : NonemptyCompacts X).nonempty)
    (fun D => (OrderDual.ofDual D.val : NonemptyCompacts X).isCompact)).2.2
    (U : Set X) U.isOpen
  simpa only [Subtype.exists, exists_prop] using h

/-- The upper-Vietoris generators are genuinely Scott open, independently of
whether they generate all Scott opens. -/
def boxOpen {X : Type u} [TopologicalSpace X] [T2Space X]
    (U : Opens X) : ScottOpens (Smyth X) := by
  refine ⟨{C | carrier (WithScott.ofScott C) ⊆ U}, ?_⟩
  rw [Topology.IsScott.isOpen_iff_isUpperSet_and_dirSupInaccOn (D := Set.univ)]
  refine ⟨?_, ?_⟩
  · intro C D hCD hC
    exact (show carrier (WithScott.ofScott D) ⊆ carrier (WithScott.ofScott C)
      from hCD).trans hC
  · intro A _ hn hd C hC hCU
    exact (isLUB_open_test hn hd hC U).mp hCU

/-- Source definition `eq:KC`, as an open set of the actual Scott topology on
the lattice of opens of `X`. -/
def compactNeighborhood {X : Type u} [TopologicalSpace X]
    (C : Smyth X) : ScottOpens (Opens X) := by
  refine ⟨{U | carrier C ⊆ ((WithScott.ofScott U : Opens X) : Set X)}, ?_⟩
  rw [Topology.IsScott.isOpen_iff_isUpperSet_and_dirSupInaccOn (D := Set.univ)]
  refine ⟨?_, ?_⟩
  · intro U V hUV hCU
    change carrier C ⊆ ((WithScott.ofScott U : Opens X) : Set X) at hCU
    change carrier C ⊆ ((WithScott.ofScott V : Opens X) : Set X)
    exact fun x hx => hUV (hCU hx)
  · intro A _ hn hd U hU hCU
    letI : Nonempty A := hn.to_subtype
    have hsup : U = sSup A := hU.unique (isLUB_sSup A)
    have hcover : carrier C ⊆ ⋃ V : A, ((WithScott.ofScott V.val : Opens X) : Set X) := by
      intro x hx
      have hxU := hCU hx
      rw [hsup] at hxU
      obtain ⟨V, hV, hxV⟩ := Opens.mem_sSup.mp hxU
      exact mem_iUnion.mpr ⟨⟨V, hV⟩, hxV⟩
    have hdir : Directed (· ⊆ ·)
        (fun V : A => ((WithScott.ofScott V.val : Opens X) : Set X)) := by
      intro V W
      obtain ⟨Z, hZ, hVZ, hWZ⟩ := hd V.val V.property W.val W.property
      exact ⟨⟨Z, hZ⟩, hVZ, hWZ⟩
    obtain ⟨V, hV⟩ := (OrderDual.ofDual C : NonemptyCompacts X).isCompact.elim_directed_cover
      (fun V : A => ((WithScott.ofScott V.val : Opens X) : Set X))
      (fun V => (WithScott.ofScott V.val).isOpen) hcover hdir
    exact ⟨V.val, V.property, hV⟩

@[simp] theorem mem_compactNeighborhood {X : Type u} [TopologicalSpace X]
    (C : Smyth X) (U : Opens X) :
    WithScott.toScott U ∈ compactNeighborhood C ↔ carrier C ⊆ U := Iff.rfl

/-- Source equation `eq:KC-union`, for every nonempty directed family and its
actual least upper bound. -/
theorem compactNeighborhood_isLUB_eq_iUnion {X : Type u}
    [TopologicalSpace X] [T2Space X] {A : Set (Smyth X)}
    (hn : A.Nonempty) (hd : DirectedOn (· ≤ ·) A)
    {C : Smyth X} (hC : IsLUB A C) :
    (compactNeighborhood C : Set (WithScott (Opens X))) =
      ⋃ D : A, (compactNeighborhood D.val : Set (WithScott (Opens X))) := by
  ext U
  change (carrier C ⊆ ((WithScott.ofScott U : Opens X) : Set X)) ↔ _
  rw [isLUB_open_test hn hd hC]
  simp only [mem_iUnion, Subtype.exists, exists_prop]
  rfl

/-- The map taking a compact set to its open-neighborhood Scott-open set is
Scott continuous. This proves the mathematical bridge needed for the profile. -/
theorem compactNeighborhood_scottContinuous {X : Type u}
    [TopologicalSpace X] [T2Space X] : ScottContinuous (@compactNeighborhood X _) := by
  intro A hn hd C hC
  constructor
  · rintro H ⟨D, hD, rfl⟩ U hDU
    exact (show carrier C ⊆ carrier D from hC.1 hD).trans hDU
  · intro H hH U hCU
    obtain ⟨D, hD, hDU⟩ := (isLUB_open_test hn hd hC (WithScott.ofScott U)).mp hCU
    exact hH ⟨D, hD, rfl⟩ hDU

/-- Source Proposition `prop:g-continuous`, the continuity portion, exposed as
a proved composition bridge. The application must supply the real valuation
`rho` and its proved Scott continuity; it is not stored as a target assumption. -/
theorem compactProfile_scottContinuous {X : Type u} {E : Type w}
    [TopologicalSpace X] [T2Space X] [Preorder E]
    (rho : ScottOpens (Opens X) → E) (hrho : ScottContinuous rho) :
    ScottContinuous (fun C : Smyth X => rho (compactNeighborhood C)) :=
  compactNeighborhood_scottContinuous.comp hrho

/-- Source Proposition `prop:W-Scott-open`: incidence in the coordinatewise
product order, not merely in the product of the two Scott topologies. -/
def incidenceOpen {X : Type u} [TopologicalSpace X] [T2Space X] :
    ScottOpens (Smyth X × Opens X) := by
  refine ⟨{p | carrier (WithScott.ofScott p).1 ⊆ (WithScott.ofScott p).2}, ?_⟩
  rw [Topology.IsScott.isOpen_iff_isUpperSet_and_dirSupInaccOn (D := Set.univ)]
  refine ⟨?_, ?_⟩
  · intro p q hpq hp
    exact (show carrier q.1 ⊆ carrier p.1 from hpq.1).trans (hp.trans hpq.2)
  · intro A _ hn hd p hp hpinc
    classical
    by_contra hno
    have hnot : ∀ q ∈ A, ¬ carrier q.1 ⊆ (q.2 : Set X) := by
      intro q hq hqinc
      exact hno ⟨q, hq, hqinc⟩
    letI : Nonempty A := hn.to_subtype
    let F : A → Set X := fun q => carrier q.val.1 \ (q.val.2 : Set X)
    have hne : ∀ q, (F q).Nonempty := by
      intro q
      exact Set.not_subset.mp (hnot q.val q.property)
    have hdir : Directed (· ⊇ ·) F := by
      intro q r
      obtain ⟨s, hs, hqs, hrs⟩ := hd q.val q.property r.val r.property
      refine ⟨⟨s, hs⟩, ?_, ?_⟩
      · intro x hx
        exact ⟨hqs.1 hx.1, fun hxq => hx.2 (hqs.2 hxq)⟩
      · intro x hx
        exact ⟨hrs.1 hx.1, fun hxr => hx.2 (hrs.2 hxr)⟩
    have hc : ∀ q, IsCompact (F q) := fun q =>
      (OrderDual.ofDual q.val.1 : NonemptyCompacts X).isCompact.inter_right
        q.val.2.isOpen.isClosed_compl
    obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
      F hdir hne hc (fun q => (hc q).isClosed)
    change IsLUB (show Set (Smyth X × Opens X) from A) (WithScott.ofScott p) at hp
    rw [isLUB_prod] at hp
    have hsingle : p.1 ≤ OrderDual.toDual ({x} : NonemptyCompacts X) := by
      apply hp.1.2
      rintro C ⟨q, hq, rfl⟩
      intro y hy
      have hyx : y = x := (NonemptyCompacts.mem_singleton y x).mp hy
      subst y
      exact (mem_iInter.mp hx ⟨q, hq⟩).1
    have hxp : x ∈ carrier p.1 :=
      hsingle ((NonemptyCompacts.mem_singleton x x).mpr rfl)
    have hxpU : x ∈ p.2 := hpinc hxp
    have hsup : p.2 = sSup (Prod.snd '' A) :=
      hp.2.unique (isLUB_sSup _)
    rw [hsup] at hxpU
    obtain ⟨V, ⟨q, hq, rfl⟩, hxV⟩ := Opens.mem_sSup.mp hxpU
    exact (mem_iInter.mp hx ⟨q, hq⟩).2 hxV

@[simp] theorem mem_incidenceOpen {X : Type u} [TopologicalSpace X] [T2Space X]
    (C : Smyth X) (U : Opens X) :
    WithScott.toScott (C, U) ∈ incidenceOpen ↔ carrier C ⊆ U := Iff.rfl

end CHFubini

