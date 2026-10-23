import CHFubini.OuterBase
import Mathlib.Topology.Sober
import Mathlib.Topology.Separation.Hausdorff

/-!
Hausdorff-space application of the Smyth-sobriety theorem, proved directly.
No sobriety conclusion is introduced as an assumption or unproved instance.
The upper Vietoris topology remains explicit and separate from Scott until
the already proved topology-comparison bridge is applied at the end.
-/

set_option autoImplicit false

open Set Topology TopologicalSpace Filter

universe u

namespace CHFubini

def upperBox {X : Type u} [TopologicalSpace X] (U : Opens X) :
    Set (WithScott (Smyth X)) :=
  {C | carrier (WithScott.ofScott C) ⊆ U}

@[simp] theorem mem_upperBox {X : Type u} [TopologicalSpace X]
    (U : Opens X) (C : WithScott (Smyth X)) :
    C ∈ upperBox U ↔ carrier (WithScott.ofScott C) ⊆ U := Iff.rfl

/-- A binary compact-neighborhood expansion in a Hausdorff space. This is
the only separation-sensitive ingredient of the irreducible-family proof. -/
theorem compact_inter_open_expansion {X : Type u} [TopologicalSpace X] [T2Space X]
    (C D : Set X) (hC : IsCompact C) (hD : IsCompact D)
    (U : Opens X) (hCDU : C ∩ D ⊆ U) :
    ∃ V W : Opens X, C ⊆ V ∧ D ⊆ W ∧ (V : Set X) ∩ W ⊆ U := by
  have hU : (U : Set X) ∈ 𝓝ˢ (C ∩ D) :=
    mem_nhdsSet_iff_exists.mpr ⟨U, U.isOpen, hCDU, Subset.rfl⟩
  rw [hC.nhdsSet_inter_eq hD] at hU
  obtain ⟨V, hV, W, hW, hVWU⟩ := Filter.mem_inf_iff_superset.mp hU
  obtain ⟨V', hV'open, hCV', hV'V⟩ := mem_nhdsSet_iff_exists.mp hV
  obtain ⟨W', hW'open, hDW', hW'W⟩ := mem_nhdsSet_iff_exists.mp hW
  exact ⟨⟨V', hV'open⟩, ⟨W', hW'open⟩, hCV', hDW',
    fun x hx => hVWU ⟨hV'V hx.1, hW'W hx.2⟩⟩

section UpperVietoris

local instance upperVietorisInst (X : Type u) [TopologicalSpace X] [T2Space X] :
    TopologicalSpace (WithScott (Smyth X)) := upperVietorisTopology X

theorem upperBox_isOpen {X : Type u} [TopologicalSpace X] [T2Space X]
    (U : Opens X) : IsOpen (upperBox U) :=
  isOpen_generateFrom_of_mem ⟨U, rfl⟩

theorem upperBox_basis (X : Type u) [TopologicalSpace X] [T2Space X] :
    IsTopologicalBasis {B : Set (WithScott (Smyth X)) | ∃ U : Opens X, B = upperBox U} := by
  let B : Set (Set (WithScott (Smyth X))) :=
    {B | ∃ U : Opens X, B = upperBox U}
  have hgen : (inferInstance : TopologicalSpace (WithScott (Smyth X))) = generateFrom B := rfl
  have hinter : ∀ ⦃s : Set (WithScott (Smyth X))⦄, s ∈ B →
      ∀ ⦃t : Set (WithScott (Smyth X))⦄, t ∈ B → s ∩ t ∈ B := by
    rintro s ⟨U, rfl⟩ t ⟨V, rfl⟩
    refine ⟨U ⊓ V, ?_⟩
    ext C
    exact subset_inter_iff.symm
  have huniv : univ ∈ B := by
    refine ⟨⊤, ?_⟩
    ext C
    simp only [mem_univ, mem_upperBox, Opens.coe_top, subset_univ]
  have hb := isTopologicalBasis_of_subbasis_of_inter hgen hinter
  simpa only [insert_eq_of_mem huniv] using hb

/-- The specialization order of upper Vietoris is exactly reverse inclusion.
Here membership in closure of a singleton is exposed directly. -/
theorem upperVietoris_mem_closure_singleton_iff {X : Type u}
    [TopologicalSpace X] [T2Space X] (C D : Smyth X) :
    WithScott.toScott D ∈ closure ({WithScott.toScott C} : Set (WithScott (Smyth X))) ↔
      D ≤ C := by
  rw [(upperBox_basis X).mem_closure_iff]
  constructor
  · intro h
    change carrier C ⊆ carrier D
    intro x hxC
    by_contra hxD
    let U : Opens X := ⟨({x} : Set X)ᶜ, isClosed_singleton.isOpen_compl⟩
    have hDU : WithScott.toScott D ∈ upperBox U := by
      intro y hy hyx
      exact hxD ((Set.mem_singleton_iff.mp hyx) ▸ hy)
    obtain ⟨E, hEU, hEC⟩ := h (upperBox U) ⟨U, rfl⟩ hDU
    have hEC' : E = WithScott.toScott C := Set.mem_singleton_iff.mp hEC
    subst E
    exact hEU hxC rfl
  · intro hDC
    rintro B ⟨U, rfl⟩ hDU
    exact ⟨WithScott.toScott C, (show carrier C ⊆ carrier D from hDC).trans hDU,
      Set.mem_singleton _⟩

theorem upperVietoris_t0 (X : Type u) [TopologicalSpace X] [T2Space X] :
    T0Space (WithScott (Smyth X)) := by
  constructor
  intro C D hCD
  have h : C ∈ closure ({D} : Set (WithScott (Smyth X))) ∧
      D ∈ closure ({C} : Set (WithScott (Smyth X))) := inseparable_iff_mem_closure.mp hCD
  exact le_antisymm
    ((upperVietoris_mem_closure_singleton_iff (WithScott.ofScott D) (WithScott.ofScott C)).mp h.1)
    ((upperVietoris_mem_closure_singleton_iff (WithScott.ofScott C) (WithScott.ofScott D)).mp h.2)

private theorem irreducible_compact_intersection_hits {X : Type u}
    [TopologicalSpace X] [T2Space X] {F : Set (WithScott (Smyth X))}
    (hF : IsIrreducible F) {C D : WithScott (Smyth X)} (hC : C ∈ F) (hD : D ∈ F)
    (U : Opens X) (hCDU : carrier (WithScott.ofScott C) ∩ carrier (WithScott.ofScott D) ⊆ U) :
    (F ∩ upperBox U).Nonempty := by
  obtain ⟨V, W, hCV, hDW, hVWU⟩ := compact_inter_open_expansion
    (carrier (WithScott.ofScott C)) (carrier (WithScott.ofScott D))
    (OrderDual.ofDual (WithScott.ofScott C) : NonemptyCompacts X).isCompact
    (OrderDual.ofDual (WithScott.ofScott D) : NonemptyCompacts X).isCompact U hCDU
  obtain ⟨E, hEF, hEV, hEW⟩ := hF.2 (upperBox V) (upperBox W)
    (upperBox_isOpen V) (upperBox_isOpen W) ⟨C, hC, hCV⟩ ⟨D, hD, hDW⟩
  exact ⟨E, hEF, (subset_inter hEV hEW).trans hVWU⟩

theorem upperVietoris_irreducible_closed_directed {X : Type u}
    [TopologicalSpace X] [T2Space X] {F : Set (WithScott (Smyth X))}
    (hF : IsIrreducible F) (hFclosed : IsClosed F) : DirectedOn (· ≤ ·) F := by
  intro C hC D hD
  have hne : (carrier (WithScott.ofScott C) ∩ carrier (WithScott.ofScott D)).Nonempty := by
    by_contra hno
    have hsub : carrier (WithScott.ofScott C) ∩ carrier (WithScott.ofScott D) ⊆
        ((⊥ : Opens X) : Set X) := fun x hx => False.elim (hno ⟨x, hx⟩)
    obtain ⟨E, _, hE⟩ := irreducible_compact_intersection_hits hF hC hD ⊥ hsub
    obtain ⟨x, hx⟩ := (OrderDual.ofDual (WithScott.ofScott E) : NonemptyCompacts X).nonempty
    exact hE hx
  let E : Smyth X := OrderDual.toDual
    ⟨⟨carrier (WithScott.ofScott C) ∩ carrier (WithScott.ofScott D),
      (OrderDual.ofDual (WithScott.ofScott C) : NonemptyCompacts X).isCompact.inter
        (OrderDual.ofDual (WithScott.ofScott D) : NonemptyCompacts X).isCompact⟩, hne⟩
  have hEclosure : WithScott.toScott E ∈ closure F := by
    apply (upperBox_basis X).mem_closure_iff.mpr
    rintro B ⟨U, rfl⟩ hEU
    obtain ⟨K, hKF, hKU⟩ := irreducible_compact_intersection_hits hF hC hD U hEU
    exact ⟨K, hKU, hKF⟩
  have hEF : WithScott.toScott E ∈ F := hFclosed.closure_eq ▸ hEclosure
  exact ⟨WithScott.toScott E, hEF, inter_subset_left, inter_subset_right⟩

/-- The Hausdorff-space case of the cited Smyth sobriety theorem. Every
irreducible closed family is directed, and its compact intersection is its
generic point. -/
theorem upperVietoris_quasiSober (X : Type u) [TopologicalSpace X] [T2Space X] :
    QuasiSober (WithScott (Smyth X)) := by
  constructor
  intro F hF hFclosed
  have hd := upperVietoris_irreducible_closed_directed hF hFclosed
  let K : Smyth X := directedInter (show Set (Smyth X) from F) hF.1 hd
  have hK : IsLUB (show Set (Smyth X) from F) K := directedInter_isLUB F hF.1 hd
  have hKclosure : WithScott.toScott K ∈ closure F := by
    apply (upperBox_basis X).mem_closure_iff.mpr
    rintro B ⟨U, rfl⟩ hKU
    obtain ⟨D, hDF, hDU⟩ := (isLUB_open_test hF.1 hd hK U).mp hKU
    exact ⟨D, hDU, hDF⟩
  have hKF : WithScott.toScott K ∈ F := hFclosed.closure_eq ▸ hKclosure
  refine ⟨WithScott.toScott K, subset_antisymm ?_ ?_⟩
  · exact closure_minimal (singleton_subset_iff.mpr hKF) hFclosed
  · intro D hDF
    exact (upperVietoris_mem_closure_singleton_iff K (WithScott.ofScott D)).mpr (hK.1 hDF)

theorem upperVietoris_sober (X : Type u) [TopologicalSpace X] [T2Space X] :
    @T0Space (WithScott (Smyth X)) (upperVietorisTopology X) ∧
      @QuasiSober (WithScott (Smyth X)) (upperVietorisTopology X) :=
  ⟨upperVietoris_t0 X, upperVietoris_quasiSober X⟩

end UpperVietoris

/-- Transfers the proved upper-Vietoris sobriety across the proved equality
of topologies, never across an assumed instance. -/
theorem scottSmyth_quasiSober_of_outer_bases {X : Type u}
    [TopologicalSpace X] [T2Space X]
    (houter : ∀ C : Smyth X, ∃ N, IsDecreasingOuterBase (carrier C) N) :
    QuasiSober (WithScott (Smyth X)) := by
  change @QuasiSober (WithScott (Smyth X)) (inferInstance : TopologicalSpace _)
  rw [scott_eq_upperVietoris_of_outer_bases houter]
  exact upperVietoris_quasiSober X

theorem scottSmyth_sober_of_countable_compacts {X : Type u}
    [TopologicalSpace X] [T2Space X] [FirstCountableTopology X]
    (hcount : ∀ C : NonemptyCompacts X, (C : Set X).Countable) :
    T0Space (WithScott (Smyth X)) ∧ QuasiSober (WithScott (Smyth X)) := by
  refine ⟨inferInstance, scottSmyth_quasiSober_of_outer_bases ?_⟩
  intro C
  exact compact_countable_decreasing_outer_base (carrier C)
    (OrderDual.ofDual C : NonemptyCompacts X).isCompact (hcount (OrderDual.ofDual C))

end CHFubini

