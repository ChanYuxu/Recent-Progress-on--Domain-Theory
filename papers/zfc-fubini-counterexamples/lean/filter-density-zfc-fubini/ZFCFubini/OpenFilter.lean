import ZFCFubini.Foundations
import Mathlib.Topology.MetricSpace.Thickening

/-!
Proper filters on the specified finer topology (manuscript §3).
This is a family of actual open subsets, not an ideal completion or a filter
on a replacement carrier. All implementation in this file is new.
-/

set_option autoImplicit false
open Set Topology TopologicalSpace
universe u v

namespace ZFCFubini

/-- A nonempty, proper family of opens, upward closed among opens and closed
under binary (hence finite) intersections. -/
structure OpenFilter {X : Type u} (tau : TopologicalSpace X) where
  sets : Set (Set X)
  isOpen : ∀ U ∈ sets, @IsOpen X tau U
  univ_mem : Set.univ ∈ sets
  empty_not_mem : ∅ ∉ sets
  upward : ∀ {U V}, U ∈ sets → @IsOpen X tau V → U ⊆ V → V ∈ sets
  inter_mem : ∀ {U V}, U ∈ sets → V ∈ sets → U ∩ V ∈ sets

namespace OpenFilter
variable {X : Type u} {tau : TopologicalSpace X}

instance : Membership (Set X) (OpenFilter tau) := ⟨fun F U => U ∈ F.sets⟩

@[ext] theorem ext {F G : OpenFilter tau} (h : F.sets = G.sets) : F = G := by
  cases F; cases G; congr

instance : PartialOrder (OpenFilter tau) where
  le F G := F.sets ⊆ G.sets
  le_refl _ := Subset.rfl
  le_trans _ _ _ := Subset.trans
  le_antisymm F G hFG hGF := ext (Subset.antisymm hFG hGF)

/-- The literal intersection of all filter members. -/
def kernel (F : OpenFilter tau) : Set X := {x | ∀ U ∈ F, x ∈ U}

theorem kernel_subset {F : OpenFilter tau} {U : Set X} (hU : U ∈ F) :
    F.kernel ⊆ U := fun _ hx => hx U hU

theorem kernel_antitone {F G : OpenFilter tau} (h : F ≤ G) : G.kernel ⊆ F.kernel :=
  fun _ hx U hU => hx U (h hU)

/-- The open-neighbourhood filter used in the source, on the finer topology. -/
def nhds (tau : TopologicalSpace X) (x : X) : OpenFilter tau where
  sets := {U | @IsOpen X tau U ∧ x ∈ U}
  isOpen _ h := h.1
  univ_mem := ⟨@isOpen_univ X tau, Set.mem_univ _⟩
  empty_not_mem h := h.2
  upward hU hV hUV := ⟨hV, hUV hU.2⟩
  inter_mem hU hV := ⟨@IsOpen.inter X tau _ _ hU.1 hV.1, hU.2, hV.2⟩

@[simp] theorem mem_nhds {x : X} {U : Set X} :
    U ∈ nhds tau x ↔ @IsOpen X tau U ∧ x ∈ U := Iff.rfl

theorem le_nhds_iff {F : OpenFilter tau} {x : X} : F ≤ nhds tau x ↔ x ∈ F.kernel := by
  constructor
  · intro h U hU; exact (h hU).2
  · intro h U hU; exact ⟨F.isOpen U hU, h U hU⟩

theorem self_mem_kernel_nhds (x : X) : x ∈ (nhds tau x).kernel :=
  fun _ h => h.2

/-- Intersection of a nonempty family of proper filters. -/
def intersection {ι : Type v} [Nonempty ι] (F : ι → OpenFilter tau) : OpenFilter tau where
  sets := {U | ∀ i, U ∈ F i}
  isOpen U h := (F (Classical.arbitrary ι)).isOpen U (h _)
  univ_mem _ := (F _).univ_mem
  empty_not_mem h := (F (Classical.arbitrary ι)).empty_not_mem (h _)
  upward hU hV hUV i := (F i).upward (hU i) hV hUV
  inter_mem hU hV i := (F i).inter_mem (hU i) (hV i)

@[simp] theorem mem_intersection {ι : Type v} [Nonempty ι]
    (F : ι → OpenFilter tau) (U : Set X) :
    U ∈ intersection F ↔ ∀ i, U ∈ F i := Iff.rfl

/-- The source's co-singleton argument. This theorem is not a stored kernel
identity: the reverse implication uses upward closure within the T1 topology. -/
theorem not_mem_kernel_iff {F : OpenFilter tau} {x : X}
    (h : @IsOpen X tau ({x}ᶜ)) :
    x ∉ F.kernel ↔ {x}ᶜ ∈ F := by
  constructor
  · intro hx
    simp only [kernel, Set.mem_setOf_eq, not_forall] at hx
    obtain ⟨U, hU, hxU⟩ := hx
    apply F.upward hU h
    intro y hy hyx
    exact hxU ((Set.mem_singleton_iff.mp hyx) ▸ hy)
  · intro hU hx; exact (kernel_subset hU hx) (by simp)

theorem kernel_intersection {ι : Type v} [Nonempty ι]
    (F : ι → OpenFilter tau) (hT1 : ∀ x : X, @IsOpen X tau ({x}ᶜ)) :
    (intersection F).kernel = ⋃ i, (F i).kernel := by
  ext x
  classical
  rw [← not_iff_not]
  simp only [not_mem_kernel_iff (hT1 x), mem_intersection, mem_iUnion, not_exists]

/-- Directed union of the actual open-filter families. -/
def directedUnion {ι : Type v} [Nonempty ι] (F : ι → OpenFilter tau)
    (hF : Directed (· ≤ ·) F) : OpenFilter tau where
  sets := {U | ∃ i, U ∈ F i}
  isOpen _ h := by obtain ⟨i, hi⟩ := h; exact (F i).isOpen _ hi
  univ_mem := ⟨Classical.arbitrary ι, (F _).univ_mem⟩
  empty_not_mem h := by obtain ⟨i, hi⟩ := h; exact (F i).empty_not_mem hi
  upward hU hV hUV := by obtain ⟨i, hi⟩ := hU; exact ⟨i, (F i).upward hi hV hUV⟩
  inter_mem hU hV := by
    obtain ⟨i, hi⟩ := hU
    obtain ⟨j, hj⟩ := hV
    obtain ⟨k, hik, hjk⟩ := hF i j
    exact ⟨k, (F k).inter_mem (hik hi) (hjk hj)⟩

@[simp] theorem mem_directedUnion {ι : Type v} [Nonempty ι]
    (F : ι → OpenFilter tau) (hF : Directed (· ≤ ·) F) (U : Set X) :
    U ∈ directedUnion F hF ↔ ∃ i, U ∈ F i := Iff.rfl

theorem kernel_directedUnion {ι : Type v} [Nonempty ι]
    (F : ι → OpenFilter tau) (hF : Directed (· ≤ ·) F) :
    (directedUnion F hF).kernel = ⋂ i, (F i).kernel := by
  ext x
  simp only [kernel, Set.mem_setOf_eq, mem_iInter, mem_directedUnion]
  constructor
  · intro h i U hU; exact h U ⟨i, hU⟩
  · rintro h U ⟨i, hi⟩; exact h i U hi

/-- A countable cofinal base is an equivalent, explicit form of countable
generation. Decreasing and metric refinements are proved separately.
No countability is imposed on arbitrary filters. -/
def CountablyBased (F : OpenFilter tau) : Prop :=
  ∃ a : ℕ → Set X, (∀ n, a n ∈ F) ∧ ∀ U ∈ F, ∃ n, a n ⊆ U

/-- Members of the filter generated by B are exactly the finer-open supersets
of finite intersections of generators. -/
def GeneratedMember (B : Set (Set X)) (U : Set X) : Prop :=
  @IsOpen X tau U ∧ ∃ S : Finset (Set X),
    (∀ V ∈ S, V ∈ B) ∧ (⋂ V ∈ S, V) ⊆ U

noncomputable def generated (B : Set (Set X))
    (hB : ∀ U ∈ B, @IsOpen X tau U) (x : X) (hx : ∀ U ∈ B, x ∈ U) :
    OpenFilter tau where
  sets := GeneratedMember B
  isOpen _ h := h.1
  univ_mem := ⟨@isOpen_univ X tau, ∅, by simp⟩
  empty_not_mem := by
    rintro ⟨_, S, hS, he⟩
    have hxs : x ∈ ⋂ V ∈ S, V := by
      simp only [mem_iInter]; exact fun V hV => hx V (hS V hV)
    exact he hxs
  upward hU hV hUV := by
    obtain ⟨_, S, hS, hSU⟩ := hU
    exact ⟨hV, S, hS, hSU.trans hUV⟩
  inter_mem := by
    rintro U V ⟨hU, S, hS, hSU⟩ ⟨hV, T, hT, hTV⟩
    refine ⟨@IsOpen.inter X tau U V hU hV, S ∪ T, ?_, ?_⟩
    · intro W hW
      rcases Finset.mem_union.mp hW with hW | hW
      · exact hS W hW
      · exact hT W hW
    · intro y hy
      simp only [mem_iInter] at hy
      exact ⟨hSU (by simp only [mem_iInter]; exact fun W hW => hy W (Finset.mem_union_left _ hW)),
        hTV (by simp only [mem_iInter]; exact fun W hW => hy W (Finset.mem_union_right _ hW))⟩

@[simp] theorem mem_generated (B : Set (Set X))
    (hB : ∀ U ∈ B, @IsOpen X tau U) (x : X) (hx : ∀ U ∈ B, x ∈ U) (U : Set X) :
    U ∈ generated B hB x hx ↔ GeneratedMember (tau := tau) B U := Iff.rfl

theorem generator_mem (B : Set (Set X))
    (hB : ∀ U ∈ B, @IsOpen X tau U) (x : X) (hx : ∀ U ∈ B, x ∈ U)
    {U : Set X} (hU : U ∈ B) : U ∈ generated B hB x hx := by
  classical
  exact ⟨hB U hU, {U}, by simpa⟩

theorem generated_le {B : Set (Set X)}
    {hB : ∀ U ∈ B, @IsOpen X tau U} {x : X} {hx : ∀ U ∈ B, x ∈ U}
    {F : OpenFilter tau} (hBF : ∀ U ∈ B, U ∈ F) : generated B hB x hx ≤ F := by
  classical
  rintro U ⟨hU, S, hS, hSU⟩
  have hi : ∀ S : Finset (Set X), (∀ V ∈ S, V ∈ B) → (⋂ V ∈ S, V) ∈ F := by
    intro S hS
    induction S using Finset.induction_on with
    | empty => simpa using F.univ_mem
    | @insert V S hVS ih =>
      rw [Finset.set_biInter_insert]
      exact F.inter_mem (hBF V (hS V (Finset.mem_insert_self _ _)))
        (ih (fun W hW => hS W (Finset.mem_insert_of_mem hW)))
  exact F.upward (hi S hS) hU hSU

theorem finset_inter_mem (F : OpenFilter tau) (S : Finset (Set X))
    (hS : ∀ U ∈ S, U ∈ F) : (⋂ U ∈ S, U) ∈ F := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using F.univ_mem
  | @insert U S hUS ih =>
    rw [Finset.set_biInter_insert]
    exact F.inter_mem (hS U (Finset.mem_insert_self _ _))
      (ih (fun V hV => hS V (Finset.mem_insert_of_mem hV)))

/-- The source's unrestricted finite-intersection-property generator interface.
The common-point helper above is a special case, not a hidden strengthened premise. -/
noncomputable def generatedFIP (B : Set (Set X))
    (hB : ∀ U ∈ B, @IsOpen X tau U)
    (hFIP : ∀ S : Finset (Set X), (∀ U ∈ S, U ∈ B) → (⋂ U ∈ S, U).Nonempty) :
    OpenFilter tau where
  sets := GeneratedMember B
  isOpen _ h := h.1
  univ_mem := ⟨@isOpen_univ X tau, ∅, by simp⟩
  empty_not_mem := by
    rintro ⟨_, S, hS, he⟩
    obtain ⟨x, hx⟩ := hFIP S hS
    exact he hx
  upward hU hV hUV := by
    obtain ⟨_, S, hS, hSU⟩ := hU
    exact ⟨hV, S, hS, hSU.trans hUV⟩
  inter_mem := by
    rintro U V ⟨hU, S, hS, hSU⟩ ⟨hV, T, hT, hTV⟩
    refine ⟨@IsOpen.inter X tau U V hU hV, S ∪ T, ?_, ?_⟩
    · intro W hW
      exact (Finset.mem_union.mp hW).elim (hS W) (hT W)
    · intro y hy
      simp only [mem_iInter] at hy
      exact ⟨hSU (by simp only [mem_iInter]; exact fun W hW => hy W (Finset.mem_union_left _ hW)),
        hTV (by simp only [mem_iInter]; exact fun W hW => hy W (Finset.mem_union_right _ hW))⟩

theorem generatedFIP_eq_generated (B : Set (Set X))
    (hB : ∀ U ∈ B, @IsOpen X tau U)
    (hFIP : ∀ S : Finset (Set X), (∀ U ∈ S, U ∈ B) → (⋂ U ∈ S, U).Nonempty)
    (x : X) (hx : ∀ U ∈ B, x ∈ U) :
    generatedFIP B hB hFIP = generated B hB x hx := ext rfl

theorem countablyBased_generated (B : Set (Set X))
    (hB : ∀ U ∈ B, @IsOpen X tau U) (x : X) (hx : ∀ U ∈ B, x ∈ U)
    (hc : B.Countable) : (generated B hB x hx).CountablyBased := by
  classical
  let C : Set (Set X) := Set.sInter '' {S : Set (Set X) | S.Finite ∧ S ⊆ B}
  have hCcount : C.Countable := (Set.countable_setOf_finite_subset hc).image Set.sInter
  have hCnonempty : C.Nonempty := ⟨univ, ∅, ⟨Set.finite_empty, Set.empty_subset _⟩, by simp⟩
  obtain ⟨a, ha⟩ := hCcount.exists_eq_range hCnonempty
  refine ⟨a, ?_, ?_⟩
  · intro n
    have hn : a n ∈ C := ha.symm ▸ Set.mem_range_self n
    obtain ⟨S, ⟨hSf, hSB⟩, hSa⟩ := hn
    rw [← hSa]
    have hEq : (⋂ U ∈ hSf.toFinset, U) = ⋂₀ S := by ext y; simp
    refine ⟨hSf.isOpen_sInter (fun U hU => hB U (hSB hU)), hSf.toFinset, ?_, ?_⟩
    · intro U hU; exact hSB (hSf.mem_toFinset.mp hU)
    · exact hEq.subset
  · rintro U ⟨_, S, hS, hSU⟩
    have hCS : (⋂₀ (S : Set (Set X))) ∈ C :=
      ⟨(S : Set (Set X)), ⟨S.finite_toSet, hS⟩, rfl⟩
    rw [ha] at hCS
    obtain ⟨n, hn⟩ := hCS
    refine ⟨n, ?_⟩
    rw [hn]
    convert hSU using 1
    ext y; simp

end OpenFilter

namespace FilterDcpo

/-- Ordinary metric topology remains the ambient topology. `tau` is an
explicit finer topology, instantiated later by the manuscript's density topology. -/
abbrev ordinaryTopology (X : Type u) [MetricSpace X] : TopologicalSpace X := inferInstance

structure Model (X : Type u) [MetricSpace X] where
  tau : TopologicalSpace X
  ordinary_le : ∀ U : Set X, @IsOpen X (ordinaryTopology X) U → @IsOpen X tau U

namespace Model
variable {X : Type u} [MetricSpace X] (M : Model X)

theorem coSingleton_open (x : X) : @IsOpen X M.tau ({x}ᶜ) :=
  M.ordinary_le _ isClosed_singleton.isOpen_compl

theorem kernel_nhds (x : X) : (OpenFilter.nhds M.tau x).kernel = {x} := by
  ext y
  constructor
  · intro hy
    by_contra hne
    have hyx : y ≠ x := by simpa using hne
    have hU : ({y}ᶜ : Set X) ∈ OpenFilter.nhds M.tau x :=
      ⟨M.coSingleton_open y, by simpa using hyx.symm⟩
    exact (OpenFilter.kernel_subset hU hy) (by simp)
  · intro hy
    subst y
    exact OpenFilter.self_mem_kernel_nhds x

theorem nhds_le_iff (x y : X) : OpenFilter.nhds M.tau x ≤ OpenFilter.nhds M.tau y ↔ x = y := by
  rw [OpenFilter.le_nhds_iff, M.kernel_nhds, mem_singleton_iff, eq_comm]

end Model
end FilterDcpo
end ZFCFubini
