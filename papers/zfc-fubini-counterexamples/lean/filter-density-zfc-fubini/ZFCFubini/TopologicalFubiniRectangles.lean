import ZFCFubini.ValuationIntegral
import ZFCFubini.IntegralTransport
import Mathlib.Topology.Constructions.SumProd

/-! Finite rectangles and lower semicontinuity of valuation section masses.
These are statements about the ordinary topological product, never an
identification with an intrinsic Scott topology on an order product. -/

set_option autoImplicit false
open Set Topology TopologicalSpace MeasureTheory
open scoped ENNReal NNReal Classical
universe u v w
namespace ZFCFubini
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

theorem mem_finset_sup_opens {ι : Type w} (F : Finset ι) (U : ι → Opens X) (x : X) :
    x ∈ F.sup U ↔ ∃ i ∈ F, x ∈ U i := by
  change x ∈ (↑(F.sup U) : Set X) ↔ _
  rw [Opens.coe_finset_sup, Finset.sup_eq_iSup]
  simp

theorem mem_finset_inf_opens {ι : Type w} (F : Finset ι) (U : ι → Opens X) (x : X) :
    x ∈ F.inf U ↔ ∀ i ∈ F, x ∈ U i := by
  change x ∈ (↑(F.inf U) : Set X) ↔ _
  rw [Opens.coe_finset_inf, Finset.inf_eq_iInf]
  simp

def openRectangle (a : Opens X × Opens Y) : Opens (X × Y) :=
  ⟨(a.1 : Set X) ×ˢ (a.2 : Set Y), a.1.isOpen.prod a.2.isOpen⟩

def openSection (W : Opens (X × Y)) (x : X) : Opens Y :=
  ⟨{y | (x, y) ∈ W}, W.isOpen.preimage (continuous_const.prodMk continuous_id)⟩

@[simp] theorem mem_openSection (W : Opens (X × Y)) (x : X) (y : Y) :
    y ∈ openSection W x ↔ (x, y) ∈ W := Iff.rfl

abbrev RectangleIndex (W : Opens (X × Y)) := {a : Opens X × Opens Y // openRectangle a ≤ W}

noncomputable def rectangleFiniteUnion (W : Opens (X × Y)) (F : Finset (RectangleIndex W)) :
    Opens (X × Y) := F.sup (fun a => openRectangle a.val)

theorem rectangleFiniteUnion_le (W : Opens (X × Y)) (F : Finset (RectangleIndex W)) :
    rectangleFiniteUnion W F ≤ W := Finset.sup_le (fun a _ => a.property)

theorem rectangleFiniteUnion_directed (W : Opens (X × Y)) :
    Directed (· ≤ ·) (rectangleFiniteUnion W) := by
  intro F G
  exact ⟨F ∪ G, Finset.sup_mono Finset.subset_union_left,
    Finset.sup_mono Finset.subset_union_right⟩

theorem iSup_rectangleFiniteUnion (W : Opens (X × Y)) :
    (⨆ F : Finset (RectangleIndex W), rectangleFiniteUnion W F) = W := by
  apply le_antisymm (iSup_le (rectangleFiniteUnion_le W))
  rintro ⟨x, y⟩ hxy
  obtain ⟨U, V, hU, hV, hx, hy, hUV⟩ := isOpen_prod_iff.mp W.isOpen x y hxy
  let a : RectangleIndex W := ⟨(⟨U, hU⟩, ⟨V, hV⟩), hUV⟩
  apply (Opens.mem_iSup).mpr
  refine ⟨{a}, ?_⟩
  change (x, y) ∈ ({a} : Finset (RectangleIndex W)).sup (fun a => openRectangle a.val)
  simpa only [Finset.sup_singleton] using (show (x, y) ∈ openRectangle a.val from ⟨hx, hy⟩)

theorem openSection_mono {U V : Opens (X × Y)} (hUV : U ≤ V) (x : X) :
    openSection U x ≤ openSection V x := fun _ hy => hUV hy

theorem openSection_iSup {ι : Type w} (W : ι → Opens (X × Y)) (x : X) :
    openSection (⨆ i, W i) x = ⨆ i, openSection (W i) x := by
  apply Opens.ext
  ext y
  change ((x, y) ∈ (⨆ i, W i)) ↔ y ∈ (⨆ i, openSection (W i) x)
  simp only [Opens.mem_iSup, mem_openSection]

theorem openSection_sup (U V : Opens (X × Y)) (x : X) :
    openSection (U ⊔ V) x = openSection U x ⊔ openSection V x := rfl

theorem openSection_inf (U V : Opens (X × Y)) (x : X) :
    openSection (U ⊓ V) x = openSection U x ⊓ openSection V x := rfl

theorem openSection_rectangleFiniteUnion (W : Opens (X × Y)) (x : X) :
    openSection W x =
      ⨆ F : Finset (RectangleIndex W), openSection (rectangleFiniteUnion W F) x := by
  rw [← openSection_iSup, iSup_rectangleFiniteUnion]

theorem valuation_openSection_isLSC (ν : Valuation Y) (W : Opens (X × Y)) :
    IsLSC (fun x => ν (openSection W x)) := by
  intro r
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  change r < ν (openSection W x) at hx
  have hd : Directed (· ≤ ·)
      (fun F : Finset (RectangleIndex W) => openSection (rectangleFiniteUnion W F) x) := by
    intro F G
    obtain ⟨H, hFH, hGH⟩ := rectangleFiniteUnion_directed W F G
    exact ⟨H, openSection_mono hFH x, openSection_mono hGH x⟩
  rw [openSection_rectangleFiniteUnion, ν.map_iSup _ hd, lt_iSup_iff] at hx
  obtain ⟨F, hF⟩ := hx
  let A := F.filter (fun a => x ∈ a.val.1)
  let V : Opens X := A.inf (fun a => a.val.1)
  have hxV : x ∈ V := by
    simp only [V, A, mem_finset_inf_opens, Finset.mem_filter]
    exact fun a ha => ha.2
  apply Filter.mem_of_superset (V.isOpen.mem_nhds hxV)
  intro x' hx'
  apply hF.trans_le (ν.mono ?_)
  intro y hy
  have hxy : (x, y) ∈ rectangleFiniteUnion W F := hy
  rw [rectangleFiniteUnion, mem_finset_sup_opens] at hxy
  obtain ⟨a, ha, hxa, hya⟩ := hxy
  have haA : a ∈ A := Finset.mem_filter.mpr ⟨ha, hxa⟩
  have hV : V ≤ a.val.1 := Finset.inf_le haA
  have hxa' : x' ∈ a.val.1 := hV hx'
  exact a.property ⟨hxa', hya⟩

end ZFCFubini
