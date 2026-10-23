import CantorFubini.ScottBasics

/-!
Source Lemma `lem:finite-restriction`, for the literal null-ideal model.
The finite avoidance induction is adapted from
ZFC_Fubini_Lean/ZFCFubini/FiniteTruncation.lean, SHA256
a70035aaa1a5855d65d34eac0cb6f57c406bb9aae72ce1c5a74fa05bc3ab540e.
That origin's filter carrier is not reused. The restricted trace cover is new.
-/

set_option autoImplicit false
open Set Topology TopologicalSpace MeasureTheory
universe u
namespace CantorFubini
variable {X : Type u} [TopologicalSpace X] [T2Space X] [MeasurableSpace X]
open IdealPoint

/-- Finite restriction is Scott-open in the component for every target
containing an ordinary neighborhood of the component label. -/
theorem kernelSubset_branch_isOpen (m : Measure X) (x : X) (V : Opens X)
    (hxV : x ∈ V) (A : Set X) (hVA : (V : Set X) ⊆ A) :
    IsOpen {p : WithScott (Branch m x) | (WithScott.ofScott p).val.kernel ⊆ A} := by
  apply (scott_isOpen_iff {p : Branch m x | p.val.kernel ⊆ A}).mpr
  constructor
  · intro p q hpq hp
    exact (IdealPoint.kernel_antitone hpq).trans hp
  · intro D hn hd p hp hpA
    classical
    have he : p = branchSup hn hd := hp.unique (branchSup_isLUB hn hd)
    subst p
    let p₀ : Branch m x := hn.choose
    have hp₀ : p₀ ∈ D := hn.choose_spec
    have hfinite : (p₀.val.kernel \ A).Finite :=
      (p₀.val.finite_outside V V.isOpen (p₀.property.symm ▸ hxV)).subset
        (fun _ hy => ⟨hy.1, fun hV => hy.2 (hVA hV)⟩)
    have hfinite_bound : ∀ S : Finset X,
        (∀ y ∈ S, y ∉ (branchSup hn hd).val.kernel) →
        ∃ q ∈ D, p₀ ≤ q ∧ ∀ y ∈ S, y ∉ q.val.kernel := by
      intro S
      induction S using Finset.induction_on with
      | empty => exact fun _ => ⟨p₀, hp₀, le_rfl, by simp⟩
      | @insert y S hyS ih =>
        intro hS
        obtain ⟨q, hq, hpq, hqS⟩ := ih (fun z hz => hS z (Finset.mem_insert_of_mem hz))
        have hyK := hS y (Finset.mem_insert_self _ _)
        rw [kernel_branchSup hn hd] at hyK
        simp only [Set.mem_iInter, not_forall] at hyK
        obtain ⟨r, hr⟩ := hyK
        obtain ⟨s, hs, hqs, hrs⟩ := hd q hq r.val r.property
        refine ⟨s, hs, hpq.trans hqs, ?_⟩
        intro z hz hzs
        rcases Finset.mem_insert.mp hz with rfl | hz
        · exact hr (IdealPoint.kernel_antitone hrs hzs)
        · exact hqS z hz (IdealPoint.kernel_antitone hqs hzs)
    obtain ⟨q, hq, hpq, hqS⟩ := hfinite_bound hfinite.toFinset (by
      intro y hy
      exact fun hyK => (hfinite.mem_toFinset.mp hy).2 (hpA hyK))
    refine ⟨q, hq, ?_⟩
    intro y hy
    by_contra hyA
    exact hqS y (hfinite.mem_toFinset.mpr ⟨IdealPoint.kernel_antitone hpq hy, hyA⟩) hy

/-- The printed set `T_{x,V,F}`. -/
def branchTruncation (m : Measure X) (x : X) (V : Opens X) (hxV : x ∈ V)
    (F : Finset X) : ScottOpens (Branch m x) :=
  ⟨{p | (WithScott.ofScott p).val.kernel ⊆ (V : Set X) ∪ (F : Set X)},
    kernelSubset_branch_isOpen m x V hxV _ Set.subset_union_left⟩

@[simp] theorem mem_branchTruncation (m : Measure X) (x : X) (V : Opens X)
    (hxV : x ∈ V) (F : Finset X) (p : Branch m x) :
    WithScott.toScott p ∈ branchTruncation m x V hxV F ↔
      p.val.kernel ⊆ (V : Set X) ∪ (F : Set X) := Iff.rfl

theorem branchTruncation_mono (m : Measure X) (x : X) (V : Opens X) (hxV : x ∈ V) :
    Monotone (branchTruncation m x V hxV) := by
  intro F G hFG p hp y hy
  exact (hp hy).elim Or.inl (fun h => Or.inr (hFG h))

theorem branchTruncation_directed (m : Measure X) (x : X) (V : Opens X)
    (hxV : x ∈ V) : Directed (· ≤ ·) (branchTruncation m x V hxV) := by
  classical
  intro F G
  exact ⟨F ∪ G, branchTruncation_mono m x V hxV Finset.subset_union_left,
    branchTruncation_mono m x V hxV Finset.subset_union_right⟩

theorem branchTruncation_cover (m : Measure X) (x : X) (V : Opens X) (hxV : x ∈ V) :
    (⨆ F : Finset X, branchTruncation m x V hxV F) = ⊤ := by
  apply top_unique
  intro p _
  have hf := (WithScott.ofScott p).val.finite_outside V V.isOpen
    ((WithScott.ofScott p).property.symm ▸ hxV)
  apply Opens.mem_iSup.mpr
  refine ⟨hf.toFinset, ?_⟩
  intro y hy
  by_cases hyV : y ∈ V
  · exact Or.inl hyV
  · exact Or.inr (hf.mem_toFinset.mpr ⟨hy, hyV⟩)

def branchRestriction (m : Measure X) (x : X) (H : ScottOpens (IdealPoint m)) :
    ScottOpens (Branch m x) :=
  Opens.comap ⟨fun p => WithScott.toScott (WithScott.ofScott p).val,
    (scott_continuous_iff (Subtype.val : Branch m x → IdealPoint m)).mp
      (branch_inclusion_scottContinuous m x)⟩ H

/-- The exact trace-restricted finite index collection in equation
`eq:restricted-cover`. -/
abbrev TraceFinset {m : Measure X} (H : ScottOpens (IdealPoint m)) :=
  {F : Finset X // (F : Set X) ⊆ trace H}

theorem restricted_branch_cover (m : Measure X) (x : X) (V : Opens X)
    (hxV : x ∈ V) (H : ScottOpens (IdealPoint m)) :
    branchRestriction m x H =
      ⨆ F : TraceFinset H,
        branchRestriction m x H ⊓ branchTruncation m x V hxV F.val := by
  classical
  apply le_antisymm
  · intro p hp
    have hf := (WithScott.ofScott p).val.finite_outside V V.isOpen
      ((WithScott.ofScott p).property.symm ▸ hxV)
    have hFtrace : (hf.toFinset : Set X) ⊆ trace H := by
      intro y hy
      exact kernel_subset_trace hp (hf.mem_toFinset.mp hy).1
    apply Opens.mem_iSup.mpr
    refine ⟨⟨hf.toFinset, hFtrace⟩, hp, ?_⟩
    intro y hy
    by_cases hyV : y ∈ V
    · exact Or.inl hyV
    · exact Or.inr (hf.mem_toFinset.mpr ⟨hy, hyV⟩)
  · apply iSup_le
    intro F
    exact inf_le_left

/-- Public source-facing wrapper for all assertions of
Lemma `lem:finite-restriction`. -/
theorem finite_restriction (m : Measure X) (x : X) (V : Opens X) (hxV : x ∈ V) :
    (∀ F : Finset X, IsOpen (branchTruncation m x V hxV F : Set (WithScott (Branch m x)))) ∧
    Directed (· ≤ ·) (branchTruncation m x V hxV) ∧
    (⨆ F : Finset X, branchTruncation m x V hxV F) = ⊤ ∧
    (∀ H : ScottOpens (IdealPoint m), branchRestriction m x H =
      ⨆ F : TraceFinset H,
        branchRestriction m x H ⊓ branchTruncation m x V hxV F.val) :=
  ⟨fun F => (branchTruncation m x V hxV F).isOpen,
    branchTruncation_directed m x V hxV, branchTruncation_cover m x V hxV,
    fun H => restricted_branch_cover m x V hxV H⟩

end CantorFubini
