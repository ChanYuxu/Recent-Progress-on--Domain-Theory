import ZFCFubini.FilterDcpo

/-! The literal finite-truncation argument of manuscript §3.3. New implementation. -/

set_option autoImplicit false
open Set Topology TopologicalSpace
universe u

namespace ZFCFubini.FilterDcpo
variable {X : Type u} [MetricSpace X] {M : Model X}

theorem kernel_diff_neighborhood_finite (p : Point M) {N : Set X}
    (hN : IsOpen N) (hxN : p.label ∈ N) : (p.kernel \ N).Finite := by
  by_contra h
  have hinf : (p.kernel \ N).Infinite := h
  obtain ⟨y, hy, hyacc⟩ := hinf.exists_accPt_of_subset_isCompact
    (p.kernel_compact.diff hN) Subset.rfl
  have he : y = p.label := p.derived_subset y
    (hyacc.mono (Filter.principal_mono.mpr Set.diff_subset))
  exact hy.2 (he ▸ hxN)

theorem kernel_branchSup {x : X} {A : Set (Branch M x)}
    (hn : A.Nonempty) (hd : DirectedOn (· ≤ ·) A) :
    (branchSup hn hd).val.kernel = ⋂ p : A, p.val.val.kernel := by
  letI : Nonempty A := hn.to_subtype
  exact kernel_sameLabelSup (fun p : A => p.val.val)
    (Directed.mono_comp (· ≤ ·) (fun _ _ h => h) hd.directed_val) x (fun p => p.val.property)

/-- Source finite-truncation lemma: A is an arbitrary set containing the
ordinary-open neighbourhood N, not required to be open in either topology. -/
theorem kernelSubset_branch_isOpen (M : Model X) (x : X) (N : Opens X)
    (hxN : x ∈ N) (A : Set X) (hNA : (N : Set X) ⊆ A) :
    IsOpen {p : WithScott (Branch M x) | (WithScott.ofScott p).val.kernel ⊆ A} := by
  apply (scott_isOpen_iff {p : Branch M x | p.val.kernel ⊆ A}).mpr
  constructor
  · intro p q hpq hp
    exact (Point.kernel_antitone hpq).trans hp
  · intro B hn hd p hp hpA
    classical
    have he : p = branchSup hn hd := hp.unique (branchSup_isLUB hn hd)
    subst p
    let p₀ : Branch M x := hn.choose
    have hp₀ : p₀ ∈ B := hn.choose_spec
    have hxN₀ : p₀.val.label ∈ N := p₀.property.symm ▸ hxN
    have hfinite : (p₀.val.kernel \ A).Finite :=
      (kernel_diff_neighborhood_finite p₀.val N.isOpen hxN₀).subset
        (fun _ hy => ⟨hy.1, fun hN => hy.2 (hNA hN)⟩)
    have hfinite_bound : ∀ S : Finset X,
        (∀ y ∈ S, y ∉ (branchSup hn hd).val.kernel) →
        ∃ q ∈ B, p₀ ≤ q ∧ ∀ y ∈ S, y ∉ q.val.kernel := by
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
        · exact hr (Point.kernel_antitone hrs hzs)
        · exact hqS z hz (Point.kernel_antitone hqs hzs)
    obtain ⟨q, hq, hpq, hqS⟩ := hfinite_bound hfinite.toFinset (by
      intro y hy
      have hyA := (hfinite.mem_toFinset.mp hy).2
      exact fun hyK => hyA (hpA hyK))
    refine ⟨q, hq, ?_⟩
    intro y hy
    by_contra hyA
    have hyS : y ∈ hfinite.toFinset := hfinite.mem_toFinset.mpr
      ⟨Point.kernel_antitone hpq hy, hyA⟩
    exact hqS y hyS hy

/-- The source's B_(x,N,F), with finite F represented by its exact Finset. -/
def branchTruncation (M : Model X) (x : X) (N : Opens X) (hxN : x ∈ N)
    (F : Finset X) : ScottOpens (Branch M x) :=
  ⟨{p | (WithScott.ofScott p).val.kernel ⊆ (N : Set X) ∪ (F : Set X)},
    kernelSubset_branch_isOpen M x N hxN _ Set.subset_union_left⟩

@[simp] theorem mem_branchTruncation (M : Model X) (x : X) (N : Opens X) (hxN : x ∈ N)
    (F : Finset X) (p : Branch M x) :
    WithScott.toScott p ∈ branchTruncation M x N hxN F ↔
      p.val.kernel ⊆ (N : Set X) ∪ (F : Set X) := Iff.rfl

theorem branchTruncation_mono (M : Model X) (x : X) (N : Opens X) (hxN : x ∈ N) :
    Monotone (branchTruncation M x N hxN) := by
  intro F G hFG p hp y hy
  rcases hp hy with hyN | hyF
  · exact Or.inl hyN
  · exact Or.inr (hFG hyF)

theorem branchTruncation_directed (M : Model X) (x : X) (N : Opens X) (hxN : x ∈ N) :
    Directed (· ≤ ·) (branchTruncation M x N hxN) := by
  classical
  intro F G
  exact ⟨F ∪ G, branchTruncation_mono M x N hxN Finset.subset_union_left,
    branchTruncation_mono M x N hxN Finset.subset_union_right⟩

theorem branchTruncation_cover (M : Model X) (x : X) (N : Opens X) (hxN : x ∈ N) :
    (⨆ F : Finset X, branchTruncation M x N hxN F) = ⊤ := by
  apply top_unique
  intro p _
  have hf := kernel_diff_neighborhood_finite (WithScott.ofScott p).val N.isOpen
    ((WithScott.ofScott p).property.symm ▸ hxN)
  apply Opens.mem_iSup.mpr
  refine ⟨hf.toFinset, ?_⟩
  intro y hy
  by_cases hyN : y ∈ N
  · exact Or.inl hyN
  · exact Or.inr (hf.mem_toFinset.mpr ⟨hy, hyN⟩)

end ZFCFubini.FilterDcpo
