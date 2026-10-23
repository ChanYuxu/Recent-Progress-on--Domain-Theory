import ZFCFubini.FiniteTruncation
import ZFCFubini.FilterTraceSequence

/-!
The finite-label and per-label-finite-slice constructions C_S and C_(S,F)
from the manuscript's same-trace comparison proof. No comparison outcome is
stored in a hypothesis package. New implementation.
-/

set_option autoImplicit false
open Set Topology TopologicalSpace
universe u v

namespace ZFCFubini.FilterDcpo
variable {X : Type u} [MetricSpace X] {M : Model X}

def branchRestriction (M : Model X) (x : X) (U : ScottOpens (Point M)) :
    ScottOpens (Branch M x) :=
  Opens.comap ⟨fun p => WithScott.toScott (WithScott.ofScott p).val,
    (scott_continuous_iff (Subtype.val : Branch M x → Point M)).mp
      (branch_inclusion_scottContinuous M x)⟩ U

theorem labelSlices_isOpen (Z H : ScottOpens (Point M))
    (htr : trace H ⊆ trace Z) (S : Finset X) :
    IsOpen {p : WithScott (Point M) | p ∈ Z ∨ p ∈ H ∧ (WithScott.ofScott p).label ∈ S} := by
  apply (isOpen_gluing_iff M {p : Point M |
    WithScott.toScott p ∈ Z ∨ WithScott.toScott p ∈ H ∧ p.label ∈ S}).mpr
  constructor
  · intro x
    by_cases hx : x ∈ S
    · convert (branchRestriction M x Z ⊔ branchRestriction M x H).isOpen using 1
      ext p
      change (_ ∨ _ ∧ (WithScott.ofScott p).val.label ∈ S) ↔ (_ ∨ _)
      rw [(WithScott.ofScott p).property]
      simp only [hx, and_true]
      rfl
    · convert (branchRestriction M x Z).isOpen using 1
      ext p
      change (_ ∨ _ ∧ (WithScott.ofScott p).val.label ∈ S) ↔ _
      rw [(WithScott.ofScott p).property]
      simp only [hx, and_false, or_false]
      rfl
  · intro p hp y hy
    apply Or.inl
    rcases hp with hpZ | ⟨hpH, _⟩
    · exact kernel_subset_trace hpZ hy
    · exact htr (kernel_subset_trace hpH hy)

/-- Literal C_S = Z ∪ {p ∈ H : label(p) ∈ S}. -/
def labelSlices (Z H : ScottOpens (Point M)) (htr : trace H ⊆ trace Z) (S : Finset X) :
    ScottOpens (Point M) :=
  ⟨{p | p ∈ Z ∨ p ∈ H ∧ (WithScott.ofScott p).label ∈ S}, labelSlices_isOpen Z H htr S⟩

theorem labelSlices_mono (Z H : ScottOpens (Point M)) (htr : trace H ⊆ trace Z) :
    Monotone (labelSlices Z H htr) := by
  intro S T hST p hp
  exact hp.elim Or.inl (fun h => Or.inr ⟨h.1, hST h.2⟩)

theorem labelSlices_directed (Z H : ScottOpens (Point M)) (htr : trace H ⊆ trace Z) :
    Directed (· ≤ ·) (labelSlices Z H htr) := by
  classical
  intro S T
  exact ⟨S ∪ T, labelSlices_mono Z H htr Finset.subset_union_left,
    labelSlices_mono Z H htr Finset.subset_union_right⟩

theorem labelSlices_cover (Z H : ScottOpens (Point M)) (hZH : Z ≤ H)
    (htr : trace H ⊆ trace Z) : (⨆ S : Finset X, labelSlices Z H htr S) = H := by
  apply le_antisymm
  · apply iSup_le
    intro S p hp
    exact hp.elim (fun h => hZH h) And.left
  · intro p hp
    apply Opens.mem_iSup.mpr
    exact ⟨{(WithScott.ofScott p).label}, Or.inr ⟨hp, by simp⟩⟩

noncomputable def activeLabels (H : ScottOpens (Point M)) (S : Finset X) : Finset X :=
  by classical exact S.filter (fun x => ∃ p : Point M, WithScott.toScott p ∈ H ∧ p.label = x)

theorem labelSlices_active (Z H : ScottOpens (Point M)) (htr : trace H ⊆ trace Z) (S : Finset X) :
    labelSlices Z H htr (activeLabels H S) = labelSlices Z H htr S := by
  classical
  apply Opens.ext
  ext p
  change (_ ∨ _ ∧ _ ∈ activeLabels H S) ↔ (_ ∨ _ ∧ _ ∈ S)
  constructor
  · rintro (hpZ | ⟨hpH, hpS⟩)
    · exact Or.inl hpZ
    · exact Or.inr ⟨hpH, (Finset.mem_filter.mp hpS).1⟩
  · rintro (hpZ | ⟨hpH, hpS⟩)
    · exact Or.inl hpZ
    · exact Or.inr ⟨hpH, Finset.mem_filter.mpr ⟨hpS, WithScott.ofScott p, hpH, rfl⟩⟩

theorem activeLabels_avoid (H : ScottOpens (Point M)) {M0 : Set X}
    (havoid : trace H ⊆ M0ᶜ) (S : Finset X) :
    ∀ x ∈ activeLabels H S, x ∉ M0 := by
  classical
  intro x hx
  obtain ⟨_, p, hpH, hpx⟩ := Finset.mem_filter.mp hx
  exact havoid (hpx ▸ kernel_subset_trace hpH p.label_mem)

theorem finiteSlices_isOpen (Z H : ScottOpens (Point M)) (htr : trace H ⊆ trace Z)
    (S : Finset X) (N : X → Opens X) (hN : ∀ x ∈ S, x ∈ N x) (F : X → Finset X) :
    IsOpen {p : WithScott (Point M) | p ∈ Z ∨ p ∈ H ∧
      (WithScott.ofScott p).label ∈ S ∧ (WithScott.ofScott p).kernel ⊆
        (N (WithScott.ofScott p).label : Set X) ∪ (F (WithScott.ofScott p).label : Set X)} := by
  apply (isOpen_gluing_iff M {p : Point M | WithScott.toScott p ∈ Z ∨
    WithScott.toScott p ∈ H ∧ p.label ∈ S ∧ p.kernel ⊆ (N p.label : Set X) ∪ (F p.label : Set X)}).mpr
  constructor
  · intro x
    by_cases hx : x ∈ S
    · convert (branchRestriction M x Z ⊔
        (branchRestriction M x H ⊓ branchTruncation M x (N x) (hN x hx) (F x))).isOpen using 1
      ext p
      change (_ ∨ _ ∧ _ ∈ S ∧ _) ↔ (_ ∨ _ ∧ _)
      rw [(WithScott.ofScott p).property]
      simp only [hx, true_and]
      rfl
    · convert (branchRestriction M x Z).isOpen using 1
      ext p
      change (_ ∨ _ ∧ _ ∈ S ∧ _) ↔ _
      rw [(WithScott.ofScott p).property]
      simp only [hx, false_and, and_false, or_false]
      rfl
  · intro p hp y hy
    apply Or.inl
    rcases hp with hpZ | ⟨hpH, _, _⟩
    · exact kernel_subset_trace hpZ hy
    · exact htr (kernel_subset_trace hpH hy)

/-- Literal per-label finite tuple construction C_(S,F). Components of F
outside S are unused; restricting F to S gives exactly the source tuple. -/
def finiteSlices (Z H : ScottOpens (Point M)) (htr : trace H ⊆ trace Z)
    (S : Finset X) (N : X → Opens X) (hN : ∀ x ∈ S, x ∈ N x) (F : X → Finset X) :
    ScottOpens (Point M) :=
  ⟨{p | p ∈ Z ∨ p ∈ H ∧ (WithScott.ofScott p).label ∈ S ∧
    (WithScott.ofScott p).kernel ⊆ (N (WithScott.ofScott p).label : Set X) ∪
      (F (WithScott.ofScott p).label : Set X)}, finiteSlices_isOpen Z H htr S N hN F⟩

theorem finiteSlices_mono (Z H : ScottOpens (Point M)) (htr : trace H ⊆ trace Z)
    (S : Finset X) (N : X → Opens X) (hN : ∀ x ∈ S, x ∈ N x) :
    Monotone (finiteSlices Z H htr S N hN) := by
  intro F G hFG p hp
  rcases hp with hp | ⟨hpH, hpS, hpK⟩
  · exact Or.inl hp
  · refine Or.inr ⟨hpH, hpS, ?_⟩
    intro y hy
    rcases hpK hy with hyN | hyF
    · exact Or.inl hyN
    · exact Or.inr (hFG _ hyF)

theorem finiteSlices_directed (Z H : ScottOpens (Point M)) (htr : trace H ⊆ trace Z)
    (S : Finset X) (N : X → Opens X) (hN : ∀ x ∈ S, x ∈ N x) :
    Directed (· ≤ ·) (finiteSlices Z H htr S N hN) := by
  classical
  intro F G
  refine ⟨fun x => F x ∪ G x, finiteSlices_mono Z H htr S N hN ?_,
    finiteSlices_mono Z H htr S N hN ?_⟩
  · intro x; exact Finset.subset_union_left
  · intro x; exact Finset.subset_union_right

theorem finiteSlices_cover (Z H : ScottOpens (Point M)) (htr : trace H ⊆ trace Z)
    (S : Finset X) (N : X → Opens X) (hN : ∀ x ∈ S, x ∈ N x) :
    (⨆ F : X → Finset X, finiteSlices Z H htr S N hN F) = labelSlices Z H htr S := by
  classical
  apply le_antisymm
  · apply iSup_le
    intro F p hp
    exact hp.elim Or.inl (fun h => Or.inr ⟨h.1, h.2.1⟩)
  · intro p hp
    apply Opens.mem_iSup.mpr
    rcases hp with hpZ | ⟨hpH, hpS⟩
    · exact ⟨fun _ => ∅, Or.inl hpZ⟩
    · have hfin := kernel_diff_neighborhood_finite (WithScott.ofScott p)
        (N (WithScott.ofScott p).label).isOpen (hN _ hpS)
      refine ⟨fun _ => hfin.toFinset, Or.inr ⟨hpH, hpS, ?_⟩⟩
      intro y hy
      by_cases hyN : y ∈ N (WithScott.ofScott p).label
      · exact Or.inl hyN
      · exact Or.inr (hfin.mem_toFinset.mpr ⟨hy, hyN⟩)

noncomputable def cleanFiniteTuple (M0 : Set X) (F : X → Finset X) : X → Finset X :=
  by classical exact fun x => (F x).filter (fun y => y ∉ M0)

theorem finiteSlices_clean (Z H : ScottOpens (Point M)) (htr : trace H ⊆ trace Z)
    {M0 : Set X} (havoid : trace H ⊆ M0ᶜ)
    (S : Finset X) (N : X → Opens X) (hN : ∀ x ∈ S, x ∈ N x) (F : X → Finset X) :
    finiteSlices Z H htr S N hN (cleanFiniteTuple M0 F) = finiteSlices Z H htr S N hN F := by
  classical
  apply Opens.ext
  ext p
  constructor
  · rintro (hpZ | ⟨hpH, hpS, hpK⟩)
    · exact Or.inl hpZ
    · refine Or.inr ⟨hpH, hpS, ?_⟩
      intro y hy
      exact (hpK hy).elim Or.inl (fun h => Or.inr (Finset.mem_filter.mp h).1)
  · rintro (hpZ | ⟨hpH, hpS, hpK⟩)
    · exact Or.inl hpZ
    · refine Or.inr ⟨hpH, hpS, ?_⟩
      intro y hy
      exact (hpK hy).elim Or.inl (fun h => Or.inr
        (Finset.mem_filter.mpr ⟨h, havoid (kernel_subset_trace hpH hy)⟩))

theorem finiteSlices_congr_on_S (Z H : ScottOpens (Point M)) (htr : trace H ⊆ trace Z)
    (S : Finset X) (N : X → Opens X) (hN : ∀ x ∈ S, x ∈ N x) {F G : X → Finset X}
    (hFG : ∀ x ∈ S, F x = G x) : finiteSlices Z H htr S N hN F = finiteSlices Z H htr S N hN G := by
  apply Opens.ext
  ext p
  constructor <;> rintro (hpZ | ⟨hpH, hpS, hpK⟩)
  · exact Or.inl hpZ
  · exact Or.inr ⟨hpH, hpS, by simpa only [hFG _ hpS] using hpK⟩
  · exact Or.inl hpZ
  · exact Or.inr ⟨hpH, hpS, by simpa only [hFG _ hpS] using hpK⟩

noncomputable def extendFiniteTuple (S : Finset X) (F : S → Finset X) : X → Finset X :=
  by classical exact fun x => if hx : x ∈ S then F ⟨x, hx⟩ else ∅

theorem extend_restrict_finiteSlices (Z H : ScottOpens (Point M)) (htr : trace H ⊆ trace Z)
    (S : Finset X) (N : X → Opens X) (hN : ∀ x ∈ S, x ∈ N x) (F : X → Finset X) :
    finiteSlices Z H htr S N hN (extendFiniteTuple S (fun x : S => F x.val)) =
      finiteSlices Z H htr S N hN F := by
  classical
  apply finiteSlices_congr_on_S
  intro x hx
  simp only [extendFiniteTuple, dif_pos hx]

theorem sup_right_scottContinuous {P : Type v} [SemilatticeSup P] (B : P) :
    ScottContinuous (fun U : P => U ⊔ B) := by
  simpa only [Function.comp_def] using
    (ScottContinuous.id.prodMk (ScottContinuous.const B)).comp ScottContinuous.sup₂

theorem sup_left_scottContinuous {P : Type v} [SemilatticeSup P] (B : P) :
    ScottContinuous (fun U : P => B ⊔ U) := by
  simpa only [Function.comp_def] using
    ((ScottContinuous.const B).prodMk ScottContinuous.id).comp ScottContinuous.sup₂

theorem background_scottContinuous {P : Type v} [SemilatticeSup P] (B C : P) :
    ScottContinuous (fun U : P => U ⊔ B ⊔ C) := by
  exact (sup_right_scottContinuous B).comp (sup_right_scottContinuous C)

theorem scottOpen_capture_map {P : Type u} {Q : Type v} [PartialOrder P] [PartialOrder Q]
    (f : P → Q) (hf : ScottContinuous f) {S : Set P} (hn : S.Nonempty)
    (hd : DirectedOn (· ≤ ·) S) {p : P} (hp : IsLUB S p) (A : ScottOpens Q)
    (hA : WithScott.toScott (f p) ∈ A) : ∃ s ∈ S, WithScott.toScott (f s) ∈ A := by
  have hAcc := ((scott_isOpen_iff {q : Q | WithScott.toScott q ∈ A}).mp A.isOpen).2
  have hdir : DirectedOn (· ≤ ·) (f '' S) := DirectedOn.mono_comp hf.monotone hd
  obtain ⟨q, hq, hqA⟩ := hAcc (hn.image f) hdir (hf hn hd hp) hA
  obtain ⟨s, hs, rfl⟩ := hq
  exact ⟨s, hs, hqA⟩

def innerOpens (U : Opens X) : Set (Opens X) := {V | closure (V : Set X) ⊆ U}

theorem innerOpens_nonempty (U : Opens X) : (innerOpens U).Nonempty := by
  exact ⟨⊥, by simp only [innerOpens, Set.mem_setOf_eq, Opens.coe_bot, closure_empty, Set.empty_subset]⟩

theorem innerOpens_directed (U : Opens X) : DirectedOn (· ≤ ·) (innerOpens U) := by
  intro V hV W hW
  refine ⟨V ⊔ W, ?_, le_sup_left, le_sup_right⟩
  change closure ((V : Set X) ∪ W) ⊆ U
  rw [closure_union]
  exact Set.union_subset hV hW

theorem innerOpens_isLUB (U : Opens X) : IsLUB (innerOpens U) U := by
  constructor
  · intro V hV; exact subset_closure.trans hV
  · intro W hW x hxU
    obtain ⟨V, hVo, hxV, hVU⟩ := isCompact_singleton.exists_isOpen_closure_subset
      (U.isOpen.mem_nhdsSet.mpr (Set.singleton_subset_iff.mpr hxU))
    exact hW (show (⟨V, hVo⟩ : Opens X) ∈ innerOpens U from hVU) (hxV (Set.mem_singleton _))

theorem noise_event_isOpen {T : Type v} [TopologicalSpace T] (M : Model X)
    (R : T → Opens X) (hR : Continuous (fun t => WithScott.toScott (R t)))
    (B C : ScottOpens (Point M)) (A : ScottOpens (ScottOpens (Point M))) :
    IsOpen {t | WithScott.toScott (H_ordinary M (R t) ⊔ B ⊔ C) ∈ A} := by
  have hf : ScottContinuous (fun U : Opens X => H_ordinary M U ⊔ B ⊔ C) :=
    (ordinaryH_scottContinuous M).comp (background_scottContinuous B C)
  exact A.isOpen.preimage (((scott_continuous_iff _).mp hf).comp hR)

theorem compact_hit_scott_isOpen {K : Set X} (hK : IsCompact K) :
    IsOpen {U : WithScott (Opens X) | K ⊆ ((WithScott.ofScott U : Opens X) : Set X)} := by
  apply (scott_isOpen_iff {U : Opens X | K ⊆ U}).mpr
  constructor
  · intro U V hUV hKU
    exact (show K ⊆ (U : Set X) from hKU).trans
      (show (U : Set X) ⊆ (V : Set X) from hUV)
  · intro A hn hd U hU hKU
    letI : Nonempty A := hn.to_subtype
    have he : U = sSup A := hU.unique (isLUB_sSup A)
    have hcover : K ⊆ ⋃ V : A, (V.val : Set X) := by
      intro x hx
      have hxU := hKU hx
      rw [he] at hxU
      simp only [Opens.coe_sSup, Set.mem_iUnion] at hxU
      obtain ⟨V, hV, hxV⟩ := hxU
      exact Set.mem_iUnion.mpr ⟨⟨V, hV⟩, hxV⟩
    have hdir : Directed (· ⊆ ·) (fun V : A => (V.val : Set X)) := by
      intro V W
      obtain ⟨Z, hZ, hVZ, hWZ⟩ := hd V.val V.property W.val W.property
      exact ⟨⟨Z, hZ⟩, hVZ, hWZ⟩
    obtain ⟨V, hV⟩ := hK.elim_directed_cover _ (fun V => V.val.isOpen) hcover hdir
    exact ⟨V.val, V.property, hV⟩

theorem compact_event_isOpen {T : Type v} [TopologicalSpace T]
    (R : T → Opens X) (hR : Continuous (fun t => WithScott.toScott (R t)))
    {K : Set X} (hK : IsCompact K) : IsOpen {t | K ⊆ (R t : Set X)} :=
  (compact_hit_scott_isOpen hK).preimage hR

/-- The source's same-trace comparison lemma. The finite hitting premise is
the exact conclusion of the preceding source hitting lemma, not the desired
comparison or a rank/existence certificate. Compactness of the ordinary X is
used only to make the finitely many chosen closures compact. -/
theorem same_trace_comparison [CompactSpace X] (M : Model X)
    {T : Type v} [TopologicalSpace T] (R : T → Opens X)
    (hR : Continuous (fun t => WithScott.toScott (R t)))
    (D : Set T) (Nbad M0 : Set X) (hbad : Nbad ⊆ M0)
    (hit : ∀ F : Finset X, (∀ y ∈ F, y ∉ Nbad) →
      ∀ W : Set D, IsOpen W → W.Nonempty → ∃ t ∈ W, (F : Set X) ⊆ R t.val)
    (Z H B : ScottOpens (Point M)) (hZH : Z ≤ H) (htr : trace Z = trace H)
    (havoid : trace H ⊆ M0ᶜ) (A : ScottOpens (ScottOpens (Point M)))
    (W : Set D) (hW : IsOpen W)
    (hstart : ∃ t ∈ W, WithScott.toScott (H_ordinary M (R t.val) ⊔ B ⊔ H) ∈ A) :
    ∃ s ∈ W, WithScott.toScott (H_ordinary M (R s.val) ⊔ B ⊔ Z) ∈ A := by
  classical
  obtain ⟨t, htW, htA⟩ := hstart
  have htr' : trace H ⊆ trace Z := htr.symm.subset
  have hLabelLUB : IsLUB (Set.range (labelSlices Z H htr')) H := by
    simpa only [sSup_range, labelSlices_cover Z H hZH htr'] using
      isLUB_sSup (Set.range (labelSlices Z H htr'))
  obtain ⟨C, hCrange, hCA⟩ := scottOpen_capture_map
    (fun C : ScottOpens (Point M) => (H_ordinary M (R t.val) ⊔ B) ⊔ C)
    (sup_left_scottContinuous _) (Set.range_nonempty (labelSlices Z H htr'))
    (labelSlices_directed Z H htr').directedOn_range hLabelLUB A htA
  obtain ⟨S, rfl⟩ := hCrange
  let S₀ : Finset X := activeLabels H S
  have hCA₀ : WithScott.toScott (H_ordinary M (R t.val) ⊔ B ⊔ labelSlices Z H htr' S₀) ∈ A := by
    simpa only [S₀, labelSlices_active] using hCA
  have hSavoid : ∀ x ∈ S₀, x ∉ Nbad := by
    intro x hx
    exact fun hxN => activeLabels_avoid H havoid S x hx (hbad hxN)
  let W₁ : Set D := W ∩ {u | WithScott.toScott
    (H_ordinary M (R u.val) ⊔ B ⊔ labelSlices Z H htr' S₀) ∈ A}
  have hW₁ : IsOpen W₁ := hW.inter
    ((noise_event_isOpen M R hR B (labelSlices Z H htr' S₀) A).preimage continuous_subtype_val)
  obtain ⟨t₀, ht₀W₁, hS₀hit⟩ := hit S₀ hSavoid W₁ hW₁ ⟨t, htW, hCA₀⟩
  have hNexists : ∀ x : X, ∃ N : Opens X, x ∈ N ∧
      (x ∈ S₀ → closure (N : Set X) ⊆ R t₀.val) := by
    intro x
    by_cases hx : x ∈ S₀
    · obtain ⟨N, hNo, hxN, hNcl⟩ := isCompact_singleton.exists_isOpen_closure_subset
        ((R t₀.val).isOpen.mem_nhdsSet.mpr (Set.singleton_subset_iff.mpr (hS₀hit hx)))
      exact ⟨⟨N, hNo⟩, hxN (Set.mem_singleton x), fun _ => hNcl⟩
    · exact ⟨⊤, Set.mem_univ x, fun h => (hx h).elim⟩
  choose N hNx hNclosure using hNexists
  have hN : ∀ x ∈ S₀, x ∈ N x := fun x _ => hNx x
  have hFiniteLUB : IsLUB (Set.range (finiteSlices Z H htr' S₀ N hN))
      (labelSlices Z H htr' S₀) := by
    simpa only [sSup_range, finiteSlices_cover] using
      isLUB_sSup (Set.range (finiteSlices Z H htr' S₀ N hN))
  obtain ⟨C, hCrange, hCAF⟩ := scottOpen_capture_map
    (fun C : ScottOpens (Point M) => (H_ordinary M (R t₀.val) ⊔ B) ⊔ C)
    (sup_left_scottContinuous _) (Set.range_nonempty (finiteSlices Z H htr' S₀ N hN))
    (finiteSlices_directed Z H htr' S₀ N hN).directedOn_range hFiniteLUB A ht₀W₁.2
  obtain ⟨F, rfl⟩ := hCrange
  let F₀ : X → Finset X := cleanFiniteTuple M0 F
  let C₀ : ScottOpens (Point M) := finiteSlices Z H htr' S₀ N hN F₀
  have hC₀eq : C₀ = finiteSlices Z H htr' S₀ N hN F := finiteSlices_clean Z H htr' havoid S₀ N hN F
  have hCAclean : WithScott.toScott (H_ordinary M (R t₀.val) ⊔ B ⊔ C₀) ∈ A := hC₀eq.symm ▸ hCAF
  have hMap : ScottContinuous (fun V : Opens X => H_ordinary M V ⊔ B ⊔ C₀) :=
    (ordinaryH_scottContinuous M).comp (background_scottContinuous B C₀)
  obtain ⟨V₀, hV₀, hAV₀⟩ := scottOpen_capture_map
    (fun V : Opens X => H_ordinary M V ⊔ B ⊔ C₀) hMap
    (innerOpens_nonempty (R t₀.val)) (innerOpens_directed (R t₀.val))
    (innerOpens_isLUB (R t₀.val)) A hCAclean
  let K₀ : Set X := closure (V₀ : Set X) ∪ ⋃ x ∈ S₀, closure (N x : Set X)
  have hK₀compact : IsCompact K₀ := isClosed_closure.isCompact.union
    (S₀.isCompact_biUnion (fun _ _ => isClosed_closure.isCompact))
  have hK₀subset : K₀ ⊆ R t₀.val := by
    apply Set.union_subset hV₀
    exact Set.iUnion₂_subset (fun x hx => hNclosure x hx)
  let W₀ : Set D := W ∩ {u | K₀ ⊆ R u.val}
  have hW₀ : IsOpen W₀ := hW.inter
    ((compact_event_isOpen R hR hK₀compact).preimage continuous_subtype_val)
  let Fstar : Finset X := S₀.biUnion F₀
  have hFstarAvoid : ∀ y ∈ Fstar, y ∉ Nbad := by
    intro y hy
    obtain ⟨x, hx, hyF⟩ := Finset.mem_biUnion.mp hy
    have hyM0 : y ∉ M0 := (Finset.mem_filter.mp hyF).2
    exact fun hyN => hyM0 (hbad hyN)
  obtain ⟨s, hsW₀, hFstarHit⟩ := hit Fstar hFstarAvoid W₀ hW₀ ⟨t₀, ht₀W₁.1, hK₀subset⟩
  have hV₀s : V₀ ≤ R s.val := fun y hy => hsW₀.2 (Or.inl (subset_closure hy))
  have hNs : ∀ x ∈ S₀, (N x : Set X) ⊆ R s.val := by
    intro x hx y hy
    exact hsW₀.2 (Or.inr (Set.mem_iUnion.mpr ⟨x,
      Set.mem_iUnion.mpr ⟨hx, subset_closure hy⟩⟩))
  have hFs : ∀ x ∈ S₀, (F₀ x : Set X) ⊆ R s.val := by
    intro x hx y hy
    exact hFstarHit (Finset.mem_biUnion.mpr ⟨x, hx, hy⟩)
  have hAbsorb : H_ordinary M V₀ ⊔ B ⊔ C₀ ≤ H_ordinary M (R s.val) ⊔ B ⊔ Z := by
    intro p hp
    rcases hp with (hpV | hpB) | hpC
    · exact Or.inl (Or.inl (H_ordinary_mono M hV₀s hpV))
    · exact Or.inl (Or.inr hpB)
    · rcases hpC with hpZ | ⟨hpH, hpS, hpK⟩
      · exact Or.inr hpZ
      · apply Or.inl ∘ Or.inl
        apply (mem_H_ordinary_iff_kernel_subset M (R s.val) _).mpr
        exact hpK.trans (Set.union_subset (hNs _ hpS) (hFs _ hpS))
  have hUpper := ((scott_isOpen_iff {C : ScottOpens (Point M) | WithScott.toScott C ∈ A}).mp A.isOpen).1
  exact ⟨s, hsW₀.1, hUpper hAbsorb hAV₀⟩

end ZFCFubini.FilterDcpo
