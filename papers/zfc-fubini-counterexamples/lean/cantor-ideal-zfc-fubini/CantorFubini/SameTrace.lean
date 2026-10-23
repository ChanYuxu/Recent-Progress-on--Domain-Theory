import CantorFubini.FiniteRestriction

/-!
Source same-trace comparison for the literal ideal carrier. Label and finite
slice arguments are adapted from ZFC_Fubini_Lean/ZFCFubini/SameTraceComparison.lean,
SHA256 d62f84b39b8a83f845a31c3fa400d0bc5d62e291f02dd39fda5269b190fd096e.
The comparison below follows the current source's clopen neighborhoods and
finite random prefixes rather than the origin's inner-open approximation.
-/

set_option autoImplicit false
open Set Topology TopologicalSpace MeasureTheory
universe u v
namespace CantorFubini
variable {X : Type u} [TopologicalSpace X] [T2Space X] [MeasurableSpace X]
variable {m : Measure X}
open IdealPoint

theorem labelSlices_isOpen (Z H : ScottOpens (IdealPoint m))
    (htr : trace H ⊆ trace Z) (S : Finset X) :
    IsOpen {p : WithScott (IdealPoint m) | p ∈ Z ∨ p ∈ H ∧ (WithScott.ofScott p).label ∈ S} := by
  apply (isOpen_gluing_iff m {p : IdealPoint m |
    WithScott.toScott p ∈ Z ∨ WithScott.toScott p ∈ H ∧ p.label ∈ S}).mpr
  constructor
  · intro x
    by_cases hx : x ∈ S
    · convert (branchRestriction m x Z ⊔ branchRestriction m x H).isOpen using 1
      ext p
      change (_ ∨ _ ∧ (WithScott.ofScott p).val.label ∈ S) ↔ (_ ∨ _)
      rw [(WithScott.ofScott p).property]
      simp only [hx, and_true]
      rfl
    · convert (branchRestriction m x Z).isOpen using 1
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
def labelSlices (Z H : ScottOpens (IdealPoint m)) (htr : trace H ⊆ trace Z) (S : Finset X) :
    ScottOpens (IdealPoint m) :=
  ⟨{p | p ∈ Z ∨ p ∈ H ∧ (WithScott.ofScott p).label ∈ S}, labelSlices_isOpen Z H htr S⟩

theorem labelSlices_mono (Z H : ScottOpens (IdealPoint m)) (htr : trace H ⊆ trace Z) :
    Monotone (labelSlices Z H htr) := by
  intro S T hST p hp
  exact hp.elim Or.inl (fun h => Or.inr ⟨h.1, hST h.2⟩)

theorem labelSlices_directed (Z H : ScottOpens (IdealPoint m)) (htr : trace H ⊆ trace Z) :
    Directed (· ≤ ·) (labelSlices Z H htr) := by
  classical
  intro S T
  exact ⟨S ∪ T, labelSlices_mono Z H htr Finset.subset_union_left,
    labelSlices_mono Z H htr Finset.subset_union_right⟩

theorem labelSlices_cover (Z H : ScottOpens (IdealPoint m)) (hZH : Z ≤ H)
    (htr : trace H ⊆ trace Z) : (⨆ S : Finset X, labelSlices Z H htr S) = H := by
  apply le_antisymm
  · apply iSup_le
    intro S p hp
    exact hp.elim (fun h => hZH h) And.left
  · intro p hp
    apply Opens.mem_iSup.mpr
    exact ⟨{(WithScott.ofScott p).label}, Or.inr ⟨hp, by simp⟩⟩

noncomputable def activeLabels (H : ScottOpens (IdealPoint m)) (S : Finset X) : Finset X :=
  by classical exact S.filter (fun x => ∃ p : IdealPoint m, WithScott.toScott p ∈ H ∧ p.label = x)

theorem labelSlices_active (Z H : ScottOpens (IdealPoint m)) (htr : trace H ⊆ trace Z) (S : Finset X) :
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

theorem activeLabels_avoid (H : ScottOpens (IdealPoint m)) {M0 : Set X}
    (havoid : trace H ⊆ M0ᶜ) (S : Finset X) :
    ∀ x ∈ activeLabels H S, x ∉ M0 := by
  classical
  intro x hx
  obtain ⟨_, p, hpH, hpx⟩ := Finset.mem_filter.mp hx
  exact havoid (hpx ▸ kernel_subset_trace hpH p.label_mem)

theorem finiteSlices_isOpen (Z H : ScottOpens (IdealPoint m)) (htr : trace H ⊆ trace Z)
    (S : Finset X) (N : X → Opens X) (hN : ∀ x ∈ S, x ∈ N x) (F : X → Finset X) :
    IsOpen {p : WithScott (IdealPoint m) | p ∈ Z ∨ p ∈ H ∧
      (WithScott.ofScott p).label ∈ S ∧ (WithScott.ofScott p).kernel ⊆
        (N (WithScott.ofScott p).label : Set X) ∪ (F (WithScott.ofScott p).label : Set X)} := by
  apply (isOpen_gluing_iff m {p : IdealPoint m | WithScott.toScott p ∈ Z ∨
    WithScott.toScott p ∈ H ∧ p.label ∈ S ∧ p.kernel ⊆ (N p.label : Set X) ∪ (F p.label : Set X)}).mpr
  constructor
  · intro x
    by_cases hx : x ∈ S
    · convert (branchRestriction m x Z ⊔
        (branchRestriction m x H ⊓ branchTruncation m x (N x) (hN x hx) (F x))).isOpen using 1
      ext p
      change (_ ∨ _ ∧ _ ∈ S ∧ _) ↔ (_ ∨ _ ∧ _)
      rw [(WithScott.ofScott p).property]
      simp only [hx, true_and]
      rfl
    · convert (branchRestriction m x Z).isOpen using 1
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
def finiteSlices (Z H : ScottOpens (IdealPoint m)) (htr : trace H ⊆ trace Z)
    (S : Finset X) (N : X → Opens X) (hN : ∀ x ∈ S, x ∈ N x) (F : X → Finset X) :
    ScottOpens (IdealPoint m) :=
  ⟨{p | p ∈ Z ∨ p ∈ H ∧ (WithScott.ofScott p).label ∈ S ∧
    (WithScott.ofScott p).kernel ⊆ (N (WithScott.ofScott p).label : Set X) ∪
      (F (WithScott.ofScott p).label : Set X)}, finiteSlices_isOpen Z H htr S N hN F⟩

theorem finiteSlices_mono (Z H : ScottOpens (IdealPoint m)) (htr : trace H ⊆ trace Z)
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

theorem finiteSlices_directed (Z H : ScottOpens (IdealPoint m)) (htr : trace H ⊆ trace Z)
    (S : Finset X) (N : X → Opens X) (hN : ∀ x ∈ S, x ∈ N x) :
    Directed (· ≤ ·) (finiteSlices Z H htr S N hN) := by
  classical
  intro F G
  refine ⟨fun x => F x ∪ G x, finiteSlices_mono Z H htr S N hN ?_,
    finiteSlices_mono Z H htr S N hN ?_⟩
  · intro x; exact Finset.subset_union_left
  · intro x; exact Finset.subset_union_right

theorem finiteSlices_cover (Z H : ScottOpens (IdealPoint m)) (htr : trace H ⊆ trace Z)
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
    · have hfin := (WithScott.ofScott p).finite_outside (N (WithScott.ofScott p).label)
        (N (WithScott.ofScott p).label).isOpen (hN _ hpS)
      refine ⟨fun _ => hfin.toFinset, Or.inr ⟨hpH, hpS, ?_⟩⟩
      intro y hy
      by_cases hyN : y ∈ N (WithScott.ofScott p).label
      · exact Or.inl hyN
      · exact Or.inr (hfin.mem_toFinset.mpr ⟨hy, hyN⟩)

noncomputable def traceFiniteTuple (H : ScottOpens (IdealPoint m))
    (F : X → Finset X) : X → Finset X :=
  by classical exact fun x => (F x).filter (fun y => y ∈ trace H)

theorem finiteSlices_trace_restrict (Z H : ScottOpens (IdealPoint m)) (htr : trace H ⊆ trace Z)
    (S : Finset X) (N : X → Opens X) (hN : ∀ x ∈ S, x ∈ N x) (F : X → Finset X) :
    finiteSlices Z H htr S N hN (traceFiniteTuple H F) = finiteSlices Z H htr S N hN F := by
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
        (Finset.mem_filter.mpr ⟨h, kernel_subset_trace hpH hy⟩))

theorem finiteSlices_congr_on_S (Z H : ScottOpens (IdealPoint m)) (htr : trace H ⊆ trace Z)
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

theorem extend_restrict_finiteSlices (Z H : ScottOpens (IdealPoint m)) (htr : trace H ⊆ trace Z)
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


theorem noise_event_isOpen {T : Type v} [TopologicalSpace T]
    (R : T → Opens X) (hR : Continuous (fun t => WithScott.toScott (R t)))
    (B₀ C : ScottOpens (IdealPoint m)) (A₀ : ScottOpens (ScottOpens (IdealPoint m))) :
    IsOpen {t | WithScott.toScott (B m (R t) ⊔ B₀ ⊔ C) ∈ A₀} := by
  have hf : ScottContinuous (fun U : Opens X => B m U ⊔ B₀ ⊔ C) :=
    (B_scottContinuous m).comp (background_scottContinuous B₀ C)
  exact A₀.isOpen.preimage (((scott_continuous_iff _).mp hf).comp hR)

theorem compact_hit_scott_isOpen {K : Set X} (hK : IsCompact K) :
    IsOpen {O : WithScott (Opens X) | K ⊆ ((WithScott.ofScott O : Opens X) : Set X)} := by
  apply (scott_isOpen_iff {O : Opens X | K ⊆ (O : Set X)}).mpr
  constructor
  · intro O P hOP hKO
    exact (show K ⊆ (O : Set X) from hKO).trans
      (show (O : Set X) ⊆ (P : Set X) from hOP)
  · intro E hn hd O hO hKO
    letI : Nonempty E := hn.to_subtype
    have hcover : K ⊆ ⋃ P : E, (P.val : Set X) := by
      intro x hx
      have hxO := hKO hx
      rw [hO.unique (isLUB_sSup E)] at hxO
      obtain ⟨P, hP, hxP⟩ := Opens.mem_sSup.mp hxO
      exact mem_iUnion.mpr ⟨⟨P, hP⟩, hxP⟩
    obtain ⟨P, hP⟩ := hK.elim_directed_cover
      (fun P : E => (P.val : Set X)) (fun P => P.val.isOpen) hcover (by
        intro P Q
        obtain ⟨R₀, hR₀, hPR, hQR⟩ := hd P.val P.property Q.val Q.property
        exact ⟨⟨R₀, hR₀⟩, hPR, hQR⟩)
    exact ⟨P.val, P.property, hP⟩

theorem compact_event_isOpen {T : Type v} [TopologicalSpace T]
    (R : T → Opens X) (hR : Continuous (fun t => WithScott.toScott (R t)))
    {K : Set X} (hK : IsCompact K) : IsOpen {t | K ⊆ (R t : Set X)} :=
  (compact_hit_scott_isOpen hK).preimage hR

/-- Source Lemma `lem:same-trace`. Every finite set used for added component
points is filtered into the actual maximal trace. The final approximation is
one of the specified finite prefixes, rather than an arbitrary smaller open. -/
theorem same_trace_comparison [CompactSpace X]
    {T : Type v} [TopologicalSpace T]
    (R : T → Opens X) (hR : Continuous (fun t => WithScott.toScott (R t)))
    (stagePrefix : T → ℕ → Opens X) (hprefix : ∀ t, Monotone (stagePrefix t))
    (hprefixLUB : ∀ t, IsLUB (range (stagePrefix t)) (R t))
    (hprefixCompact : ∀ t k, IsCompact (stagePrefix t k : Set X))
    (hclopen : ∀ (x : X) (U : Opens X), x ∈ U →
      ∃ V : Opens X, IsClopen (V : Set X) ∧ x ∈ V ∧ V ≤ U)
    {D : Set T} {Nbad M0 : Set X} (hbad : Nbad ⊆ M0)
    (hit : ∀ F : Finset X, (∀ x ∈ F, x ∉ Nbad) →
      ∀ W : Set D, IsOpen W → W.Nonempty → ∃ t ∈ W, (F : Set X) ⊆ R t.val)
    (Z H B₀ : ScottOpens (IdealPoint m)) (hZH : Z ≤ H) (htr : trace Z = trace H)
    (havoid : trace H ⊆ M0ᶜ) (A₀ : ScottOpens (ScottOpens (IdealPoint m)))
    (W : Set D) (hW : IsOpen W)
    (hstart : ∃ t ∈ W, WithScott.toScott (B m (R t.val) ⊔ B₀ ⊔ H) ∈ A₀) :
    ∃ s ∈ W, WithScott.toScott (B m (R s.val) ⊔ B₀ ⊔ Z) ∈ A₀ := by
  classical
  obtain ⟨t, htW, htA⟩ := hstart
  have htr' : trace H ⊆ trace Z := htr.symm.subset
  have hLabelLUB : IsLUB (range (labelSlices Z H htr')) H := by
    simpa only [sSup_range, labelSlices_cover Z H hZH htr'] using
      isLUB_sSup (range (labelSlices Z H htr'))
  obtain ⟨C, hCrange, hCA⟩ := scottOpen_capture_map
    (fun C : ScottOpens (IdealPoint m) => (B m (R t.val) ⊔ B₀) ⊔ C)
    (sup_left_scottContinuous _) (range_nonempty (labelSlices Z H htr'))
    (labelSlices_directed Z H htr').directedOn_range hLabelLUB A₀ htA
  obtain ⟨S, rfl⟩ := hCrange
  let S₀ : Finset X := activeLabels H S
  have hCA₀ : WithScott.toScott (B m (R t.val) ⊔ B₀ ⊔ labelSlices Z H htr' S₀) ∈ A₀ := by
    simpa only [S₀, labelSlices_active] using hCA
  have hSavoid : ∀ x ∈ S₀, x ∉ Nbad := by
    intro x hx
    exact fun hxN => activeLabels_avoid H havoid S x hx (hbad hxN)
  let W₁ : Set D := W ∩ {u | WithScott.toScott
    (B m (R u.val) ⊔ B₀ ⊔ labelSlices Z H htr' S₀) ∈ A₀}
  have hW₁ : IsOpen W₁ := hW.inter
    ((noise_event_isOpen R hR B₀ (labelSlices Z H htr' S₀) A₀).preimage continuous_subtype_val)
  obtain ⟨t₀, ht₀W₁, hS₀hit⟩ := hit S₀ hSavoid W₁ hW₁ ⟨t, htW, hCA₀⟩
  have hVexists : ∀ x : X, ∃ V : Opens X, IsClopen (V : Set X) ∧ x ∈ V ∧
      (x ∈ S₀ → V ≤ R t₀.val) := by
    intro x
    by_cases hx : x ∈ S₀
    · obtain ⟨V, hVc, hxV, hVU⟩ := hclopen x (R t₀.val) (hS₀hit hx)
      exact ⟨V, hVc, hxV, fun _ => hVU⟩
    · exact ⟨⊤, isClopen_univ, mem_univ x, fun h => (hx h).elim⟩
  choose V hVclopen hxV hVU using hVexists
  have hV : ∀ x ∈ S₀, x ∈ V x := fun x _ => hxV x
  have hFiniteLUB : IsLUB (range (finiteSlices Z H htr' S₀ V hV))
      (labelSlices Z H htr' S₀) := by
    simpa only [sSup_range, finiteSlices_cover] using
      isLUB_sSup (range (finiteSlices Z H htr' S₀ V hV))
  obtain ⟨C, hCrange, hCAF⟩ := scottOpen_capture_map
    (fun C : ScottOpens (IdealPoint m) => (B m (R t₀.val) ⊔ B₀) ⊔ C)
    (sup_left_scottContinuous _) (range_nonempty (finiteSlices Z H htr' S₀ V hV))
    (finiteSlices_directed Z H htr' S₀ V hV).directedOn_range hFiniteLUB A₀ ht₀W₁.2
  obtain ⟨F, rfl⟩ := hCrange
  let F₀ : X → Finset X := traceFiniteTuple H F
  let C₀ : ScottOpens (IdealPoint m) := finiteSlices Z H htr' S₀ V hV F₀
  have hC₀eq : C₀ = finiteSlices Z H htr' S₀ V hV F :=
    finiteSlices_trace_restrict Z H htr' S₀ V hV F
  have hCAtrace : WithScott.toScott (B m (R t₀.val) ⊔ B₀ ⊔ C₀) ∈ A₀ :=
    hC₀eq.symm ▸ hCAF
  have hMap : ScottContinuous (fun O : Opens X => B m O ⊔ B₀ ⊔ C₀) :=
    (B_scottContinuous m).comp (background_scottContinuous B₀ C₀)
  obtain ⟨O, hOrange, hAO⟩ := scottOpen_capture_map _ hMap
    (range_nonempty (stagePrefix t₀.val))
    (hprefix t₀.val).directed_le.directedOn_range (hprefixLUB t₀.val) A₀ hCAtrace
  obtain ⟨k, rfl⟩ := hOrange
  let K₀ : Set X := (stagePrefix t₀.val k : Set X) ∪ ⋃ x ∈ S₀, (V x : Set X)
  have hK₀compact : IsCompact K₀ := (hprefixCompact _ _).union
    (S₀.isCompact_biUnion (fun x _ => (hVclopen x).isClosed.isCompact))
  have hK₀subset : K₀ ⊆ R t₀.val :=
    union_subset ((hprefixLUB t₀.val).1 (mem_range_self k))
      (iUnion₂_subset (fun x hx => hVU x hx))
  have hcompact_event := compact_event_isOpen R hR hK₀compact
  let W₀ : Set D := W ∩ {u | K₀ ⊆ R u.val}
  have hW₀ : IsOpen W₀ := hW.inter (hcompact_event.preimage continuous_subtype_val)
  let Fstar : Finset X := S₀.biUnion F₀
  have hFstarAvoid : ∀ y ∈ Fstar, y ∉ Nbad := by
    intro y hy
    obtain ⟨x, hx, hyF⟩ := Finset.mem_biUnion.mp hy
    have hyR : y ∈ trace H := (Finset.mem_filter.mp hyF).2
    exact fun hyN => havoid hyR (hbad hyN)
  obtain ⟨s, hsW₀, hFstarHit⟩ := hit Fstar hFstarAvoid W₀ hW₀ ⟨t₀, ht₀W₁.1, hK₀subset⟩
  have hprefixs : stagePrefix t₀.val k ≤ R s.val := fun y hy => hsW₀.2 (Or.inl hy)
  have hVs : ∀ x ∈ S₀, (V x : Set X) ⊆ R s.val := by
    intro x hx y hy
    exact hsW₀.2 (Or.inr (mem_iUnion₂.mpr ⟨x, hx, hy⟩))
  have hFs : ∀ x ∈ S₀, (F₀ x : Set X) ⊆ R s.val := by
    intro x hx y hy
    exact hFstarHit (Finset.mem_biUnion.mpr ⟨x, hx, hy⟩)
  have hAbsorb : B m (stagePrefix t₀.val k) ⊔ B₀ ⊔ C₀ ≤ B m (R s.val) ⊔ B₀ ⊔ Z := by
    intro p hp
    rcases hp with (hpV | hpB) | hpC
    · exact Or.inl (Or.inl ((B_scottContinuous m).monotone hprefixs hpV))
    · exact Or.inl (Or.inr hpB)
    · rcases hpC with hpZ | ⟨hpH, hpS, hpK⟩
      · exact Or.inr hpZ
      · exact Or.inl (Or.inl (hpK.trans (union_subset (hVs _ hpS) (hFs _ hpS))))
  have hUpper := ((scott_isOpen_iff {C : ScottOpens (IdealPoint m) |
    WithScott.toScott C ∈ A₀}).mp A₀.isOpen).1
  exact ⟨s, hsW₀.1, hUpper hAbsorb hAO⟩

end CantorFubini
