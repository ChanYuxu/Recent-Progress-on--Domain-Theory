import CantorFubini.IdealDcpo
/-! Source §3 gluing and basic Scott opens. Gluing proof adapted from the
separately frozen ZFC_Fubini_Lean/FilterDcpo; the model here is literal ideals. -/
set_option autoImplicit false
open Set Topology TopologicalSpace MeasureTheory
universe u v
namespace CantorFubini
variable {X : Type u} [TopologicalSpace X] [T2Space X] [MeasurableSpace X]
open IdealPoint

theorem branch_inclusion_scottContinuous (m : Measure X) (x : X) :
    ScottContinuous (Subtype.val : Branch m x → IdealPoint m) := by
  intro D hn hd p hp
  have he : p = branchSup hn hd := hp.unique (branchSup_isLUB hn hd)
  subst p
  exact branchSup_isLUB_ambient hn hd

theorem directed_different_labels_has_greatest {m : Measure X} {D : Set (IdealPoint m)}
    (hd : DirectedOn (· ≤ ·) D) {p q : IdealPoint m}
    (hp : p ∈ D) (hq : q ∈ D) (hne : p.label ≠ q.label) :
    ∃ r ∈ D, ∀ s ∈ D, s ≤ r := by
  obtain ⟨r, hr, hpr, hqr⟩ := hd p hp q hq
  have he := common_upper_different_labels hpr hqr hne
  refine ⟨r, hr, fun s hs => ?_⟩
  obtain ⟨t, ht, hst, hrt⟩ := hd s hs r hr
  exact ((IdealPoint.e_le (he ▸ hrt)).trans he.symm) ▸ hst

theorem scott_isOpen_iff {P : Type v} [PartialOrder P] (S : Set P) :
    IsOpen (WithScott.ofScott ⁻¹' S) ↔ IsUpperSet S ∧ DirSupInacc S := by
  rw [Topology.IsScott.isOpen_iff_isUpperSet_and_dirSupInaccOn (D := Set.univ), dirSupInaccOn_univ]
  rfl

/-- Source gluing lemma, with the full Scott topology on each induced branch. -/
theorem isOpen_gluing_iff (m : Measure X) (S : Set (IdealPoint m)) :
    IsOpen (WithScott.ofScott ⁻¹' S) ↔
      (∀ x : X, IsOpen {p : WithScott (Branch m x) | (WithScott.ofScott p).val ∈ S}) ∧
      (∀ p ∈ S, ∀ y ∈ p.kernel, IdealPoint.e m y ∈ S) := by
  constructor
  · intro hS
    constructor
    · intro x
      exact hS.preimage ((scott_continuous_iff
        (Subtype.val : Branch m x → IdealPoint m)).mp (branch_inclusion_scottContinuous m x))
    · intro p hp y hy
      exact ((scott_isOpen_iff S).mp hS).1 ((le_e_iff p y).mpr hy) hp
  · rintro ⟨hB, hmax⟩
    apply (scott_isOpen_iff S).mpr
    constructor
    · intro p q hpq hp
      rcases hpq with ⟨hx, hK, hI⟩ | ⟨hq, hF⟩
      · let p' : Branch m p.label := ⟨p, rfl⟩
        let q' : Branch m p.label := ⟨q, hx.symm⟩
        exact ((scott_isOpen_iff {r : Branch m p.label | r.val ∈ S}).mp
          (hB p.label)).1 (show p' ≤ q' from Or.inl ⟨hx, hK, hI⟩) hp
      · exact hq ▸ hmax p hp q.label hF
    · intro A hn hd p hp hpS
      classical
      by_cases hdiff : ∃ a ∈ A, ∃ b ∈ A, a.label ≠ b.label
      · obtain ⟨a, ha, b, hb, hab⟩ := hdiff
        obtain ⟨r, hr, hgr⟩ := directed_different_labels_has_greatest hd ha hb hab
        have he : p = r := hp.unique ⟨hgr, fun q hq => hq hr⟩
        exact ⟨r, hr, he ▸ hpS⟩
      · obtain ⟨a, ha⟩ := hn
        have hx : ∀ q ∈ A, q.label = a.label := by
          intro q hq; by_contra h; exact hdiff ⟨q, hq, a, ha, h⟩
        let B : Set (Branch m a.label) := {q | q.val ∈ A}
        have hnB : B.Nonempty := ⟨⟨a, rfl⟩, ha⟩
        have hdB : DirectedOn (· ≤ ·) B := by
          intro q hq r hr
          obtain ⟨s, hs, hqs, hrs⟩ := hd q.val hq r.val hr
          exact ⟨⟨s, hx s hs⟩, hs, hqs, hrs⟩
        have heB : Subtype.val '' B = A := by
          ext q
          constructor
          · rintro ⟨r, hr, rfl⟩; exact hr
          · intro hq; exact ⟨⟨q, hx q hq⟩, hq, rfl⟩
        have hpB := branch_inclusion_scottContinuous m a.label hnB hdB
          (branchSup_isLUB hnB hdB)
        rw [heB] at hpB
        have he : p = (branchSup hnB hdB).val := hp.unique hpB
        have hAcc := ((scott_isOpen_iff {r : Branch m a.label | r.val ∈ S}).mp (hB a.label)).2
        have hSupS : (branchSup hnB hdB).val ∈ S := he ▸ hpS
        obtain ⟨q, hqB, hqS⟩ := hAcc hnB hdB (branchSup_isLUB hnB hdB) hSupS
        exact ⟨q.val, hqB, hqS⟩


def trace {m : Measure X} (H : ScottOpens (IdealPoint m)) : Set X :=
  {x | WithScott.toScott (IdealPoint.e m x) ∈ H}

theorem kernel_subset_trace {m : Measure X} {H : ScottOpens (IdealPoint m)}
    {p : IdealPoint m} (hp : WithScott.toScott p ∈ H) : p.kernel ⊆ trace H := by
  intro y hy
  exact (IsScott.isUpperSet_of_isOpen (D := univ) H.isOpen) ((le_e_iff p y).mpr hy) hp

@[simp] theorem trace_sup {m : Measure X} (H Z : ScottOpens (IdealPoint m)) :
    trace (H ⊔ Z) = trace H ∪ trace Z := rfl
@[simp] theorem trace_inf {m : Measure X} (H Z : ScottOpens (IdealPoint m)) :
    trace (H ⊓ Z) = trace H ∩ trace Z := rfl

theorem kernelSubset_branch_open (m : Measure X) (O : Opens X) (x : X) :
    IsOpen {p : WithScott (Branch m x) | (WithScott.ofScott p).val.kernel ⊆ O} := by
  apply (scott_isOpen_iff {p : Branch m x | p.val.kernel ⊆ O}).mpr
  constructor
  · intro p q hpq hp; exact (kernel_antitone hpq).trans hp
  · intro D hn hd p hp hpO
    have he : p = branchSup hn hd := hp.unique (branchSup_isLUB hn hd)
    subst p
    letI : Nonempty D := hn.to_subtype
    have hdir : Directed (· ⊇ ·) (fun q : D => q.val.val.kernel) := by
      intro q r
      obtain ⟨s, hs, hqs, hrs⟩ := hd q.val q.property r.val r.property
      exact ⟨⟨s, hs⟩, kernel_antitone hqs, kernel_antitone hrs⟩
    obtain ⟨q, hq⟩ := compact_filtered_containment (fun q : D => q.val.val.kernel)
      (fun q => q.val.val.compact) hdir O.isOpen hpO
    exact ⟨q.val, q.property, hq⟩

def B (m : Measure X) (O : Opens X) : ScottOpens (IdealPoint m) :=
  ⟨{p | (WithScott.ofScott p).kernel ⊆ O},
    (isOpen_gluing_iff m {p : IdealPoint m | p.kernel ⊆ O}).mpr
    ⟨fun x => kernelSubset_branch_open m O x,
      fun p hp y hy => singleton_subset_iff.mpr (hp hy)⟩⟩

@[simp] theorem mem_B (m : Measure X) (O : Opens X) (p : IdealPoint m) :
    WithScott.toScott p ∈ B m O ↔ p.kernel ⊆ O := Iff.rfl

theorem B_mono (m : Measure X) : Monotone (B m) := by
  intro O V h p hp
  change (WithScott.ofScott p).kernel ⊆ V
  exact hp.trans h

@[simp] theorem trace_B (m : Measure X) (O : Opens X) : trace (B m O) = O := by
  ext x; exact singleton_subset_iff

theorem B_scottContinuous (m : Measure X) : ScottContinuous (B m) := by
  intro D hn hd O hO
  have he : O = sSup D := hO.unique (isLUB_sSup D)
  subst O
  have hEq : B m (sSup D) = sSup (B m '' D) := by
    ext p
    change WithScott.toScott (WithScott.ofScott p) ∈ B m (sSup D) ↔
      p ∈ sSup (B m '' D)
    rw [mem_B]
    simp only [Opens.mem_sSup, Set.mem_image, exists_exists_and_eq_and]
    constructor
    · intro hK
      letI : Nonempty D := hn.to_subtype
      have hc : (WithScott.ofScott p).kernel ⊆ ⋃ V : D, (V.val : Set X) := by
        simpa only [Opens.coe_sSup, iUnion_subtype] using hK
      have hdir : Directed (· ⊆ ·) (fun V : D => (V.val : Set X)) := by
        intro V W
        obtain ⟨Z, hZ, hVZ, hWZ⟩ := hd V.val V.property W.val W.property
        exact ⟨⟨Z, hZ⟩, hVZ, hWZ⟩
      obtain ⟨V, hV⟩ := (WithScott.ofScott p).compact.elim_directed_cover
        (fun V : D => (V.val : Set X)) (fun V => V.val.isOpen) hc hdir
      exact ⟨V.val, V.property, hV⟩
    · rintro ⟨V, hV, hpV⟩
      exact hpV.trans (show (V : Set X) ⊆ (sSup D : Opens X) from
        (show V ≤ (sSup D : Opens X) from le_sSup hV))
  rw [hEq]
  exact isLUB_sSup _

theorem idealMembership_branch_open (m : Measure X) (N : Set X) (x : X) :
    IsOpen {p : WithScott (Branch m x) | N ∈ (WithScott.ofScott p).val.ideal.sets} := by
  apply (scott_isOpen_iff {p : Branch m x | N ∈ p.val.ideal.sets}).mpr
  constructor
  · intro p q hpq hp; exact ideal_mono hpq hp
  · intro D hn hd p hp hpN
    have he : p = branchSup hn hd := hp.unique (branchSup_isLUB hn hd)
    subst p
    obtain ⟨q, hq⟩ := mem_iUnion.mp hpN
    exact ⟨q.val, q.property, hq⟩

def A (m : Measure X) (N : Set X) (hN : m N = 0) : ScottOpens (IdealPoint m) :=
  ⟨{p | N ∈ (WithScott.ofScott p).ideal.sets},
    (isOpen_gluing_iff m {p : IdealPoint m | N ∈ p.ideal.sets}).mpr
    ⟨fun x => idealMembership_branch_open m N x, by
      intro p hp y hy
      exact ⟨hN, disjoint_singleton_right.mpr (fun hyN =>
        disjoint_left.mp (p.upper_bound hp).2 hyN hy)⟩⟩⟩

@[simp] theorem mem_A (m : Measure X) (N : Set X) (hN : m N = 0) (p : IdealPoint m) :
    WithScott.toScott p ∈ A m N hN ↔ N ∈ p.ideal.sets := Iff.rfl

@[simp] theorem trace_A (m : Measure X) (N : Set X) (hN : m N = 0) :
    trace (A m N hN) = Nᶜ := by
  ext x
  change (m N = 0 ∧ Disjoint N {x}) ↔ x ∉ N
  simp [hN]

theorem A_antitone (m : Measure X) {M N : Set X} (hM : m M = 0) (hN : m N = 0)
    (hMN : M ⊆ N) : A m N hN ≤ A m M hM := by
  intro p hp; exact (WithScott.ofScott p).ideal.lower hp hMN

end CantorFubini
