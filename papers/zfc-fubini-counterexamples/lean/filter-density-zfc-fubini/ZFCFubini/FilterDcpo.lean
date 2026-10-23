import ZFCFubini.OpenFilter

/-!
The actual pointed-filter poset of manuscript §3.1. The ambient topology in
compactness and accumulation-point conditions is the ordinary metric topology;
filter members are opens in the explicitly specified finer topology.
All implementation in this file is new.
-/

set_option autoImplicit false
open Set Topology TopologicalSpace
open scoped Topology
universe u v

namespace ZFCFubini.FilterDcpo
variable {X : Type u} [MetricSpace X]

structure Point (M : Model X) where
  filter : OpenFilter M.tau
  label : X
  kernel_nonempty : filter.kernel.Nonempty
  kernel_countable : filter.kernel.Countable
  kernel_compact : IsCompact filter.kernel
  label_mem : label ∈ filter.kernel
  derived_subset : ∀ y : X, AccPt y (Filter.principal filter.kernel) → y = label
  ordinary_mem : ∀ U : Set X, IsOpen U → filter.kernel ⊆ U → U ∈ filter

namespace Point
variable {M : Model X}

def kernel (p : Point M) : Set X := p.filter.kernel

@[ext] theorem ext {p q : Point M} (hF : p.filter = q.filter) (hx : p.label = q.label) :
    p = q := by cases p; cases q; cases hF; cases hx; rfl

theorem filter_le_nhds (p : Point M) : p.filter ≤ OpenFilter.nhds M.tau p.label :=
  OpenFilter.le_nhds_iff.mpr p.label_mem

def Below (p q : Point M) : Prop :=
  (p.label = q.label ∧ p.filter ≤ q.filter) ∨
  (q.filter = OpenFilter.nhds M.tau q.label ∧ p.filter ≤ q.filter)

instance : LE (Point M) := ⟨Point.Below⟩

theorem le_iff {p q : Point M} : p ≤ q ↔
    (p.label = q.label ∧ p.filter ≤ q.filter) ∨
    (q.filter = OpenFilter.nhds M.tau q.label ∧ p.filter ≤ q.filter) := Iff.rfl

theorem filter_mono {p q : Point M} (h : p ≤ q) : p.filter ≤ q.filter :=
  h.elim And.right And.right

theorem le_refl (p : Point M) : p ≤ p := Or.inl ⟨rfl, le_rfl⟩

theorem le_trans {p q r : Point M} (hpq : p ≤ q) (hqr : q ≤ r) : p ≤ r := by
  have hqrF := filter_mono hqr
  have hF := (filter_mono hpq).trans (filter_mono hqr)
  rcases hqr with ⟨hqr, _⟩ | ⟨hr, _⟩
  · rcases hpq with ⟨hpq, _⟩ | ⟨hq, hqF⟩
    · exact Or.inl ⟨hpq.trans hqr, hF⟩
    · refine Or.inr ⟨le_antisymm r.filter_le_nhds ?_, hF⟩
      rw [← hqr, ← hq]
      exact hqrF
  · exact Or.inr ⟨hr, hF⟩

theorem le_antisymm {p q : Point M} (hpq : p ≤ q) (hqp : q ≤ p) : p = q := by
  have hF := _root_.le_antisymm (filter_mono hpq) (filter_mono hqp)
  apply Point.ext hF
  rcases hpq with ⟨hx, _⟩ | ⟨hq, _⟩
  · exact hx
  · have hx := p.label_mem
    change p.label ∈ p.filter.kernel at hx
    rw [hF, hq, M.kernel_nhds] at hx
    exact hx

instance : PartialOrder (Point M) where
  le := (· ≤ ·)
  le_refl := Point.le_refl
  le_trans _ _ _ := Point.le_trans
  le_antisymm _ _ := Point.le_antisymm

theorem kernel_antitone {p q : Point M} (h : p ≤ q) : q.kernel ⊆ p.kernel :=
  OpenFilter.kernel_antitone (filter_mono h)

end Point

/-- The source's e(y), not an arbitrarily chosen maximal-point embedding. -/
def e (M : Model X) (y : X) : Point M where
  filter := OpenFilter.nhds M.tau y
  label := y
  kernel_nonempty := by rw [M.kernel_nhds]; exact singleton_nonempty _
  kernel_countable := by rw [M.kernel_nhds]; exact countable_singleton _
  kernel_compact := by rw [M.kernel_nhds]; exact isCompact_singleton
  label_mem := OpenFilter.self_mem_kernel_nhds _
  derived_subset := by
    intro z hz
    have hcl := hz.clusterPt.mem_closure_of_mem _ (Filter.mem_principal_self _)
    simpa only [M.kernel_nhds, closure_singleton, mem_singleton_iff] using hcl
  ordinary_mem U hU hKU := ⟨M.ordinary_le _ hU, hKU (OpenFilter.self_mem_kernel_nhds _)⟩

@[simp] theorem label_e (M : Model X) (y : X) : (e M y).label = y := rfl
@[simp] theorem filter_e (M : Model X) (y : X) : (e M y).filter = OpenFilter.nhds M.tau y := rfl
@[simp] theorem kernel_e (M : Model X) (y : X) : (e M y).kernel = {y} := M.kernel_nhds y

theorem e_injective (M : Model X) : Function.Injective (e M) :=
  fun _ _ h => congrArg Point.label h

theorem le_e_iff {M : Model X} (p : Point M) (y : X) : p ≤ e M y ↔ y ∈ p.kernel := by
  constructor
  · intro h; exact OpenFilter.le_nhds_iff.mp (Point.filter_mono h)
  · intro h; exact Or.inr ⟨rfl, OpenFilter.le_nhds_iff.mpr h⟩

theorem le_e_label {M : Model X} (p : Point M) : p ≤ e M p.label :=
  (le_e_iff p _).mpr p.label_mem

theorem e_le_iff {M : Model X} (y : X) (p : Point M) : e M y ≤ p ↔ p = e M y := by
  constructor
  · intro h
    have hN : OpenFilter.nhds M.tau y ≤ OpenFilter.nhds M.tau p.label :=
      (Point.filter_mono h).trans p.filter_le_nhds
    have hy := (M.nhds_le_iff y p.label).mp hN
    apply Point.ext
    · apply le_antisymm
      · simpa only [filter_e, ← hy] using p.filter_le_nhds
      · exact Point.filter_mono h
    · exact hy.symm
  · rintro rfl; exact le_rfl

theorem maximal_iff {M : Model X} (p : Point M) :
    (∀ q : Point M, p ≤ q → q = p) ↔ ∃ y, p = e M y := by
  constructor
  · intro hp; exact ⟨p.label, (hp _ (le_e_label p)).symm⟩
  · rintro ⟨y, rfl⟩ q hq; exact (e_le_iff _ _).mp hq

theorem common_upper_different_labels {M : Model X} {p q r : Point M}
    (hp : p ≤ r) (hq : q ≤ r) (hne : p.label ≠ q.label) : r = e M r.label := by
  have hr : r.filter = OpenFilter.nhds M.tau r.label := by
    rcases hp with ⟨hpr, _⟩ | ⟨hr, _⟩
    · rcases hq with ⟨hqr, _⟩ | ⟨hr, _⟩
      · exact (hne (hpr.trans hqr.symm)).elim
      · exact hr
    · exact hr
  exact Point.ext hr rfl

theorem directed_different_labels_has_greatest {M : Model X} {A : Set (Point M)}
    (hd : DirectedOn (· ≤ ·) A) {p q : Point M}
    (hp : p ∈ A) (hq : q ∈ A) (hne : p.label ≠ q.label) :
    ∃ r ∈ A, ∀ s ∈ A, s ≤ r := by
  obtain ⟨r, hr, hpr, hqr⟩ := hd p hp q hq
  have hre := common_upper_different_labels hpr hqr hne
  refine ⟨r, hr, ?_⟩
  intro s hs
  obtain ⟨t, ht, hrt, hst⟩ := hd r hr s hs
  have htr : t = r := by
    rw [hre] at hrt
    exact (e_le_iff _ _).mp hrt |>.trans hre.symm
  exact htr ▸ hst

/-- The compact finite-intersection argument in the directed-supremum proof. -/
theorem directed_kernels_eventually_subset {M : Model X} {ι : Type v} [Nonempty ι]
    (p : ι → Point M) (hd : Directed (· ≤ ·) p) {U : Set X}
    (hU : IsOpen U) (hKU : (⋂ i, (p i).kernel) ⊆ U) :
    ∃ i, (p i).kernel ⊆ U := by
  let i₀ : ι := Classical.arbitrary ι
  have he : ((p i₀).kernel \ U) ∩ (⋂ i, (p i).kernel) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    rintro y ⟨⟨_, hyU⟩, hy⟩; exact hyU (hKU hy)
  have hk : Directed (· ⊇ ·) (fun i => (p i).kernel) := by
    intro i j
    obtain ⟨k, hik, hjk⟩ := hd i j
    exact ⟨k, Point.kernel_antitone hik, Point.kernel_antitone hjk⟩
  obtain ⟨i, hi⟩ := ((p i₀).kernel_compact.diff hU).elim_directed_family_closed
    (fun i => (p i).kernel) (fun i => (p i).kernel_compact.isClosed) he hk
  obtain ⟨j, hj₀, hji⟩ := hd i₀ i
  refine ⟨j, ?_⟩
  intro y hy
  by_contra hyU
  have : y ∈ ((p i₀).kernel \ U) ∩ (p i).kernel :=
    ⟨⟨Point.kernel_antitone hj₀ hy, hyU⟩, Point.kernel_antitone hji hy⟩
  exact (Set.eq_empty_iff_forall_notMem.mp hi) y this

/-- Source equation (3.4): the actual union filter and fixed label. -/
noncomputable def sameLabelSup {M : Model X} {ι : Type v} [Nonempty ι]
    (p : ι → Point M) (hd : Directed (· ≤ ·) p) (x : X)
    (hx : ∀ i, (p i).label = x) : Point M := by
  let hF : Directed (· ≤ ·) (fun i => (p i).filter) :=
    fun i j => by obtain ⟨k, hik, hjk⟩ := hd i j; exact ⟨k, Point.filter_mono hik, Point.filter_mono hjk⟩
  let F := OpenFilter.directedUnion (fun i => (p i).filter) hF
  have hK : F.kernel = ⋂ i, (p i).kernel := OpenFilter.kernel_directedUnion _ _
  let i₀ : ι := Classical.arbitrary ι
  have hclosed : IsClosed F.kernel := by
    rw [hK]; exact isClosed_iInter (fun i => (p i).kernel_compact.isClosed)
  have hsub : F.kernel ⊆ (p i₀).kernel := by rw [hK]; exact iInter_subset _ i₀
  have hxK : x ∈ F.kernel := by
    rw [hK]; simp only [mem_iInter]; intro i; exact hx i ▸ (p i).label_mem
  exact {
    filter := F
    label := x
    kernel_nonempty := ⟨x, hxK⟩
    kernel_countable := (p i₀).kernel_countable.mono hsub
    kernel_compact := (p i₀).kernel_compact.of_isClosed_subset hclosed hsub
    label_mem := hxK
    derived_subset := fun y hy => ((p i₀).derived_subset y
      (hy.mono (Filter.principal_mono.mpr hsub))).trans (hx i₀)
    ordinary_mem := fun U hU hKU => by
      have hKU' : (⋂ i, (p i).kernel) ⊆ U := hK ▸ hKU
      obtain ⟨i, hi⟩ := directed_kernels_eventually_subset p hd hU hKU'
      exact ⟨i, (p i).ordinary_mem U hU hi⟩ }

@[simp] theorem label_sameLabelSup {M : Model X} {ι : Type v} [Nonempty ι]
    (p : ι → Point M) (hd : Directed (· ≤ ·) p) (x : X) (hx : ∀ i, (p i).label = x) :
    (sameLabelSup p hd x hx).label = x := rfl

theorem mem_filter_sameLabelSup {M : Model X} {ι : Type v} [Nonempty ι]
    (p : ι → Point M) (hd : Directed (· ≤ ·) p) (x : X) (hx : ∀ i, (p i).label = x)
    (U : Set X) : U ∈ (sameLabelSup p hd x hx).filter ↔ ∃ i, U ∈ (p i).filter := Iff.rfl

theorem kernel_sameLabelSup {M : Model X} {ι : Type v} [Nonempty ι]
    (p : ι → Point M) (hd : Directed (· ≤ ·) p) (x : X) (hx : ∀ i, (p i).label = x) :
    (sameLabelSup p hd x hx).kernel = ⋂ i, (p i).kernel := by
  let hF : Directed (· ≤ ·) (fun i => (p i).filter) :=
    fun i j => by obtain ⟨k, hik, hjk⟩ := hd i j; exact ⟨k, Point.filter_mono hik, Point.filter_mono hjk⟩
  exact OpenFilter.kernel_directedUnion (fun i => (p i).filter) hF

theorem sameLabelSup_isLUB {M : Model X} {ι : Type v} [Nonempty ι]
    (p : ι → Point M) (hd : Directed (· ≤ ·) p) (x : X) (hx : ∀ i, (p i).label = x) :
    IsLUB (Set.range p) (sameLabelSup p hd x hx) := by
  constructor
  · rintro _ ⟨i, rfl⟩
    refine Or.inl ⟨hx i, ?_⟩
    intro U hU
    exact ⟨i, hU⟩
  · intro q hq
    have hF : (sameLabelSup p hd x hx).filter ≤ q.filter := by
      rintro U ⟨i, hi⟩; exact Point.filter_mono (hq (Set.mem_range_self i)) hi
    by_cases hqx : q.label = x
    · exact Or.inl ⟨hqx.symm, hF⟩
    · refine Or.inr ⟨?_, hF⟩
      have hi := hq (Set.mem_range_self (Classical.arbitrary ι))
      rcases hi with ⟨he, _⟩ | ⟨h, _⟩
      · exact (hqx (he.symm.trans (hx _))).elim
      · exact h

theorem point_isDcpo (M : Model X) : IsDcpo (Point M) := by
  intro A hn hd
  classical
  by_cases hdiff : ∃ p ∈ A, ∃ q ∈ A, p.label ≠ q.label
  · obtain ⟨p, hp, q, hq, hpq⟩ := hdiff
    obtain ⟨r, hr, hgr⟩ := directed_different_labels_has_greatest hd hp hq hpq
    exact ⟨r, hgr, fun q hq => hq hr⟩
  · obtain ⟨p₀, hp₀⟩ := hn
    letI : Nonempty A := ⟨⟨p₀, hp₀⟩⟩
    have hval : Directed (· ≤ ·) (fun p : A => p.val) := hd.directed_val
    have hx : ∀ p : A, p.val.label = p₀.label := by
      intro p; by_contra h; exact hdiff ⟨p, p.property, p₀, hp₀, h⟩
    refine ⟨sameLabelSup (fun p : A => p.val) hval p₀.label hx, ?_⟩
    simpa only [Subtype.range_coe_subtype, Set.setOf_mem_eq] using
      sameLabelSup_isLUB (fun p : A => p.val) hval p₀.label hx

/-- The fixed-label branch, with the induced order. -/
abbrev Branch (M : Model X) (x : X) := {p : Point M // p.label = x}

theorem branch_le_iff {M : Model X} {x : X} (p q : Branch M x) :
    p ≤ q ↔ p.val.filter ≤ q.val.filter := by
  constructor
  · exact Point.filter_mono
  · intro h; exact Or.inl ⟨p.property.trans q.property.symm, h⟩

noncomputable def branchSup {M : Model X} {x : X} {A : Set (Branch M x)}
    (hn : A.Nonempty) (hd : DirectedOn (· ≤ ·) A) : Branch M x := by
  letI : Nonempty A := hn.to_subtype
  exact ⟨sameLabelSup (fun p : A => p.val.val)
    (Directed.mono_comp (· ≤ ·) (fun _ _ h => h) hd.directed_val) x
    (fun p => p.val.property), rfl⟩

theorem branchSup_isLUB {M : Model X} {x : X} {A : Set (Branch M x)}
    (hn : A.Nonempty) (hd : DirectedOn (· ≤ ·) A) : IsLUB A (branchSup hn hd) := by
  letI : Nonempty A := hn.to_subtype
  have h := sameLabelSup_isLUB (fun p : A => p.val.val)
    (Directed.mono_comp (· ≤ ·) (fun _ _ h => h) hd.directed_val) x (fun p => p.val.property)
  constructor
  · intro p hp; exact h.1 ⟨⟨p, hp⟩, rfl⟩
  · intro q hq; exact h.2 (by rintro _ ⟨p, rfl⟩; exact hq p.property)

theorem branch_isDcpo (M : Model X) (x : X) : IsDcpo (Branch M x) :=
  fun _ hn hd => ⟨branchSup hn hd, branchSup_isLUB hn hd⟩

theorem branch_inclusion_scottContinuous (M : Model X) (x : X) :
    ScottContinuous (Subtype.val : Branch M x → Point M) := by
  intro A hn hd p hp
  have ep : p = branchSup hn hd := hp.unique (branchSup_isLUB hn hd)
  subst p
  letI : Nonempty A := hn.to_subtype
  have h := sameLabelSup_isLUB (fun p : A => p.val.val)
    (Directed.mono_comp (· ≤ ·) (fun _ _ h => h) hd.directed_val) x (fun p => p.val.property)
  convert h using 1
  ext q
  simp only [Set.mem_image, Set.mem_range]
  constructor
  · rintro ⟨p, hp, rfl⟩; exact ⟨⟨p, hp⟩, rfl⟩
  · rintro ⟨p, rfl⟩; exact ⟨p.val, p.property, rfl⟩

/-- Explicit translation between mathlib's intrinsic Scott topology and the
upper-set / arbitrary-nonempty-directed-supremum definition. -/
theorem scott_isOpen_iff {P : Type v} [PartialOrder P] (S : Set P) :
    IsOpen (WithScott.ofScott ⁻¹' S) ↔ IsUpperSet S ∧ DirSupInacc S := by
  rw [Topology.IsScott.isOpen_iff_isUpperSet_and_dirSupInaccOn (D := Set.univ), dirSupInaccOn_univ]
  rfl

/-- Source gluing lemma, with the full Scott topology on each induced branch. -/
theorem isOpen_gluing_iff (M : Model X) (S : Set (Point M)) :
    IsOpen (WithScott.ofScott ⁻¹' S) ↔
      (∀ x : X, IsOpen {p : WithScott (Branch M x) | (WithScott.ofScott p).val ∈ S}) ∧
      (∀ p ∈ S, ∀ y ∈ p.kernel, e M y ∈ S) := by
  constructor
  · intro hS
    constructor
    · intro x
      exact hS.preimage ((scott_continuous_iff
        (Subtype.val : Branch M x → Point M)).mp (branch_inclusion_scottContinuous M x))
    · intro p hp y hy
      exact ((scott_isOpen_iff S).mp hS).1 ((le_e_iff p y).mpr hy) hp
  · rintro ⟨hB, hK⟩
    apply (scott_isOpen_iff S).mpr
    constructor
    · intro p q hpq hp
      rcases hpq with ⟨hx, hF⟩ | ⟨hq, hF⟩
      · let p' : Branch M p.label := ⟨p, rfl⟩
        let q' : Branch M p.label := ⟨q, hx.symm⟩
        exact ((scott_isOpen_iff {r : Branch M p.label | r.val ∈ S}).mp
          (hB p.label)).1 (show p' ≤ q' from Or.inl ⟨hx, hF⟩) hp
      · have hy : q.label ∈ p.kernel :=
          OpenFilter.le_nhds_iff.mp (hq ▸ hF)
        have heq : q = e M q.label := Point.ext hq rfl
        exact heq ▸ hK p hp q.label hy
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
        let B : Set (Branch M a.label) := {q | q.val ∈ A}
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
        have hpB := branch_inclusion_scottContinuous M a.label hnB hdB
          (branchSup_isLUB hnB hdB)
        rw [heB] at hpB
        have he : p = (branchSup hnB hdB).val := hp.unique hpB
        have hAcc := ((scott_isOpen_iff {r : Branch M a.label | r.val ∈ S}).mp (hB a.label)).2
        have hSupS : (branchSup hnB hdB).val ∈ S := he ▸ hpS
        obtain ⟨q, hqB, hqS⟩ := hAcc hnB hdB (branchSup_isLUB hnB hdB) hSupS
        exact ⟨q.val, hqB, hqS⟩

theorem membership_isOpen (M : Model X) (U : Set X) :
    IsOpen {p : WithScott (Point M) | U ∈ (WithScott.ofScott p).filter} := by
  apply (scott_isOpen_iff {p : Point M | U ∈ p.filter}).mpr
  constructor
  · intro p q hpq hp; exact Point.filter_mono hpq hp
  · intro A hn hd p hp hUp
    classical
    by_cases hdiff : ∃ a ∈ A, ∃ b ∈ A, a.label ≠ b.label
    · obtain ⟨a, ha, b, hb, hab⟩ := hdiff
      obtain ⟨r, hr, hgr⟩ := directed_different_labels_has_greatest hd ha hb hab
      have he : p = r := hp.unique ⟨hgr, fun q hq => hq hr⟩
      exact ⟨r, hr, he ▸ hUp⟩
    · obtain ⟨a, ha⟩ := hn
      letI : Nonempty A := ⟨⟨a, ha⟩⟩
      have hx : ∀ q : A, q.val.label = a.label := by
        intro q; by_contra h; exact hdiff ⟨q, q.property, a, ha, h⟩
      have hp' : IsLUB A (sameLabelSup (fun q : A => q.val) hd.directed_val a.label hx) := by
        simpa only [Subtype.range_coe_subtype, Set.setOf_mem_eq] using
          sameLabelSup_isLUB (fun q : A => q.val) hd.directed_val a.label hx
      have he := hp.unique hp'
      have : ∃ q : A, U ∈ q.val.filter := by
        rw [he] at hUp; exact hUp
      obtain ⟨q, hq⟩ := this
      exact ⟨q, q.property, hq⟩

/-- Source H_U, for every open of the specified finer topology. -/
def H (M : Model X) (U : @Opens X M.tau) : ScottOpens (Point M) :=
  ⟨{p | (U : Set X) ∈ (WithScott.ofScott p).filter}, membership_isOpen M U⟩

@[simp] theorem mem_H (M : Model X) (U : @Opens X M.tau) (p : Point M) :
    WithScott.toScott p ∈ H M U ↔ (U : Set X) ∈ p.filter := Iff.rfl

def H_ordinary (M : Model X) (U : Opens X) : ScottOpens (Point M) :=
  ⟨{p | (U : Set X) ∈ (WithScott.ofScott p).filter}, membership_isOpen M (U : Set X)⟩

theorem mem_H_ordinary_iff_kernel_subset (M : Model X) (U : Opens X) (p : Point M) :
    WithScott.toScott p ∈ H_ordinary M U ↔ p.kernel ⊆ U := by
  change ((U : Set X) ∈ p.filter) ↔ p.kernel ⊆ U
  constructor
  · exact OpenFilter.kernel_subset
  · exact p.ordinary_mem U U.isOpen

theorem H_ordinary_mono (M : Model X) : Monotone (H_ordinary M) := by
  intro U V hUV p hp
  have hp' := (mem_H_ordinary_iff_kernel_subset M U _).mp hp
  exact (mem_H_ordinary_iff_kernel_subset M V _).mpr (hp'.trans hUV)

theorem ordinaryH_scottContinuous (M : Model X) : ScottContinuous (H_ordinary M) := by
  intro A hn hd U hU
  have he : U = sSup A := hU.unique (isLUB_sSup A)
  subst U
  have hEq : H_ordinary M (sSup A) = sSup (H_ordinary M '' A) := by
    apply Opens.ext
    ext p
    change WithScott.toScott (WithScott.ofScott p) ∈ H_ordinary M (sSup A) ↔
      p ∈ sSup (H_ordinary M '' A)
    rw [mem_H_ordinary_iff_kernel_subset]
    simp only [Opens.mem_sSup, Set.mem_image, exists_exists_and_eq_and]
    constructor
    · intro hK
      letI : Nonempty A := hn.to_subtype
      have hc : (WithScott.ofScott p).kernel ⊆ ⋃ V : A, (V.val : Set X) := by
        intro y hy
        have hyU := hK hy
        simp only [Opens.coe_sSup, Set.mem_iUnion] at hyU
        obtain ⟨V, hV, hyV⟩ := hyU
        exact Set.mem_iUnion.mpr ⟨⟨V, hV⟩, hyV⟩
      have hdir : Directed (· ⊆ ·) (fun V : A => (V.val : Set X)) := by
        intro V W
        obtain ⟨Z, hZ, hVZ, hWZ⟩ := hd V.val V.property W.val W.property
        exact ⟨⟨Z, hZ⟩, hVZ, hWZ⟩
      obtain ⟨V, hV⟩ := (WithScott.ofScott p).kernel_compact.elim_directed_cover
        (fun V : A => (V.val : Set X)) (fun V => V.val.isOpen) hc hdir
      exact ⟨V.val, V.property, (mem_H_ordinary_iff_kernel_subset M V.val _).mpr hV⟩
    · rintro ⟨V, hV, hpV⟩
      exact ((mem_H_ordinary_iff_kernel_subset M V _).mp hpV).trans
        (show (V : Set X) ⊆ (sSup A : Opens X) from (le_sSup hV : V ≤ sSup A))
  rw [hEq]
  exact isLUB_sSup _

/-- Trace always means inverse image under the specified e, on all maximal points. -/
def trace {M : Model X} (U : ScottOpens (Point M)) : Set X :=
  {y | WithScott.toScott (e M y) ∈ U}

@[simp] theorem mem_trace {M : Model X} (U : ScottOpens (Point M)) (y : X) :
    y ∈ trace U ↔ WithScott.toScott (e M y) ∈ U := Iff.rfl

@[simp] theorem trace_H (M : Model X) (U : @Opens X M.tau) : trace (H M U) = U := by
  ext y
  change (@IsOpen X M.tau (U : Set X) ∧ y ∈ U) ↔ y ∈ U
  exact and_iff_right (@Opens.isOpen X M.tau U)

theorem kernel_subset_trace {M : Model X} {U : ScottOpens (Point M)} {p : Point M}
    (hp : WithScott.toScott p ∈ U) : p.kernel ⊆ trace U := by
  intro y hy
  exact Topology.IsScott.isUpperSet_of_isOpen (D := Set.univ) U.isOpen ((le_e_iff p y).mpr hy) hp

end ZFCFubini.FilterDcpo
