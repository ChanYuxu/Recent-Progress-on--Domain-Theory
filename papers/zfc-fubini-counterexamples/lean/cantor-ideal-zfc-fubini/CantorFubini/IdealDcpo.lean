import CantorFubini.Foundations
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Bases

/-! Literal compact-coordinate/null-ideal model of source §3.
The extra compactness field is redundant; `kernel_compact_of_finite_outside`
proves it from the printed kernel condition. All code in this module is new. -/
set_option autoImplicit false
open Set Topology TopologicalSpace MeasureTheory
universe u v
namespace CantorFubini
variable {X : Type u} [TopologicalSpace X] [T2Space X] [MeasurableSpace X]

structure NullIdeal (m : Measure X) where
  sets : Set (Set X)
  empty_mem : ∅ ∈ sets
  null : ∀ {N}, N ∈ sets → m N = 0
  lower : ∀ {N L}, N ∈ sets → L ⊆ N → L ∈ sets
  union_mem : ∀ {N L}, N ∈ sets → L ∈ sets → N ∪ L ∈ sets

instance {m : Measure X} : Membership (Set X) (NullIdeal m) := ⟨fun I N => N ∈ I.sets⟩

@[ext] theorem NullIdeal.ext {m : Measure X} {I J : NullIdeal m}
    (h : I.sets = J.sets) : I = J := by cases I; cases J; cases h; rfl

def lowerIdeal (m : Measure X) (K : Set X) : NullIdeal m where
  sets := {N | m N = 0 ∧ Disjoint (closure N) K}
  empty_mem := by simp
  null h := h.1
  lower h hsub := ⟨measure_mono_null hsub h.1,
    h.2.mono_left (closure_mono hsub)⟩
  union_mem hN hL := ⟨measure_union_null hN.1 hL.1, by
    rw [closure_union]; exact disjoint_union_left.mpr ⟨hN.2, hL.2⟩⟩

def upperIdeal (m : Measure X) (K : Set X) : NullIdeal m where
  sets := {N | m N = 0 ∧ Disjoint N K}
  empty_mem := by simp
  null h := h.1
  lower h hsub := ⟨measure_mono_null hsub h.1, h.2.mono_left hsub⟩
  union_mem hN hL := ⟨measure_union_null hN.1 hL.1,
    disjoint_union_left.mpr ⟨hN.2, hL.2⟩⟩

theorem kernel_compact_of_finite_outside {K : Set X} {x : X} (hx : x ∈ K)
    (h : ∀ V : Set X, IsOpen V → x ∈ V → (K \ V).Finite) : IsCompact K := by
  rw [isCompact_iff_finite_subcover]
  intro ι U hU hcover
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover hx)
  have hf := h (U i) (hU i) hi
  have hchoose : ∀ y : (K \ U i : Set X), ∃ j, y.val ∈ U j :=
    fun y => mem_iUnion.mp (hcover y.property.1)
  classical
  choose f hfU using hchoose
  let S : Finset ι := insert i (hf.toFinset.attach.image (fun y => f ⟨y.val,
    hf.mem_toFinset.mp y.property⟩))
  refine ⟨S, ?_⟩
  intro y hy
  by_cases hyi : y ∈ U i
  · exact mem_iUnion₂.mpr ⟨i, Finset.mem_insert_self _ _, hyi⟩
  · let z : (K \ U i : Set X) := ⟨y, hy, hyi⟩
    refine mem_iUnion₂.mpr ⟨f z, ?_, hfU z⟩
    apply Finset.mem_insert_of_mem
    apply Finset.mem_image.mpr
    exact ⟨⟨y, hf.mem_toFinset.mpr ⟨hy, hyi⟩⟩, Finset.mem_attach _ _, rfl⟩

structure IdealPoint (m : Measure X) where
  kernel : Set X
  label : X
  label_mem : label ∈ kernel
  finite_outside : ∀ V : Set X, IsOpen V → label ∈ V → (kernel \ V).Finite
  compact : IsCompact kernel
  ideal : NullIdeal m
  lower_bound : (lowerIdeal m kernel).sets ⊆ ideal.sets
  upper_bound : ideal.sets ⊆ (upperIdeal m kernel).sets

namespace IdealPoint
variable {m : Measure X}
@[ext] theorem ext {p q : IdealPoint m} (hK : p.kernel = q.kernel)
    (hx : p.label = q.label) (hI : p.ideal.sets = q.ideal.sets) : p = q := by
  have hi := NullIdeal.ext hI
  cases p; cases q; cases hK; cases hx; cases hi; rfl

def e (m : Measure X) (x : X) : IdealPoint m where
  kernel := {x}
  label := x
  label_mem := mem_singleton x
  finite_outside V _ hx := (finite_singleton x).subset diff_subset
  compact := isCompact_singleton
  ideal := upperIdeal m {x}
  lower_bound N hN := ⟨hN.1, hN.2.mono_left subset_closure⟩
  upper_bound := Subset.rfl

@[simp] theorem kernel_e (x : X) : (e m x).kernel = {x} := rfl
@[simp] theorem label_e (x : X) : (e m x).label = x := rfl

def Below (p q : IdealPoint m) : Prop :=
  (p.label = q.label ∧ q.kernel ⊆ p.kernel ∧ p.ideal.sets ⊆ q.ideal.sets) ∨
  (q = e m q.label ∧ q.label ∈ p.kernel)
instance : LE (IdealPoint m) := ⟨Below⟩

theorem le_iff {p q : IdealPoint m} : p ≤ q ↔
  (p.label = q.label ∧ q.kernel ⊆ p.kernel ∧ p.ideal.sets ⊆ q.ideal.sets) ∨
  (q = e m q.label ∧ q.label ∈ p.kernel) := Iff.rfl

theorem kernel_antitone {p q : IdealPoint m} (h : p ≤ q) : q.kernel ⊆ p.kernel := by
  rcases h with h | ⟨hq, hy⟩
  · exact h.2.1
  · rw [hq]; exact singleton_subset_iff.mpr hy

theorem ideal_mono {p q : IdealPoint m} (h : p ≤ q) : p.ideal.sets ⊆ q.ideal.sets := by
  rcases h with h | ⟨hq, hy⟩
  · exact h.2.2
  · intro N hN
    have hn := p.upper_bound hN
    rw [hq]
    exact ⟨hn.1, disjoint_singleton_right.mpr (fun hyN =>
      Set.disjoint_left.mp hn.2 hyN hy)⟩

theorem e_le {x : X} {p : IdealPoint m} (h : e m x ≤ p) : p = e m x := by
  have hx : p.label = x := (kernel_antitone h) p.label_mem
  have hK : p.kernel = {x} := Subset.antisymm (kernel_antitone h)
    (singleton_subset_iff.mpr (hx ▸ p.label_mem))
  apply ext hK hx
  apply Subset.antisymm
  · simpa only [hK] using p.upper_bound
  · exact ideal_mono h

instance : PartialOrder (IdealPoint m) where
  le_refl p := Or.inl ⟨rfl, Subset.rfl, Subset.rfl⟩
  le_trans p q r hpq hqr := by
    rcases hqr with ⟨hqr, hK, hI⟩ | ⟨hr, hy⟩
    · rcases hpq with ⟨hpq, hK', hI'⟩ | ⟨hq, hy⟩
      · exact Or.inl ⟨hpq.trans hqr, hK.trans hK', hI'.trans hI⟩
      · have he : r = e m q.label := e_le (hq ▸ Or.inl ⟨hqr, hK, hI⟩)
        exact Or.inr ⟨by simpa only [hqr] using he, hqr ▸ hy⟩
    · exact Or.inr ⟨hr, kernel_antitone hpq hy⟩
  le_antisymm p q hpq hqp := by
    have hK := Subset.antisymm (kernel_antitone hqp) (kernel_antitone hpq)
    have hI := Subset.antisymm (ideal_mono hpq) (ideal_mono hqp)
    apply ext hK _ hI
    rcases hpq with h | ⟨hq, _⟩
    · exact h.1
    · have he := e_le (hq ▸ hqp)
      simpa only [label_e] using congrArg (fun p : IdealPoint m => p.label) he

theorem le_e_iff (p : IdealPoint m) (x : X) : p ≤ e m x ↔ x ∈ p.kernel := by
  constructor
  · intro h; exact kernel_antitone h (mem_singleton x)
  · intro h; exact Or.inr ⟨rfl, h⟩

theorem le_e_label (p : IdealPoint m) : p ≤ e m p.label :=
  (le_e_iff _ _).mpr p.label_mem

theorem maximal_iff (p : IdealPoint m) :
    (∀ q, p ≤ q → q = p) ↔ ∃ x, p = e m x := by
  constructor
  · intro h; exact ⟨p.label, (h _ (le_e_label p)).symm⟩
  · rintro ⟨x, rfl⟩ q hq; exact e_le hq

theorem common_upper_different_labels {p q r : IdealPoint m}
    (hp : p ≤ r) (hq : q ≤ r) (hne : p.label ≠ q.label) : r = e m r.label := by
  rcases hp with hp | hp
  · rcases hq with hq | hq
    · exact False.elim (hne (hp.1.trans hq.1.symm))
    · exact hq.1
  · exact hp.1

theorem fixed_label_le_iff {p q : IdealPoint m} (hx : p.label = q.label) :
    p ≤ q ↔ q.kernel ⊆ p.kernel ∧ p.ideal.sets ⊆ q.ideal.sets :=
  ⟨fun h => ⟨kernel_antitone h, ideal_mono h⟩, fun h => Or.inl ⟨hx, h⟩⟩

end IdealPoint

theorem compact_filtered_containment {I : Type v} [Nonempty I]
    (K : I → Set X) (hc : ∀ i, IsCompact (K i))
    (hd : Directed (· ⊇ ·) K) {O : Set X} (ho : IsOpen O)
    (hKO : (⋂ i, K i) ⊆ O) : ∃ i, K i ⊆ O := by
  let i₀ : I := Classical.choice inferInstance
  have hempty : K i₀ ∩ ⋂ i, (K i \ O) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    rintro y ⟨_, hy⟩
    exact (mem_iInter.mp hy i₀).2 (hKO (mem_iInter.mpr
      (fun i => (mem_iInter.mp hy i).1)))
  obtain ⟨i, hi⟩ := (hc i₀).elim_directed_family_closed
    (fun i => K i \ O) (fun i => (hc i).isClosed.inter ho.isClosed_compl) hempty
    (by
      intro i j
      obtain ⟨k, hki, hkj⟩ := hd i j
      exact ⟨k, diff_subset_diff_left hki, diff_subset_diff_left hkj⟩)
  obtain ⟨j, hji, hj₀⟩ := hd i i₀
  refine ⟨j, fun y hy => ?_⟩
  by_contra hyO
  have : y ∈ K i₀ ∩ (K i \ O) := ⟨hj₀ hy, hji hy, hyO⟩
  rw [hi] at this
  exact this

abbrev Branch (m : Measure X) (x : X) := {p : IdealPoint m // p.label = x}

namespace IdealPoint
variable {m : Measure X} {x : X}

noncomputable def branchSup {D : Set (Branch m x)} (hn : D.Nonempty)
    (hd : DirectedOn (· ≤ ·) D) : Branch m x := by
  classical
  let K : Set X := ⋂ p : D, p.val.val.kernel
  let I : NullIdeal m := {
    sets := ⋃ p : D, p.val.val.ideal.sets
    empty_mem := mem_iUnion.mpr ⟨⟨hn.choose, hn.choose_spec⟩, hn.choose.val.ideal.empty_mem⟩
    null := by rintro N hN; obtain ⟨p, hp⟩ := mem_iUnion.mp hN; exact p.val.val.ideal.null hp
    lower := by
      rintro N L hN hLN
      obtain ⟨p, hp⟩ := mem_iUnion.mp hN
      exact mem_iUnion.mpr ⟨p, p.val.val.ideal.lower hp hLN⟩
    union_mem := by
      rintro N L hN hL
      obtain ⟨p, hp⟩ := mem_iUnion.mp hN
      obtain ⟨q, hq⟩ := mem_iUnion.mp hL
      obtain ⟨r, hr, hpr, hqr⟩ := hd p.val p.property q.val q.property
      exact mem_iUnion.mpr ⟨⟨r, hr⟩,
        r.val.ideal.union_mem (ideal_mono hpr hp) (ideal_mono hqr hq)⟩ }
  let p₀ : Branch m x := hn.choose
  have hKsub : K ⊆ p₀.val.kernel := iInter_subset (fun p : D => p.val.val.kernel)
    ⟨p₀, hn.choose_spec⟩
  have hdir : Directed (· ⊇ ·) (fun p : D => p.val.val.kernel) := by
    intro p q
    obtain ⟨r, hr, hpr, hqr⟩ := hd p.val p.property q.val q.property
    exact ⟨⟨r, hr⟩, kernel_antitone hpr, kernel_antitone hqr⟩
  refine ⟨{
    kernel := K
    label := x
    label_mem := mem_iInter.mpr (fun p : D =>
      Eq.mp (congrArg (fun z => z ∈ p.val.val.kernel) p.val.property) p.val.val.label_mem)
    finite_outside := fun V hV hx => (p₀.val.finite_outside V hV
      (p₀.property.symm ▸ hx)).subset (diff_subset_diff_left hKsub)
    compact := p₀.val.compact.of_isClosed_subset
      (isClosed_iInter (fun p : D => p.val.val.compact.isClosed)) hKsub
    ideal := I
    lower_bound := ?_
    upper_bound := ?_ }, rfl⟩
  · intro N hN
    letI : Nonempty D := hn.to_subtype
    obtain ⟨p, hp⟩ := compact_filtered_containment (fun p : D => p.val.val.kernel)
      (fun p => p.val.val.compact) hdir isClosed_closure.isOpen_compl
      (Set.disjoint_left.mp hN.2.symm)
    apply mem_iUnion.mpr
    refine ⟨p, p.val.val.lower_bound ⟨hN.1, ?_⟩⟩
    exact disjoint_left.mpr (fun y hyN hyK => hp hyK hyN)
  · intro N hN
    obtain ⟨p, hp⟩ := mem_iUnion.mp hN
    exact ⟨p.val.val.ideal.null hp, (p.val.val.upper_bound hp).2.mono_right
      (iInter_subset _ p)⟩

@[simp] theorem kernel_branchSup {D : Set (Branch m x)} (hn : D.Nonempty)
    (hd : DirectedOn (· ≤ ·) D) : (branchSup hn hd).val.kernel =
      ⋂ p : D, p.val.val.kernel := rfl

@[simp] theorem ideal_branchSup {D : Set (Branch m x)} (hn : D.Nonempty)
    (hd : DirectedOn (· ≤ ·) D) : (branchSup hn hd).val.ideal.sets =
      ⋃ p : D, p.val.val.ideal.sets := rfl

theorem branchSup_isLUB {D : Set (Branch m x)} (hn : D.Nonempty)
    (hd : DirectedOn (· ≤ ·) D) : IsLUB D (branchSup hn hd) := by
  constructor
  · intro p hp
    apply (fixed_label_le_iff (p.property.trans (branchSup hn hd).property.symm)).mpr
    exact ⟨iInter_subset (fun q : D => q.val.val.kernel) ⟨p, hp⟩,
      subset_iUnion (fun q : D => q.val.val.ideal.sets) ⟨p, hp⟩⟩
  · intro q hq
    apply (fixed_label_le_iff ((branchSup hn hd).property.trans q.property.symm)).mpr
    constructor
    · intro y hy
      exact mem_iInter.mpr (fun p : D => kernel_antitone (hq p.property) hy)
    · rintro N hN
      obtain ⟨p, hp⟩ := mem_iUnion.mp hN
      exact ideal_mono (hq p.property) hp

theorem branch_isDcpo (m : Measure X) (x : X) : IsDcpo (Branch m x) :=
  fun _ hn hd => ⟨branchSup hn hd, branchSup_isLUB hn hd⟩

theorem branchSup_isLUB_ambient {D : Set (Branch m x)} (hn : D.Nonempty)
    (hd : DirectedOn (· ≤ ·) D) : IsLUB (Subtype.val '' D) (branchSup hn hd).val := by
  constructor
  · rintro p ⟨q, hq, rfl⟩; exact (branchSup_isLUB hn hd).1 hq
  · intro q hq
    by_cases hx : q.label = x
    · exact (branchSup_isLUB hn hd).2 (show (⟨q, hx⟩ : Branch m x) ∈ upperBounds D from
        fun p hp => hq (mem_image_of_mem _ hp))
    · have hp₀ := hq (mem_image_of_mem _ hn.choose_spec)
      have he : q = e m q.label := by
        rcases hp₀ with h | h
        · exact False.elim (hx (h.1.symm.trans hn.choose.property))
        · exact h.1
      rw [he]
      apply (le_e_iff _ _).mpr
      exact mem_iInter.mpr (fun p : D => (le_e_iff p.val.val q.label).mp
        (he ▸ hq (mem_image_of_mem _ p.property)))

theorem isDcpo (m : Measure X) : IsDcpo (IdealPoint m) := by
  intro D hn hd
  classical
  by_cases hsame : ∀ p ∈ D, ∀ q ∈ D, p.label = q.label
  · let x := hn.choose.label
    let B : Set (Branch m x) := {p | p.val ∈ D}
    have hB : B.Nonempty := ⟨⟨hn.choose, rfl⟩, hn.choose_spec⟩
    have hBd : DirectedOn (· ≤ ·) B := by
      intro p hp q hq
      obtain ⟨r, hr, hpr, hqr⟩ := hd p.val hp q.val hq
      exact ⟨⟨r, hsame r hr hn.choose hn.choose_spec⟩, hr, hpr, hqr⟩
    refine ⟨(branchSup hB hBd).val, ?_⟩
    have he : Subtype.val '' B = D := by
      ext p
      constructor
      · rintro ⟨q, hq, rfl⟩; exact hq
      · intro hp; exact ⟨⟨p, hsame p hp hn.choose hn.choose_spec⟩, hp, rfl⟩
    rw [← he]
    exact branchSup_isLUB_ambient hB hBd
  · push_neg at hsame
    obtain ⟨p, hp, q, hq, hne⟩ := hsame
    obtain ⟨r, hr, hpr, hqr⟩ := hd p hp q hq
    have he := common_upper_different_labels hpr hqr hne
    have hgreat : ∀ s ∈ D, s ≤ r := by
      intro s hs
      obtain ⟨t, ht, hst, hrt⟩ := hd s hs r hr
      have htr : t = r := (e_le (he ▸ hrt)).trans he.symm
      exact htr ▸ hst
    exact ⟨r, hgreat, fun t ht => ht hr⟩

end IdealPoint
end CantorFubini
