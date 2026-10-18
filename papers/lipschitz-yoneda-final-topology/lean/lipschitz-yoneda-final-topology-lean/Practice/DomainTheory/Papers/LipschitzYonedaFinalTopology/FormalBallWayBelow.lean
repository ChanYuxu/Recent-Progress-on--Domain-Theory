import Practice.DomainTheory.Papers.LipschitzYonedaFinalTopology.FormalBallFunctor
import Practice.DomainTheory.Papers.LipschitzYonedaFinalTopology.CompletionCenterPoints

/-!
# Way-below ideals in a continuous formal-ball poset

This file formalizes Lemmas 7.2--7.5 of Goubault-Larrecq--Ng that are
needed for the section map into the rounded-ideal completion.  In
particular:

* way-below implies the strict formal-ball relation;
* the way-below relation is invariant under a common finite radius shift
  in a standard continuous formal-ball poset;
* `↓↓q` is a rounded ideal, and has aperture zero when `q` has radius zero;
* `q ↦ ↓↓q` is Scott-continuous.
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

open Set Function Filter Topology
open scoped NNReal ENNReal Topology

noncomputable section

universe u

namespace LipschitzYonedaFinalTopology
namespace QuasiMetric

variable {X : Type u} (d : QuasiMetric X)

namespace FormalBallWayBelow

/-- Way-below implies the underlying formal-ball order. -/
theorem le {p q : d.FormalBall} (hpq : d.FormalBallWayBelow p q) :
    p ≤ q := by
  let S : Set d.FormalBall := {q}
  have hne : S.Nonempty := Set.singleton_nonempty q
  have hdir : DirectedOn (· ≤ ·) S := by
    intro a ha b hb
    have haq : a = q := by simpa [S] using ha
    have hbq : b = q := by simpa [S] using hb
    subst a
    subst b
    exact ⟨q, by simp [S], le_rfl, le_rfl⟩
  have hsup : IsLUB S q := by
    simpa [S] using (isLUB_singleton : IsLUB {q} q)
  rcases hpq hne hdir hsup le_rfl with ⟨a, ha, hpa⟩
  have haq : a = q := by simpa [S] using ha
  simpa [haq] using hpa

/-- Lowering the first argument preserves way-below. -/
theorem mono_left {p p' q : d.FormalBall} (hpp' : p ≤ p')
    (hp'q : d.FormalBallWayBelow p' q) :
    d.FormalBallWayBelow p q := by
  intro S hne hdir a hsup hqa
  rcases hp'q hne hdir hsup hqa with ⟨s, hsS, hp's⟩
  exact ⟨s, hsS, hpp'.trans hp's⟩

/-- Raising the second argument preserves way-below. -/
theorem mono_right {p q q' : d.FormalBall}
    (hpq : d.FormalBallWayBelow p q) (hqq' : q ≤ q') :
    d.FormalBallWayBelow p q' := by
  intro S hne hdir a hsup hq'a
  exact hpq hne hdir hsup (hqq'.trans hq'a)

theorem trans {p q r : d.FormalBall}
    (hpq : d.FormalBallWayBelow p q)
    (hqr : d.FormalBallWayBelow q r) :
    d.FormalBallWayBelow p r :=
  mono_left d (le d hpq) hqr

/-- Interpolation in the custom source-facing way-below relation. -/
theorem exists_interpolant
    (hcontinuous : d.FormalBallPosetContinuous)
    {p q : d.FormalBall} (hpq : d.FormalBallWayBelow p q) :
    ∃ r : d.FormalBall,
      d.FormalBallWayBelow p r ∧ d.FormalBallWayBelow r q := by
  let W : d.FormalBall → Set d.FormalBall := fun a ↦
    {b | d.FormalBallWayBelow b a}
  let U : Set d.FormalBall := {b | ∃ a ∈ W q, b ∈ W a}
  have hW (a : d.FormalBall) :
      (W a).Nonempty ∧ DirectedOn (· ≤ ·) (W a) ∧ IsLUB (W a) a := by
    simpa [W] using hcontinuous a
  have hUne : U.Nonempty := by
    rcases (hW q).1 with ⟨a, ha⟩
    rcases (hW a).1 with ⟨b, hb⟩
    exact ⟨b, a, ha, hb⟩
  have hUdir : DirectedOn (· ≤ ·) U := by
    intro a ha b hb
    rcases ha with ⟨a', ha'q, haa'⟩
    rcases hb with ⟨b', hb'q, hbb'⟩
    rcases (hW q).2.1 a' ha'q b' hb'q with
      ⟨c', hc'q, ha'c', hb'c'⟩
    have hac' : d.FormalBallWayBelow a c' :=
      mono_right d haa' ha'c'
    have hbc' : d.FormalBallWayBelow b c' :=
      mono_right d hbb' hb'c'
    rcases (hW c').2.1 a hac' b hbc' with
      ⟨c, hcc', hac, hbc⟩
    exact ⟨c, ⟨c', hc'q, hcc'⟩, hac, hbc⟩
  have hUsup : IsLUB U q := by
    constructor
    · intro b hb
      rcases hb with ⟨a, haq, hba⟩
      exact (le d hba).trans (le d haq)
    · intro z hz
      apply (hW q).2.2.2
      intro a haq
      apply (hW a).2.2.2
      intro b hba
      exact hz ⟨a, haq, hba⟩
  rcases hpq hUne hUdir hUsup le_rfl with ⟨b, hbU, hpb⟩
  rcases hbU with ⟨r, hrq, hbr⟩
  exact ⟨r, mono_left d hpb hbr, hrq⟩

end FormalBallWayBelow

namespace FormalBall

/-- Strictness is preserved when the lower formal ball is decreased. -/
theorem strictBelow_of_le_of_strictBelow
    {p q r : d.FormalBall} (hpq : p ≤ q)
    (hqr : StrictBelow d q r) : StrictBelow d p r := by
  have hpq' := (FormalBall.le_def d).mp hpq
  have hfinite : d.edist p.center q.center ≠ ∞ := by
    intro htop
    rw [htop] at hpq'
    simp at hpq'
  calc
    d.edist p.center r.center + (r.radius : ℝ≥0∞)
        ≤ (d.edist p.center q.center + d.edist q.center r.center) +
            (r.radius : ℝ≥0∞) :=
          add_le_add (d.edist_triangle _ _ _) le_rfl
    _ = d.edist p.center q.center +
          (d.edist q.center r.center + (r.radius : ℝ≥0∞)) := by
            ac_rfl
    _ < d.edist p.center q.center + (q.radius : ℝ≥0∞) :=
      (ENNReal.add_lt_add_iff_left hfinite).2 hqr
    _ ≤ (p.radius : ℝ≥0∞) := hpq'

/-- Lemma 3.4: every formal ball is the supremum of its geometrically
shifted approximants. -/
theorem geometricShift_isLUB (q : d.FormalBall) :
    IsLUB
      (Set.range (fun n : ℕ ↦
        FormalBall.shift d (geometricRadius n) q)) q := by
  constructor
  · intro p hp
    rcases hp with ⟨n, rfl⟩
    rw [FormalBall.le_def]
    simp [FormalBall.shift, d.edist_self, ENNReal.coe_add]
  · intro a ha
    rw [FormalBall.le_def]
    apply ENNReal.le_of_forall_pos_le_add
    intro ε hε _hfinite
    obtain ⟨N, hN⟩ := eventually_atTop.1
      ((tendsto_order.1 geometricRadius_tendsto_zero).2 ε hε)
    have hNa := (FormalBall.le_def d).mp (ha ⟨N, rfl⟩)
    calc
      d.edist q.center a.center + (a.radius : ℝ≥0∞)
          ≤ ((q.radius + geometricRadius N : ℝ≥0) : ℝ≥0∞) := hNa
      _ = (q.radius : ℝ≥0∞) + (geometricRadius N : ℝ≥0∞) :=
        ENNReal.coe_add q.radius (geometricRadius N)
      _ ≤ (q.radius : ℝ≥0∞) + (ε : ℝ≥0∞) :=
        add_le_add le_rfl (ENNReal.coe_le_coe.mpr (hN N le_rfl).le)

/-- Lemma 7.2: order-theoretic way-below implies the strict
formal-ball relation. -/
theorem strictBelow_of_wayBelow {p q : d.FormalBall}
    (hpq : d.FormalBallWayBelow p q) : StrictBelow d p q := by
  let S : Set d.FormalBall := Set.range (fun n : ℕ ↦
    FormalBall.shift d (geometricRadius n) q)
  have hSne : S.Nonempty := ⟨_, ⟨0, rfl⟩⟩
  have hSdir : DirectedOn (· ≤ ·) S := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    let k := max i j
    refine ⟨FormalBall.shift d (geometricRadius k) q,
      ⟨k, rfl⟩, ?_, ?_⟩
    · change FormalBall.shift d (geometricRadius i) q ≤
        FormalBall.shift d (geometricRadius k) q
      rw [FormalBall.le_def]
      simp only [FormalBall.shift, d.edist_self, zero_add, ENNReal.coe_add]
      exact ENNReal.coe_le_coe.mpr
        (add_le_add le_rfl
          (geometricRadius_antitone (le_max_left i j)))
    · change FormalBall.shift d (geometricRadius j) q ≤
        FormalBall.shift d (geometricRadius k) q
      rw [FormalBall.le_def]
      simp only [FormalBall.shift, d.edist_self, zero_add, ENNReal.coe_add]
      exact ENNReal.coe_le_coe.mpr
        (add_le_add le_rfl
          (geometricRadius_antitone (le_max_right i j)))
  have hsup : IsLUB S q := geometricShift_isLUB d q
  rcases hpq hSne hSdir hsup le_rfl with ⟨a, haS, hpa⟩
  rcases haS with ⟨n, rfl⟩
  have hpa' := (FormalBall.le_def d).mp hpa
  change d.edist p.center q.center +
      (((q.radius + geometricRadius n : ℝ≥0) : ℝ≥0∞)) ≤
        (p.radius : ℝ≥0∞) at hpa'
  have hbaseLe :
      d.edist p.center q.center + (q.radius : ℝ≥0∞) ≤
        (p.radius : ℝ≥0∞) := by
    calc
      d.edist p.center q.center + (q.radius : ℝ≥0∞)
          ≤ d.edist p.center q.center +
              (((q.radius + geometricRadius n : ℝ≥0) : ℝ≥0∞)) := by
            apply add_le_add le_rfl
            rw [ENNReal.coe_add]
            exact le_add_right le_rfl
      _ ≤ (p.radius : ℝ≥0∞) := hpa'
  have hbaseFinite :
      d.edist p.center q.center + (q.radius : ℝ≥0∞) ≠ ∞ := by
    exact ne_top_of_le_ne_top ENNReal.coe_ne_top hbaseLe
  calc
    d.edist p.center q.center + (q.radius : ℝ≥0∞)
        < (d.edist p.center q.center + (q.radius : ℝ≥0∞)) +
            (geometricRadius n : ℝ≥0∞) := by
          have hadd := (ENNReal.add_lt_add_iff_left hbaseFinite).2
            (ENNReal.coe_pos.2 (geometricRadius_pos n))
          simpa using hadd
    _ = d.edist p.center q.center +
          (((q.radius + geometricRadius n : ℝ≥0) : ℝ≥0∞)) := by
            simp [ENNReal.coe_add, add_assoc]
    _ ≤ (p.radius : ℝ≥0∞) := hpa'

end FormalBall

namespace FormalBallWayBelow

/-- Lemma 3.2: removing a common radius shift preserves way-below in every
standard quasi-metric space. -/
theorem of_shift
    (hstandard : d.IsStandard) (t : ℝ≥0)
    {p q : d.FormalBall}
    (h : d.FormalBallWayBelow (FormalBall.shift d t p)
      (FormalBall.shift d t q)) :
    d.FormalBallWayBelow p q := by
  intro S hSne hSdir a hSa hqa
  let I := {s // s ∈ S}
  let b : I → d.FormalBall := fun i ↦ i.1
  have hIdir : IsDirectedIndex I := by
    constructor
    · exact hSne.to_subtype
    · intro i j
      rcases hSdir i.1 i.2 j.1 j.2 with ⟨k, hkS, hik, hjk⟩
      exact ⟨⟨k, hkS⟩, hik, hjk⟩
  have hbmono : Monotone b := fun _ _ hij ↦ hij
  have hbLUB : IsLUB (Set.range b) a := by
    simpa [I, b] using hSa
  have hshiftLUB := IsStandard.shift_isLUB d hstandard b hIdir
    hbmono hbLUB t
  have hshiftqa : FormalBall.shift d t q ≤ FormalBall.shift d t a :=
    (FormalBall.shift_le_shift_iff d t q a).2 hqa
  letI : Nonempty I := hIdir.1
  rcases h (Set.range_nonempty (fun i : I ↦ FormalBall.shift d t (b i)))
      (by
        rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
        rcases hIdir.2 i j with ⟨k, hik, hjk⟩
        exact ⟨FormalBall.shift d t (b k), ⟨k, rfl⟩,
          (FormalBall.shift_le_shift_iff d t _ _).2 (hbmono hik),
          (FormalBall.shift_le_shift_iff d t _ _).2 (hbmono hjk)⟩)
      hshiftLUB hshiftqa with ⟨z, hz, hpz⟩
  rcases hz with ⟨i, rfl⟩
  exact ⟨b i, i.2,
    (FormalBall.shift_le_shift_iff d t p (b i)).1 hpz⟩

/-- Proposition 3.6: in a standard continuous formal-ball poset, adding a
common radius shift preserves way-below. -/
theorem shift
    (hstandard : d.IsStandard)
    (hcontinuous : d.FormalBallPosetContinuous)
    (t : ℝ≥0) {p q : d.FormalBall}
    (hpq : d.FormalBallWayBelow p q) :
    d.FormalBallWayBelow (FormalBall.shift d t p)
      (FormalBall.shift d t q) := by
  intro S hSne hSdir a hSa hshiftqa
  let W : Set d.FormalBall :=
    {z | d.FormalBallWayBelow z (FormalBall.shift d t q)}
  have hW := hcontinuous (FormalBall.shift d t q)
  let I := {z // z ∈ W}
  let b : I → d.FormalBall := fun i ↦ i.1
  have hIdir : IsDirectedIndex I := by
    constructor
    · exact hW.1.to_subtype
    · intro i j
      rcases hW.2.1 i.1 i.2 j.1 j.2 with ⟨k, hkW, hik, hjk⟩
      exact ⟨⟨k, hkW⟩, hik, hjk⟩
  have hbmono : Monotone b := fun _ _ hij ↦ hij
  have hbLUB : IsLUB (Set.range b) (FormalBall.shift d t q) := by
    simpa [I, b, W] using hW.2.2
  have htq : t ≤ (FormalBall.shift d t q).radius := by
    simp [FormalBall.shift]
  have hunshiftLUB := IsStandard.unshift_isLUB d hstandard b hIdir
    hbmono hbLUB htq
  have htarget : FormalBall.unshift d t
      (FormalBall.shift d t q) = q := by
    simp [FormalBall.unshift, FormalBall.shift]
  rw [htarget] at hunshiftLUB
  letI : Nonempty I := hIdir.1
  have hunshiftDir : DirectedOn (· ≤ ·)
      (Set.range (fun i : I ↦ FormalBall.unshift d t (b i))) := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    rcases hIdir.2 i j with ⟨k, hik, hjk⟩
    have hti : t ≤ (b i).radius := by
      have hiq := FormalBallWayBelow.le d i.2
      exact htq.trans (FormalBall.radius_le_of_le d hiq)
    have htj : t ≤ (b j).radius := by
      have hjq := FormalBallWayBelow.le d j.2
      exact htq.trans (FormalBall.radius_le_of_le d hjq)
    have htk : t ≤ (b k).radius := by
      have hkq := FormalBallWayBelow.le d k.2
      exact htq.trans (FormalBall.radius_le_of_le d hkq)
    refine ⟨FormalBall.unshift d t (b k), ⟨k, rfl⟩, ?_, ?_⟩
    · apply (FormalBall.shift_le_shift_iff d t _ _).1
      simpa [FormalBall.shift_unshift d hti,
        FormalBall.shift_unshift d htk] using hbmono hik
    · apply (FormalBall.shift_le_shift_iff d t _ _).1
      simpa [FormalBall.shift_unshift d htj,
        FormalBall.shift_unshift d htk] using hbmono hjk
  rcases hpq (Set.range_nonempty
      (fun i : I ↦ FormalBall.unshift d t (b i)))
      hunshiftDir hunshiftLUB le_rfl with
    ⟨z, hz, hpz⟩
  rcases hz with ⟨i, rfl⟩
  have hti : t ≤ (b i).radius := by
    have hiq := FormalBallWayBelow.le d i.2
    exact htq.trans (FormalBall.radius_le_of_le d hiq)
  have hshiftp : FormalBall.shift d t p ≤ b i := by
    have := (FormalBall.shift_le_shift_iff d t p
      (FormalBall.unshift d t (b i))).2 hpz
    simpa [FormalBall.shift_unshift d hti] using this
  have hib : d.FormalBallWayBelow (b i) a :=
    mono_right d i.2 hshiftqa
  rcases hib hSne hSdir hSa le_rfl with ⟨s, hsS, his⟩
  exact ⟨s, hsS, hshiftp.trans his⟩

theorem shift_iff
    (hstandard : d.IsStandard)
    (hcontinuous : d.FormalBallPosetContinuous)
    (t : ℝ≥0) (p q : d.FormalBall) :
    d.FormalBallWayBelow (FormalBall.shift d t p)
        (FormalBall.shift d t q) ↔
      d.FormalBallWayBelow p q :=
  ⟨of_shift d hstandard t, shift d hstandard hcontinuous t⟩

end FormalBallWayBelow

namespace RoundedIdeal

/-- The rounded ideal `↓↓q` of all formal balls way below `q`. -/
def wayBelowIdeal
    (hcontinuous : d.FormalBallPosetContinuous)
    (q : d.FormalBall) : d.RoundedIdeal where
  val := {p | d.FormalBallWayBelow p q}
  property := by
    constructor
    · intro p r hr hpr
      exact FormalBallWayBelow.mono_left d
        (FormalBall.le_of_strictBelow d hpr) hr
    · constructor
      · exact (hcontinuous q).1
      · intro p hp r hr
        rcases (hcontinuous q).2.1 p hp r hr with
          ⟨a, ha, hpa, hra⟩
        rcases FormalBallWayBelow.exists_interpolant d hcontinuous ha with
          ⟨b, hab, hbq⟩
        have habStrict := FormalBall.strictBelow_of_wayBelow d hab
        exact ⟨b, hbq,
          FormalBall.strictBelow_of_le_of_strictBelow d hpa habStrict,
          FormalBall.strictBelow_of_le_of_strictBelow d hra habStrict⟩

@[simp]
theorem mem_wayBelowIdeal_iff
    (hcontinuous : d.FormalBallPosetContinuous)
    {p q : d.FormalBall} :
    p ∈ wayBelowIdeal d hcontinuous q ↔
      d.FormalBallWayBelow p q :=
  Iff.rfl

/-- The way-below ideal at a zero-radius ball has aperture zero. -/
theorem aperture_wayBelowIdeal_zero
    (hstandard : d.IsStandard)
    (hcontinuous : d.FormalBallPosetContinuous)
    (x : X) :
    aperture d (wayBelowIdeal d hcontinuous
      (⟨x, 0⟩ : d.FormalBall)) = 0 := by
  let A := wayBelowIdeal d hcontinuous (⟨x, 0⟩ : d.FormalBall)
  let I := {p // p ∈ A}
  let b : I → d.FormalBall := fun i ↦ i.1
  have hA := hcontinuous (⟨x, 0⟩ : d.FormalBall)
  have hIdir : IsDirectedIndex I := by
    constructor
    · exact hA.1.to_subtype
    · intro i j
      rcases hA.2.1 i.1 i.2 j.1 j.2 with ⟨k, hk, hik, hjk⟩
      exact ⟨⟨k, hk⟩, hik, hjk⟩
  have hbmono : Monotone b := fun _ _ hij ↦ hij
  have hbLUB : IsLUB (Set.range b) (⟨x, 0⟩ : d.FormalBall) := by
    simpa [I, b, A, wayBelowIdeal] using hA.2.2
  apply le_antisymm
  · apply ENNReal.le_of_forall_pos_le_add
    intro ε hε _hfinite
    obtain ⟨i, hi⟩ :=
      IsStandard.radius_eventually_lt_of_zeroRadius_isLUB d hstandard
        b hIdir hbmono x hbLUB ε hε
    simpa using (aperture_le_radius d A i.2).trans
      (ENNReal.coe_le_coe.mpr (hi i le_rfl).le)
  · exact zero_le _

/-- Lemma 7.4: translation of a way-below ideal is the way-below ideal of
the translated formal ball. -/
theorem shift_wayBelowIdeal
    (hstandard : d.IsStandard)
    (hcontinuous : d.FormalBallPosetContinuous)
    (t : ℝ≥0) (q : d.FormalBall) :
    shift d t (wayBelowIdeal d hcontinuous q) =
      wayBelowIdeal d hcontinuous (FormalBall.shift d t q) := by
  apply RoundedIdeal.ext
  intro p
  constructor
  · intro hp
    have hun : d.FormalBallWayBelow (FormalBall.unshift d t p) q := hp.2
    have hshift : d.FormalBallWayBelow
        (FormalBall.shift d t (FormalBall.unshift d t p))
        (FormalBall.shift d t q) := by
      exact FormalBallWayBelow.shift d hstandard hcontinuous t hun
    rw [FormalBall.shift_unshift d hp.1] at hshift
    change d.FormalBallWayBelow p (FormalBall.shift d t q)
    exact hshift
  · intro hp
    have hple := FormalBallWayBelow.le d hp
    have htq : t ≤ (FormalBall.shift d t q).radius := by
      simp [FormalBall.shift]
    have htp : t ≤ p.radius :=
      htq.trans (FormalBall.radius_le_of_le d hple)
    refine ⟨htp, ?_⟩
    change d.FormalBallWayBelow (FormalBall.unshift d t p) q
    have hshift : d.FormalBallWayBelow
        (FormalBall.shift d t (FormalBall.unshift d t p))
        (FormalBall.shift d t q) := by
      rw [FormalBall.shift_unshift d htp]
      exact hp
    intro S hSne hSdir a hSa hqa
    exact (FormalBallWayBelow.of_shift d hstandard t
      (p := FormalBall.unshift d t p) (q := q) hshift)
        hSne hSdir hSa hqa

/-- The way-below ideal assignment is monotone. -/
theorem wayBelowIdeal_mono
    (hcontinuous : d.FormalBallPosetContinuous) :
    Monotone (wayBelowIdeal d hcontinuous) := by
  intro p q hpq a ha
  exact FormalBallWayBelow.mono_right d ha hpq

/-- The canonical basis map `q ↦ ↓↓q` is Scott-continuous. -/
theorem wayBelowIdeal_scottContinuous
    (hcontinuous : d.FormalBallPosetContinuous) :
    ScottContinuous (wayBelowIdeal d hcontinuous) := by
  intro S hSne hSdir q hSq
  constructor
  · rintro _ ⟨p, hpS, rfl⟩
    exact wayBelowIdeal_mono d hcontinuous (hSq.1 hpS)
  · intro A hA a ha
    rcases FormalBallWayBelow.exists_interpolant d hcontinuous ha with
      ⟨b, hab, hbq⟩
    rcases hbq hSne hSdir hSq le_rfl with ⟨p, hpS, hbp⟩
    have hap : d.FormalBallWayBelow a p :=
      FormalBallWayBelow.mono_right d hab hbp
    exact hA ⟨p, hpS, rfl⟩ hap

end RoundedIdeal
end QuasiMetric
end LipschitzYonedaFinalTopology
