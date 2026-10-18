import CoreCompactNonSober.RetainedDcpo
import CoreCompactSimplified.SourceDefinitions

/-!
# Direct common-lower witnesses for the recursively constructed dcpo

Source: `prop:two-conditions` of the 2026-10-15 manuscript. The positive
case processes the endpoint/top task, chooses a rational height cut, then
processes an endpoint/reference task. No regularity of lambda is assumed.
The older two-stage localized-closure helpers are retained below solely as
additional compatibility results, not as current source statements or as
the proof of `retained_commonLowerWitness`.
-/

set_option autoImplicit false

namespace CoreCompactNonSober.Construction

open Set Ambient

/-- A row in the actual recursive union has its endpoint as its intrinsic
directed supremum; no ambient/subtype topology is identified here. -/
theorem pairRow_subtype_lub {p b : Carrier} (R : PairRow p b)
    (hp : p ∈ retained) (hR : ∀ n, R.point n ∈ retained) :
    IsLUB (Set.range (fun n ↦ (⟨R.point n, hR n⟩ : retained)))
      (⟨p, hp⟩ : retained) := by
  constructor
  · rintro _ ⟨n, rfl⟩
    exact R.below_endpoint n
  · intro q hq
    apply R.isLUB.2
    rintro _ ⟨n, rfl⟩
    exact hq (Set.mem_range_self n)

theorem pairRow_subtype_directed {p b : Carrier} (R : PairRow p b)
    (hR : ∀ n, R.point n ∈ retained) :
    NonemptyDirected (Set.range (fun n ↦ (⟨R.point n, hR n⟩ : retained))) := by
  let r : ℕ → retained := fun n ↦ ⟨R.point n, hR n⟩
  have hrmono : Monotone r := fun _ _ h ↦ R.strictMono.monotone h
  exact ⟨Set.range_nonempty r, hrmono.directed_le.directedOn_range⟩

/-- Proposition `prop:two-conditions`, condition (ii), with the printed
two-row proof. The second partner is a member of R, not a retained point.
The explicit rational height cut is part of the source argument. -/
theorem retained_commonLowerWitness : CoreCompactSimplified.CommonLowerWitness retained := by
  letI : TopologicalSpace Carrier := scottTopology Carrier
  letI : TopologicalSpace retained := scottTopology retained
  intro U q hqU E hE s hs hqs
  have hsup : sSup E = s := (isLUB_sSup E).unique hs
  have hq : q.val ≤ sSup E := by simpa only [hsup] using hqs
  have hU := (isOpen_scott_iff _).mp U.isOpen
  by_cases hpos : Positive q.val
  · obtain ⟨P, hP⟩ := retained_referenceRows q.val q.property hpos
      ⊤ top_mem_reference (by
        rw [top_eq_fullAt_one]
        exact q.val.val.1.property.2)
    obtain ⟨p, hpRange, hpU⟩ := hU.2 _ (pairRow_subtype_directed P hP)
      q (pairRow_subtype_lub P q.property hP) hqU
    obtain ⟨n, rfl⟩ := hpRange
    have hpSup : P.point n ≤ sSup E := (P.below_endpoint n).trans hq
    have hheight : height (P.point n) < height (sSup E) :=
      (P.height_lt n).trans_le ((le_iff _ _).mp hq).1
    obtain ⟨e₀, he₀E, he₀height⟩ := (heightAbove_isScottOpen (height (P.point n))).2
      E hE (sSup E) (isLUB_sSup E) hheight
    change height (P.point n) < height e₀ at he₀height
    obtain ⟨r, hpr, hre₀⟩ := exists_rat_btwn he₀height
    let H : ScottOpens Carrier :=
      ⟨heightAbove (r : ℝ), (isOpen_scott_iff _).mpr (heightAbove_isScottOpen _)⟩
    obtain ⟨b, hbR, hbH, hbe₀⟩ := witnessFamily_approx e₀
      ((P.positive n).trans (hpr.trans hre₀)) H hre₀
    have hpb : height (P.point n) ≤ height b := (hpr.trans hbH).le
    obtain ⟨R, hR⟩ := retained_referenceRows (P.point n) (hP n) (P.positive n)
      b (witness_mem_reference hbR) hpb
    obtain ⟨r', hrRange, hrU⟩ := hU.2 _ (pairRow_subtype_directed R hR)
      (⟨P.point n, hP n⟩ : retained) (pairRow_subtype_lub R (hP n) hR) hpU
    obtain ⟨k, rfl⟩ := hrRange
    obtain ⟨e, heE, hre⟩ := R.finite_prefix_domination hpb E hE hpSup e₀ he₀E hbe₀ k
    exact ⟨⟨R.point k, hR k⟩, hrU,
      (R.below_endpoint k).trans (P.below_endpoint n), e, heE, hre⟩
  · have hqzero : height q.val = 0 :=
      le_antisymm (le_of_not_gt hpos) q.val.val.1.property.1
    have hmeetS : ∀ e : E, q.val ⊓ e.val ∈ retained := by
      intro e
      apply zeroLayer_subset_retained
      have hle : height (q.val ⊓ e.val) ≤ 0 := by
        simpa only [hqzero] using ((le_iff _ _).mp
          (inf_le_left : q.val ⊓ e.val ≤ q.val)).1
      exact le_antisymm hle (q.val ⊓ e.val).val.1.property.1
    let f : E → retained := fun e ↦ ⟨q.val ⊓ e.val, hmeetS e⟩
    haveI : Nonempty E := hE.1.to_subtype
    have hdir : NonemptyDirected (Set.range f) := by
      refine ⟨Set.range_nonempty f, ?_⟩
      rintro _ ⟨e, rfl⟩ _ ⟨e', rfl⟩
      obtain ⟨d, hd, hed, he'd⟩ := hE.2 e.val e.property e'.val e'.property
      exact ⟨f ⟨d, hd⟩, Set.mem_range_self _, inf_le_inf_left _ hed, inf_le_inf_left _ he'd⟩
    have hmeetLub : IsLUB ((fun e : Carrier ↦ q.val ⊓ e) '' E) q.val := by
      have h := scottContinuous_meet_left q.val hE.1 hE.2 (isLUB_sSup E)
      simpa only [inf_eq_left.mpr hq] using h
    have hlub : IsLUB (Set.range f) q := by
      constructor
      · rintro _ ⟨e, rfl⟩
        change q.val ⊓ e.val ≤ q.val
        exact inf_le_left
      · intro z hz
        apply hmeetLub.2
        rintro _ ⟨e, he, rfl⟩
        exact hz (Set.mem_range_self (⟨e, he⟩ : E))
    obtain ⟨r, hrRange, hrU⟩ := hU.2 _ hdir q hlub hqU
    obtain ⟨e, rfl⟩ := hrRange
    refine ⟨f e, hrU, ?_, e.val, e.property, ?_⟩
    · change q.val ⊓ e.val ≤ q.val
      exact inf_le_left
    · change q.val ⊓ e.val ≤ e.val
      exact inf_le_right

theorem pairRow_endpoint_stage {p b : Carrier} (R : PairRow p b)
    (hp : p ∈ retained) (hR : ∀ n, R.point n ∈ retained)
    (A : Set retained) (k : ℕ)
    (hstage : ∀ n, (⟨R.point n, hR n⟩ : retained) ∈ closureStage k A) :
    (⟨p, hp⟩ : retained) ∈ closureStage (k + 1) A := by
  let r : ℕ → retained := fun n ↦ ⟨R.point n, hR n⟩
  have hrmono : Monotone r := fun n m hnm ↦ R.strictMono.monotone hnm
  have hdir : NonemptyDirected (Set.range r) :=
    ⟨Set.range_nonempty r, hrmono.directed_le.directedOn_range⟩
  have hlub : IsLUB (Set.range r) (⟨p, hp⟩ : retained) := by
    constructor
    · rintro _ ⟨n, rfl⟩
      exact R.below_endpoint n
    · intro q hq
      apply R.isLUB.2
      rintro _ ⟨n, rfl⟩
      exact hq (Set.mem_range_self n)
  refine ⟨⟨p, hp⟩, ⟨Set.range r, ?_, hdir, hlub⟩, le_rfl⟩
  rintro _ ⟨n, rfl⟩
  exact hstage n

/-- Additional compatibility theorem for legacy topology-transfer APIs.
It is not a numbered statement of the current manuscript and is not used
in the new direct common-lower proof. -/
theorem retained_localizedClosure : LocalizedClosure retained := by
  letI : TopologicalSpace Carrier := scottTopology Carrier
  intro E hE q hq
  let A := localizedLowerSet retained q E
  by_cases hpos : Positive q.val
  · obtain ⟨P, hP⟩ := retained_referenceRows q.val q.property hpos
      ⊤ top_mem_reference (by
        rw [top_eq_fullAt_one]
        exact q.val.val.1.property.2)
    have hpstage : ∀ n, (⟨P.point n, hP n⟩ : retained) ∈ closureStage 1 A := by
      intro n
      have hheight : height (P.point n) < height (sSup E) :=
        (P.height_lt n).trans_le ((le_iff _ _).mp hq).1
      obtain ⟨e, heE, heheight⟩ := (heightAbove_isScottOpen (height (P.point n))).2
        E hE (sSup E) (isLUB_sSup E) hheight
      let U : ScottOpens Carrier :=
        ⟨heightAbove (height (P.point n)),
          (isOpen_scott_iff _).mpr (heightAbove_isScottOpen _)⟩
      obtain ⟨b, hbR, hbheight, hbe⟩ := witnessFamily_approx e
        ((P.positive n).trans heheight) U heheight
      change height (P.point n) < height b at hbheight
      have hpb : height (P.point n) ≤ height b := hbheight.le
      obtain ⟨R, hR⟩ := retained_referenceRows (P.point n) (hP n) (P.positive n)
        b (witness_mem_reference hbR) hpb
      apply pairRow_endpoint_stage R (hP n) hR A 0
      intro m
      have hpSup : P.point n ≤ sSup E := (P.below_endpoint n).trans hq
      obtain ⟨e', he'E, hRe'⟩ := R.finite_prefix_domination hpb E hE hpSup e heE hbe m
      have hRA : (⟨R.point m, hR m⟩ : retained) ∈ A :=
        ⟨(R.below_endpoint m).trans (P.below_endpoint n), e', he'E, hRe'⟩
      exact ⟨⟨R.point m, hR m⟩, hRA, le_rfl⟩
    exact pairRow_endpoint_stage P q.property hP A 1 hpstage
  · have hqzero : height q.val = 0 :=
      le_antisymm (le_of_not_gt hpos) q.val.val.1.property.1
    have hmeetS : ∀ e : E, q.val ⊓ e.val ∈ retained := by
      intro e
      apply zeroLayer_subset_retained
      have hle : height (q.val ⊓ e.val) ≤ 0 := by
        simpa only [hqzero] using ((le_iff _ _).mp (inf_le_left : q.val ⊓ e.val ≤ q.val)).1
      exact le_antisymm hle (q.val ⊓ e.val).val.1.property.1
    let f : E → retained := fun e ↦ ⟨q.val ⊓ e.val, hmeetS e⟩
    haveI : Nonempty E := hE.1.to_subtype
    have hdir : NonemptyDirected (Set.range f) := by
      refine ⟨Set.range_nonempty f, ?_⟩
      rintro _ ⟨e, rfl⟩ _ ⟨e', rfl⟩
      obtain ⟨d, hd, hed, he'd⟩ := hE.2 e.val e.property e'.val e'.property
      exact ⟨f ⟨d, hd⟩, Set.mem_range_self _, inf_le_inf_left _ hed, inf_le_inf_left _ he'd⟩
    have hmeetLub : IsLUB ((fun e : Carrier ↦ q.val ⊓ e) '' E) q.val := by
      have h := scottContinuous_meet_left q.val hE.1 hE.2 (isLUB_sSup E)
      simpa only [inf_eq_left.mpr hq] using h
    have hlub : IsLUB (Set.range f) q := by
      constructor
      · rintro _ ⟨e, rfl⟩
        change q.val ⊓ e.val ≤ q.val
        exact inf_le_left
      · intro z hz
        apply hmeetLub.2
        rintro _ ⟨e, he, rfl⟩
        exact hz (Set.mem_range_self (⟨e, he⟩ : E))
    have hstage1 : q ∈ closureStage 1 A := by
      refine ⟨q, ⟨Set.range f, ?_, hdir, hlub⟩, le_rfl⟩
      rintro _ ⟨e, rfl⟩
      have hfa : f e ∈ A := ⟨inf_le_left, e.val, e.property, inf_le_right⟩
      exact ⟨f e, hfa, le_rfl⟩
    exact closureStage_subset_succ 1 A hstage1

/-- Additional legacy-manuscript intrinsic Scott-closure conclusion, now
also true for this newly adapted recursively retained sub-dcpo. This is not
represented as a numbered claim of the current 2026-10-15 source. -/
theorem retained_localizedScottClosure (E : Set Carrier)
    (hE : NonemptyDirected E) (q : retained)
    (hq : (q : Carrier) ≤ sSup E) :
    q ∈ @closure retained (scottTopology retained)
      (localizedLowerSet retained q E) :=
  localizedClosure_mem_scottClosure retained_localizedClosure E hE q hq

end CoreCompactNonSober.Construction
