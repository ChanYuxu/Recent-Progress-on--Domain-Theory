import CantorFubini.SameTrace
import CantorFubini.StabilizedValuation
import CantorFubini.Hitting

/-!
The actual null-set indices, random-open stages and stabilized second valuation
of source §§4–5. The null-index countable-union argument is adapted from
ZFC_Fubini_Lean/ZFCFubini/NullIndex.lean, SHA256
b3bbc829ca9bbd9aef4aa421bd42a12711680d92747039f8f19bc49621cc98b7;
the source-facing constructions and
the two same-trace replacements are new for the literal null-ideal carrier.
-/

set_option autoImplicit false
open Set Topology TopologicalSpace MeasureTheory
universe u v w
namespace CantorFubini
variable {X : Type u} [TopologicalSpace X] [T2Space X] [MeasurableSpace X]

/-- All subsets of completed-measure null sets are allowed, without a Borel
restriction on the index. -/
def NullIndex (m : Measure X) := {N : Set X // m N = 0}

instance (m : Measure X) : PartialOrder (NullIndex m) :=
  inferInstanceAs (PartialOrder {N : Set X // m N = 0})

instance (m : Measure X) : Nonempty (NullIndex m) := ⟨⟨∅, measure_empty⟩⟩

instance (m : Measure X) : SemilatticeSup (NullIndex m) :=
  Subtype.semilatticeSup (fun _ _ hN hL => measure_union_null hN hL)

theorem nullIndex_countablyBounded (m : Measure X) : CountablyBounded (NullIndex m) := by
  intro S hS
  letI : Countable S := hS.to_subtype
  let N : Set X := ⋃ M : S, M.val.val
  have hN : m N = 0 := measure_iUnion_null (fun M : S => M.val.property)
  exact ⟨⟨N, hN⟩, fun M hM => subset_iUnion (fun K : S => K.val.val) ⟨M, hM⟩⟩

section Stages
variable (m : Measure X) {T : Type v} [TopologicalSpace T] (R : T → Opens X)

/-- The manuscript's specified `G_M(t) = B_{U_t} ∪ A_M`. -/
def G (M : NullIndex m) (t : T) : WithScott (ScottOpens (IdealPoint m)) :=
  WithScott.toScott (B m (R t) ⊔ A m M.val M.property)

@[simp] theorem trace_G (M : NullIndex m) (t : T) :
    trace (WithScott.ofScott (G m R M t)) = (R t : Set X) ∪ M.valᶜ := by
  simp only [G, WithScott.ofScott_toScott, trace_sup, trace_B, trace_A]

theorem G_antitone : ∀ t, Antitone (fun M => G m R M t) := by
  intro t M N hMN
  exact sup_le_sup_left (A_antitone m M.property N.property hMN) _

theorem G_continuous (hR : Continuous (fun t => WithScott.toScott (R t)))
    (M : NullIndex m) : Continuous (G m R M) := by
  have hf : ScottContinuous (fun O : Opens X => B m O ⊔ A m M.val M.property) :=
    (B_scottContinuous m).comp (sup_right_scottContinuous _)
  exact ((scott_continuous_iff _).mp hf).comp hR

variable [SecondCountableTopology T]

/-- The exact common decreasing-stage event, independently of any chosen
stabilization index. -/
def psi (hR : Continuous (fun t => WithScott.toScott (R t)))
    (A₀ : ScottOpens (ScottOpens (IdealPoint m))) : Opens T :=
  stabilizedEvent (nullIndex_countablyBounded m) (G m R) (G_antitone m R)
    (G_continuous m R hR) A₀

theorem psi_eventually_eq (hR : Continuous (fun t => WithScott.toScott (R t)))
    (A₀ : ScottOpens (ScottOpens (IdealPoint m))) :
    ∃ M₀ : NullIndex m, ∀ M, M₀ ≤ M →
      G m R M ⁻¹' (A₀ : Set (WithScott (ScottOpens (IdealPoint m)))) =
        (psi m R hR A₀ : Set T) :=
  stabilizedEvent_eventually_eq (nullIndex_countablyBounded m) (G m R)
    (G_antitone m R) (G_continuous m R hR) A₀

end Stages

/-- Exact finite-removal indices `F ∈ Fin(M \ M₀)`. -/
abbrev RemovedFinset {m : Measure X} (M M₀ : NullIndex m) :=
  {F : Finset X // (F : Set X) ⊆ M.val \ M₀.val}

def removalOpen {m : Measure X} (M : NullIndex m) (F : Finset X) :
    ScottOpens (IdealPoint m) :=
  A m (M.val \ (F : Set X)) (measure_mono_null diff_subset M.property)

theorem removalOpen_mono {m : Measure X} (M : NullIndex m) : Monotone (removalOpen M) := by
  intro F K hFK
  exact A_antitone m _ _ (diff_subset_diff_right hFK)

theorem removalOpen_directed {m : Measure X} (M M₀ : NullIndex m) :
    Directed (· ≤ ·) (fun F : RemovedFinset M M₀ => removalOpen M F.val) := by
  classical
  intro F K
  have hFK : ((F.val ∪ K.val : Finset X) : Set X) ⊆ M.val \ M₀.val := by
    intro x hx
    exact (Finset.mem_union.mp hx).elim (fun h => F.property h) (fun h => K.property h)
  exact ⟨⟨F.val ∪ K.val, hFK⟩, removalOpen_mono M Finset.subset_union_left,
    removalOpen_mono M Finset.subset_union_right⟩

def removalUnion {m : Measure X} (M M₀ : NullIndex m) : ScottOpens (IdealPoint m) :=
  ⨆ F : RemovedFinset M M₀, removalOpen M F.val

theorem removalUnion_le {m : Measure X} (M M₀ : NullIndex m) (hM : M₀ ≤ M) :
    removalUnion M M₀ ≤ A m M₀.val M₀.property := by
  apply iSup_le
  intro F
  apply A_antitone m _ _
  intro x hx
  exact ⟨hM hx, fun hxF => (F.property hxF).2 hx⟩

theorem trace_removalUnion {m : Measure X} (M M₀ : NullIndex m) (hM : M₀ ≤ M) :
    trace (removalUnion M M₀) = M₀.valᶜ := by
  classical
  ext x
  constructor
  · intro hx
    have hxA : x ∈ trace (A m M₀.val M₀.property) := removalUnion_le M M₀ hM hx
    simpa only [trace_A] using hxA
  · intro hx
    change WithScott.toScott (IdealPoint.e m x) ∈ removalUnion M M₀
    apply Opens.mem_iSup.mpr
    by_cases hxM : x ∈ M.val
    · have hsingle : (({x} : Finset X) : Set X) ⊆ M.val \ M₀.val := by
        intro y hy
        have hyx : y = x := Finset.mem_singleton.mp hy
        subst y
        exact ⟨hxM, hx⟩
      refine ⟨⟨{x}, hsingle⟩, ?_⟩
      change x ∈ trace (removalOpen M ({x} : Finset X))
      rw [removalOpen, trace_A]
      simp
    · refine ⟨⟨∅, by simp⟩, ?_⟩
      change x ∈ trace (removalOpen M (∅ : Finset X))
      rw [removalOpen, trace_A]
      simpa using hxM

section Comparison
variable [CompactSpace X] {m : Measure X}
variable {T : Type v} [TopologicalSpace T]
variable (R : T → Opens X) (hR : Continuous (fun t => WithScott.toScott (R t)))
variable (stagePrefix : T → ℕ → Opens X) (hprefix : ∀ t, Monotone (stagePrefix t))
variable (hprefixLUB : ∀ t, IsLUB (range (stagePrefix t)) (R t))
variable (hprefixCompact : ∀ t k, IsCompact (stagePrefix t k : Set X))
variable (hclopen : ∀ (x : X) (U : Opens X), x ∈ U →
  ∃ V : Opens X, IsClopen (V : Set X) ∧ x ∈ V ∧ V ≤ U)
variable (hfiniteClopen : ∀ (F : Finset X) (U : Opens X), (F : Set X) ⊆ U →
  ∃ V : Opens X, IsClopen (V : Set X) ∧ (F : Set X) ⊆ V ∧ V ≤ U)

include hR stagePrefix hprefix hprefixLUB hprefixCompact hclopen hfiniteClopen in
/-- Source Proposition `prop:index-comparison`. The second same-trace
application uses exactly `Z = H ∩ (A_M ∪ B_V)`; no mixed-kernel inclusion
`A_(M\F) ⊆ B_U ∪ A_M` is assumed or used. -/
theorem index_comparison {D : Set T} {Nbad : Set X}
    (M₀ M : NullIndex m) (hM : M₀ ≤ M) (hbad : Nbad ⊆ M₀.val)
    (hit : ∀ F : Finset X, (∀ x ∈ F, x ∉ Nbad) →
      ∀ W : Set D, IsOpen W → W.Nonempty → ∃ t ∈ W, (F : Set X) ⊆ R t.val)
    (A₀ : ScottOpens (ScottOpens (IdealPoint m)))
    (hstart : (D ∩ (G m R M₀ ⁻¹' (A₀ : Set (WithScott (ScottOpens (IdealPoint m)))))).Nonempty) :
    (D ∩ (G m R M ⁻¹' (A₀ : Set (WithScott (ScottOpens (IdealPoint m)))))).Nonempty := by
  classical
  obtain ⟨t, htD, htG⟩ := hstart
  let J : ScottOpens (IdealPoint m) := removalUnion M M₀
  have hJtr : trace J = trace (A m M₀.val M₀.property) := by
    rw [trace_A]
    exact trace_removalUnion M M₀ hM
  have havoid₀ : trace (A m M₀.val M₀.property) ⊆ M₀.valᶜ := by rw [trace_A]
  obtain ⟨s, _, hsJ⟩ := same_trace_comparison R hR stagePrefix hprefix hprefixLUB
    hprefixCompact hclopen hbad hit J (A m M₀.val M₀.property) ⊥
    (removalUnion_le M M₀ hM) hJtr havoid₀ A₀ univ isOpen_univ
    ⟨⟨t, htD⟩, mem_univ _, by simpa only [G, sup_bot_eq] using htG⟩
  simp only [sup_bot_eq] at hsJ
  letI : Nonempty (RemovedFinset M M₀) := ⟨⟨∅, by simp⟩⟩
  have hJlub : IsLUB (range (fun F : RemovedFinset M M₀ => removalOpen M F.val)) J := by
    simpa only [J, removalUnion, sSup_range] using
      isLUB_sSup (range (fun F : RemovedFinset M M₀ => removalOpen M F.val))
  obtain ⟨H, hHrange, hsH⟩ := scottOpen_capture_map
    (fun H : ScottOpens (IdealPoint m) => B m (R s.val) ⊔ H)
    (sup_left_scottContinuous _) (range_nonempty _)
    (removalOpen_directed M M₀).directedOn_range hJlub A₀ hsJ
  obtain ⟨F, rfl⟩ := hHrange
  have hFavoid : ∀ x ∈ F.val, x ∉ Nbad := by
    intro x hx hxN
    exact (F.property hx).2 (hbad hxN)
  let W₁ : Set D := {u | WithScott.toScott (B m (R u.val) ⊔ removalOpen M F.val) ∈ A₀}
  have hW₁ : IsOpen W₁ := by
    simpa only [sup_bot_eq] using
      (noise_event_isOpen R hR ⊥ (removalOpen M F.val) A₀).preimage continuous_subtype_val
  obtain ⟨t₁, ht₁W, hFt₁⟩ := hit F.val hFavoid W₁ hW₁ ⟨s, hsH⟩
  obtain ⟨V, hVc, hFV, hVt₁⟩ := hfiniteClopen F.val (R t₁.val) hFt₁
  let C : ScottOpens (IdealPoint m) := A m M.val M.property ⊔ B m V
  let H : ScottOpens (IdealPoint m) := removalOpen M F.val
  let Z : ScottOpens (IdealPoint m) := H ⊓ C
  have hHavoid : trace H ⊆ M₀.valᶜ := by
    intro x hx hxM₀
    have hxnot : x ∉ M.val \ (F.val : Set X) := by
      simpa only [H, removalOpen, trace_A] using hx
    exact hxnot ⟨hM hxM₀, fun hxF => (F.property hxF).2 hxM₀⟩
  have hHCtrace : trace H ⊆ trace C := by
    intro x hx
    have hxnot : x ∉ M.val \ (F.val : Set X) := by
      simpa only [H, removalOpen, trace_A] using hx
    change WithScott.toScott (IdealPoint.e m x) ∈ C
    by_cases hxM : x ∈ M.val
    · have hxF : x ∈ F.val := by by_contra h; exact hxnot ⟨hxM, h⟩
      exact Or.inr (singleton_subset_iff.mpr (hFV hxF))
    · apply Or.inl
      exact ⟨M.property, disjoint_singleton_right.mpr hxM⟩
  have hZHtrace : trace Z = trace H := by
    change trace (H ⊓ C) = trace H
    rw [trace_inf, inter_eq_left.mpr hHCtrace]
  let W : Set D := {u | (V : Set X) ⊆ R u.val}
  have hW : IsOpen W :=
    (compact_event_isOpen R hR hVc.isClosed.isCompact).preimage continuous_subtype_val
  have hstart₂ : ∃ u ∈ W, WithScott.toScott (B m (R u.val) ⊔ C ⊔ H) ∈ A₀ := by
    refine ⟨t₁, hVt₁, ?_⟩
    have hUpper := ((scott_isOpen_iff {L : ScottOpens (IdealPoint m) |
      WithScott.toScott L ∈ A₀}).mp A₀.isOpen).1
    exact hUpper (sup_le (le_sup_of_le_left le_sup_left) le_sup_right) ht₁W
  obtain ⟨t₂, ht₂W, ht₂A⟩ := same_trace_comparison R hR stagePrefix hprefix hprefixLUB
    hprefixCompact hclopen hbad hit Z H C inf_le_left hZHtrace hHavoid A₀ W hW hstart₂
  have hCle : C ≤ B m (R t₂.val) ⊔ A m M.val M.property :=
    sup_le le_sup_right ((B_mono m ht₂W).trans le_sup_left)
  have hAbsorb : B m (R t₂.val) ⊔ C ⊔ Z ≤ B m (R t₂.val) ⊔ A m M.val M.property :=
    sup_le (sup_le le_sup_left hCle) (inf_le_right.trans hCle)
  have hUpper := ((scott_isOpen_iff {L : ScottOpens (IdealPoint m) |
    WithScott.toScott L ∈ A₀}).mp A₀.isOpen).1
  exact ⟨t₂.val, t₂.property, hUpper hAbsorb ht₂A⟩

end Comparison

section Valuation
variable [CompactSpace X] {m : Measure X}
variable {T : Type v} [TopologicalSpace T] [SecondCountableTopology T]
variable [T2Space T] [MeasurableSpace T] [OpensMeasurableSpace T]
variable (R : T → Opens X) (hR : Continuous (fun t => WithScott.toScott (R t)))
variable (stagePrefix : T → ℕ → Opens X) (hprefix : ∀ t, Monotone (stagePrefix t))
variable (hprefixLUB : ∀ t, IsLUB (range (stagePrefix t)) (R t))
variable (hprefixCompact : ∀ t k, IsCompact (stagePrefix t k : Set X))
variable (hclopen : ∀ (x : X) (U : Opens X), x ∈ U →
  ∃ V : Opens X, IsClopen (V : Set X) ∧ x ∈ V ∧ V ≤ U)
variable (hfiniteClopen : ∀ (F : Finset X) (U : Opens X), (F : Set X) ⊆ U →
  ∃ V : Opens X, IsClopen (V : Set X) ∧ (F : Set X) ⊆ V ∧ V ≤ U)
variable (μ : Measure T) [μ.InnerRegular] [IsProbabilityMeasure μ]
variable (hHitting : ∀ D : Set T, PositiveCarrier μ D →
  ∃ N : Set X, m N = 0 ∧ ∀ F : Finset X, (∀ x ∈ F, x ∉ N) →
    ∀ W : Set D, IsOpen W → W.Nonempty → ∃ t ∈ W, (F : Set X) ⊆ R t.val)

include hR stagePrefix hprefix hprefixLUB hprefixCompact hclopen hfiniteClopen hHitting in
/-- One null index is chosen from the carrier before either the later null
index or the Scott-open observation is quantified. -/
theorem G_carrierIndexComparison : CarrierIndexComparison (G m R) μ := by
  intro D hD
  obtain ⟨N, hN, hit⟩ := hHitting D hD
  refine ⟨⟨N, hN⟩, fun M hM A₀ hstart => ?_⟩
  exact index_comparison R hR stagePrefix hprefix hprefixLUB hprefixCompact hclopen
    hfiniteClopen ⟨N, hN⟩ M hM Subset.rfl hit A₀ hstart

include stagePrefix hprefix hprefixLUB hprefixCompact hclopen hfiniteClopen hHitting in
theorem psi_arbitrary_union_defect_null {I : Type w}
    (A₀ : I → ScottOpens (ScottOpens (IdealPoint m))) :
    μ ((psi m R hR (⨆ i, A₀ i) : Set T) \ ⋃ i, (psi m R hR (A₀ i) : Set T)) = 0 :=
  stabilizedEvent_arbitrary_union_defect_null (nullIndex_countablyBounded m) (G m R)
    (G_antitone m R) (G_continuous m R hR) μ
    (G_carrierIndexComparison R hR stagePrefix hprefix hprefixLUB hprefixCompact hclopen
      hfiniteClopen μ hHitting) A₀

/-- A genuine continuous valuation on the full intrinsic Scott topology of
the open-set lattice, constructed from all completed null-set indices. -/
def etaFromHitting : Valuation (WithScott (ScottOpens (IdealPoint m))) :=
  stabilizedValuation (nullIndex_countablyBounded m) (G m R)
    (G_antitone m R) (G_continuous m R hR) μ
    (G_carrierIndexComparison R hR stagePrefix hprefix hprefixLUB hprefixCompact hclopen
      hfiniteClopen μ hHitting)

theorem etaFromHitting_probability :
    (etaFromHitting R hR stagePrefix hprefix hprefixLUB hprefixCompact hclopen
      hfiniteClopen μ hHitting).Probability :=
  stabilizedValuation_probability (nullIndex_countablyBounded m) (G m R)
    (G_antitone m R) (G_continuous m R hR) μ
    (G_carrierIndexComparison R hR stagePrefix hprefix hprefixLUB hprefixCompact hclopen
      hfiniteClopen μ hHitting)

@[simp] theorem etaFromHitting_apply
    (A₀ : ScottOpens (ScottOpens (IdealPoint m))) :
    etaFromHitting R hR stagePrefix hprefix hprefixLUB hprefixCompact hclopen
      hfiniteClopen μ hHitting A₀ = μ (psi m R hR A₀ : Set T) := rfl

end Valuation

/-- The actual Cantor clopen neighborhood needed in the same-trace proof. -/
theorem cantor_clopen_neighborhood (x : Cantor) (U : Opens Cantor) (hx : x ∈ U) :
    ∃ V : Opens Cantor, IsClopen (V : Set Cantor) ∧ x ∈ V ∧ V ≤ U := by
  obtain ⟨n, hn⟩ := exists_cylinder_subset U.isOpen hx
  exact ⟨cylinder x n, cylinder_isClopen x n, cylinder_mem_self x n, hn⟩

noncomputable def exceptionalNullIndex (D : Set Omega)
    (hD : PositiveCarrier parameterProbability D) : NullIndex cantorMeasure :=
  ⟨(hitting hD).choose, (hitting hD).choose_spec.1⟩

theorem exceptionalNullIndex_hit (D : Set Omega)
    (hD : PositiveCarrier parameterProbability D) :
    ∀ F : Finset Cantor, (∀ x ∈ F, x ∉ (exceptionalNullIndex D hD).val) →
      ∀ W : Set D, IsOpen W → W.Nonempty →
        ∃ t ∈ W, (F : Set Cantor) ⊆ randomOpen t.val :=
  (hitting hD).choose_spec.2

/-- Source Lemma `lem:same-trace` specialized to the actual Cantor product
law and actual random cylinder unions, with its hitting input discharged. -/
theorem same_trace_comparison_actual (D : Set Omega)
    (hD : PositiveCarrier parameterProbability D) (M₀ : NullIndex cantorMeasure)
    (hM₀ : exceptionalNullIndex D hD ≤ M₀)
    (Z H B₀ : ScottOpens (IdealPoint cantorMeasure)) (hZH : Z ≤ H)
    (htr : trace Z = trace H) (havoid : trace H ⊆ M₀.valᶜ)
    (A₀ : ScottOpens (ScottOpens (IdealPoint cantorMeasure)))
    (W : Set D) (hW : IsOpen W)
    (hstart : ∃ t ∈ W,
      WithScott.toScott (B cantorMeasure (randomOpen t.val) ⊔ B₀ ⊔ H) ∈ A₀) :
    ∃ s ∈ W,
      WithScott.toScott (B cantorMeasure (randomOpen s.val) ⊔ B₀ ⊔ Z) ∈ A₀ :=
  same_trace_comparison randomOpen randomOpen_continuous randomPrefix randomPrefix_mono
    randomPrefix_isLUB randomPrefix_isCompact cantor_clopen_neighborhood hM₀
    (exceptionalNullIndex_hit D hD) Z H B₀ hZH htr havoid A₀ W hW hstart

/-- Source Proposition `prop:index-comparison`, including the choice of a
single null index before every later index and every Scott-open observation. -/
theorem index_comparison_actual (D : Set Omega)
    (hD : PositiveCarrier parameterProbability D) (M₀ M : NullIndex cantorMeasure)
    (hM₀ : exceptionalNullIndex D hD ≤ M₀) (hM : M₀ ≤ M)
    (A₀ : ScottOpens (ScottOpens (IdealPoint cantorMeasure)))
    (hstart : (D ∩ (G cantorMeasure randomOpen M₀ ⁻¹'
      (A₀ : Set (WithScott (ScottOpens (IdealPoint cantorMeasure)))))).Nonempty) :
    (D ∩ (G cantorMeasure randomOpen M ⁻¹'
      (A₀ : Set (WithScott (ScottOpens (IdealPoint cantorMeasure)))))).Nonempty :=
  index_comparison randomOpen randomOpen_continuous randomPrefix randomPrefix_mono
    randomPrefix_isLUB randomPrefix_isCompact cantor_clopen_neighborhood
    (fun _ _ h => finite_clopen_between h) M₀ M hM hM₀
    (exceptionalNullIndex_hit D hD) A₀ hstart

/-- The carrier-index quantifier form used to prove arbitrary-union
preservation; this follows from the source-exact base-index wrapper above. -/
theorem source_index_comparison (D : Set Omega)
    (hD : PositiveCarrier parameterProbability D) :
    ∃ M₀ : NullIndex cantorMeasure, ∀ M, M₀ ≤ M →
      ∀ A₀ : ScottOpens (ScottOpens (IdealPoint cantorMeasure)),
        (D ∩ (G cantorMeasure randomOpen M₀ ⁻¹'
          (A₀ : Set (WithScott (ScottOpens (IdealPoint cantorMeasure)))))).Nonempty →
        (D ∩ (G cantorMeasure randomOpen M ⁻¹'
          (A₀ : Set (WithScott (ScottOpens (IdealPoint cantorMeasure)))))).Nonempty :=
  G_carrierIndexComparison randomOpen randomOpen_continuous randomPrefix randomPrefix_mono
    randomPrefix_isLUB randomPrefix_isCompact cantor_clopen_neighborhood
    (fun _ _ h => finite_clopen_between h) parameterProbability (fun _ h => hitting h) D hD

/-- The stabilized open event `ψ(𝒜)` in equation `eq:stabilized-event`. -/
noncomputable def paperPsi (A₀ : ScottOpens (ScottOpens (IdealPoint cantorMeasure))) : Opens Omega :=
  psi cantorMeasure randomOpen randomOpen_continuous A₀

@[simp] theorem mem_paperPsi (A₀ : ScottOpens (ScottOpens (IdealPoint cantorMeasure)))
    (t : Omega) : t ∈ paperPsi A₀ ↔
      ∀ M : NullIndex cantorMeasure, G cantorMeasure randomOpen M t ∈ A₀ := by
  change t ∈ limitPreimage (G cantorMeasure randomOpen) (A₀ : Set _) ↔ _
  constructor
  · intro ht M
    exact mem_iInter.mp ht M
  · intro ht
    exact mem_iInter.mpr ht

theorem paperPsi_eventually_eq (A₀ : ScottOpens (ScottOpens (IdealPoint cantorMeasure))) :
    ∃ M₀ : NullIndex cantorMeasure, ∀ M, M₀ ≤ M →
      G cantorMeasure randomOpen M ⁻¹'
        (A₀ : Set (WithScott (ScottOpens (IdealPoint cantorMeasure)))) =
          (paperPsi A₀ : Set Omega) :=
  psi_eventually_eq cantorMeasure randomOpen randomOpen_continuous A₀

theorem paperPsi_mono : Monotone paperPsi :=
  stabilizedEvent_mono (nullIndex_countablyBounded cantorMeasure)
    (G cantorMeasure randomOpen) (G_antitone cantorMeasure randomOpen)
    (G_continuous cantorMeasure randomOpen randomOpen_continuous)

@[simp] theorem paperPsi_bot : paperPsi ⊥ = ⊥ :=
  stabilizedEvent_bot (nullIndex_countablyBounded cantorMeasure)
    (G cantorMeasure randomOpen) (G_antitone cantorMeasure randomOpen)
    (G_continuous cantorMeasure randomOpen randomOpen_continuous)

@[simp] theorem paperPsi_top : paperPsi ⊤ = ⊤ :=
  stabilizedEvent_top (nullIndex_countablyBounded cantorMeasure)
    (G cantorMeasure randomOpen) (G_antitone cantorMeasure randomOpen)
    (G_continuous cantorMeasure randomOpen randomOpen_continuous)

theorem paperPsi_sup (A₀ B₀ : ScottOpens (ScottOpens (IdealPoint cantorMeasure))) :
    paperPsi (A₀ ⊔ B₀) = paperPsi A₀ ⊔ paperPsi B₀ :=
  stabilizedEvent_sup (nullIndex_countablyBounded cantorMeasure)
    (G cantorMeasure randomOpen) (G_antitone cantorMeasure randomOpen)
    (G_continuous cantorMeasure randomOpen randomOpen_continuous) A₀ B₀

theorem paperPsi_inf (A₀ B₀ : ScottOpens (ScottOpens (IdealPoint cantorMeasure))) :
    paperPsi (A₀ ⊓ B₀) = paperPsi A₀ ⊓ paperPsi B₀ :=
  stabilizedEvent_inf (nullIndex_countablyBounded cantorMeasure)
    (G cantorMeasure randomOpen) (G_antitone cantorMeasure randomOpen)
    (G_continuous cantorMeasure randomOpen randomOpen_continuous) A₀ B₀

/-- All assertions of source Lemma `lem:stabilization`, for the specified
Cantor random cylinder construction and the full collection of null sets. -/
theorem source_stabilization :
    (∀ A₀ : ScottOpens (ScottOpens (IdealPoint cantorMeasure)),
      ∃ M₀ : NullIndex cantorMeasure, ∀ M, M₀ ≤ M →
        G cantorMeasure randomOpen M ⁻¹'
          (A₀ : Set (WithScott (ScottOpens (IdealPoint cantorMeasure)))) =
            (paperPsi A₀ : Set Omega)) ∧
    Monotone paperPsi ∧ paperPsi ⊥ = ⊥ ∧ paperPsi ⊤ = ⊤ ∧
    (∀ A₀ B₀, paperPsi (A₀ ⊔ B₀) = paperPsi A₀ ⊔ paperPsi B₀) ∧
    (∀ A₀ B₀, paperPsi (A₀ ⊓ B₀) = paperPsi A₀ ⊓ paperPsi B₀) :=
  ⟨paperPsi_eventually_eq, paperPsi_mono, paperPsi_bot, paperPsi_top,
    paperPsi_sup, paperPsi_inf⟩

/-- The manuscript's actual second valuation, with no comparison or hitting
premise left to be discharged by its caller. -/
noncomputable def eta : Valuation (WithScott (ScottOpens (IdealPoint cantorMeasure))) :=
  etaFromHitting randomOpen randomOpen_continuous randomPrefix randomPrefix_mono
    randomPrefix_isLUB randomPrefix_isCompact cantor_clopen_neighborhood
    (fun _ _ h => finite_clopen_between h) parameterProbability (fun _ h => hitting h)

@[simp] theorem eta_apply (A₀ : ScottOpens (ScottOpens (IdealPoint cantorMeasure))) :
    eta A₀ = parameterProbability (paperPsi A₀ : Set Omega) := rfl

theorem eta_probability : eta.Probability :=
  etaFromHitting_probability randomOpen randomOpen_continuous randomPrefix randomPrefix_mono
    randomPrefix_isLUB randomPrefix_isCompact cantor_clopen_neighborhood
    (fun _ _ h => finite_clopen_between h) parameterProbability (fun _ h => hitting h)

/-- Public source-facing wrapper for Theorem `thm:eta`: continuity is for
arbitrary directed subsets of the full intrinsic Scott-open lattice. -/
theorem eta_continuous_probability : ScottContinuous eta.mass ∧ eta ⊤ = 1 :=
  ⟨eta.continuous, eta_probability⟩

theorem eta_directed_union {I : Type u} [Nonempty I]
    (A₀ : I → ScottOpens (ScottOpens (IdealPoint cantorMeasure)))
    (hA : Directed (· ≤ ·) A₀) : eta (⨆ i, A₀ i) = ⨆ i, eta (A₀ i) :=
  eta.map_iSup A₀ hA

/-- Each approximating source valuation is the pushforward under the
specified `G_M`, on the actual compact-metric parameter probability space. -/
noncomputable def etaStage (M : NullIndex cantorMeasure) :
    Valuation (WithScott (ScottOpens (IdealPoint cantorMeasure))) :=
  (radonValuation parameterProbability).push (G cantorMeasure randomOpen M)
    (G_continuous cantorMeasure randomOpen randomOpen_continuous M)

theorem etaStage_probability (M : NullIndex cantorMeasure) : (etaStage M).Probability :=
  (radonValuation_probability parameterProbability).push _ _

/-- The final printed infimum identity follows from exact stabilization,
with no exchange of iterated integrals. -/
theorem eta_eq_iInf_etaStage (A₀ : ScottOpens (ScottOpens (IdealPoint cantorMeasure))) :
    eta A₀ = ⨅ M : NullIndex cantorMeasure, etaStage M A₀ := by
  apply le_antisymm
  · apply le_iInf
    intro M
    apply measure_mono
    exact iInter_subset (fun N : NullIndex cantorMeasure =>
      G cantorMeasure randomOpen N ⁻¹'
        (A₀ : Set (WithScott (ScottOpens (IdealPoint cantorMeasure))))) M
  · obtain ⟨M₀, hM₀⟩ := paperPsi_eventually_eq A₀
    have he : etaStage M₀ A₀ = eta A₀ :=
      congrArg parameterProbability (hM₀ M₀ le_rfl)
    exact (iInf_le (fun M : NullIndex cantorMeasure => etaStage M A₀) M₀).trans he.le

/-- Source Proposition `prop:unions-ae` for genuinely arbitrary families. -/
theorem source_unions_ae {I : Type u}
    (A₀ : I → ScottOpens (ScottOpens (IdealPoint cantorMeasure))) :
    parameterProbability ((paperPsi (⨆ i, A₀ i) : Set Omega) \
      ⋃ i, (paperPsi (A₀ i) : Set Omega)) = 0 :=
  psi_arbitrary_union_defect_null randomOpen randomOpen_continuous randomPrefix randomPrefix_mono
    randomPrefix_isLUB randomPrefix_isCompact cantor_clopen_neighborhood
    (fun _ _ h => finite_clopen_between h) parameterProbability (fun _ h => hitting h) A₀

end CantorFubini
