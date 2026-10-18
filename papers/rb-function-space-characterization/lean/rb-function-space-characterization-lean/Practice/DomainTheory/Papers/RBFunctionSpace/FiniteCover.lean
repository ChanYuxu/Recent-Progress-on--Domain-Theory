import Practice.DomainTheory.Papers.RBFunctionSpace.Extraction
import Practice.DomainTheory.Papers.RBFunctionSpace.ExternalFacts

/-!
# Finite-cover extraction

This file formalizes `prop:finite-cover-extraction` and
`cor:pointed-test`.
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

universe u

namespace RBFunctionSpace

open Set
open AbramskyJung.Chapter2

variable {X : Type u} [PartialOrder X]

/-- A finite family of pairs `u ≪ v` whose `↑↑v` cover `X`. -/
structure FiniteRequirementCover (hX : IsDomain X) where
  pairs : Set (X × X)
  finite_pairs : pairs.Finite
  wayBelow_pairs : ∀ p ∈ pairs, p.1 ≪ p.2
  covers : ∀ x : X, ∃ p ∈ pairs, p.2 ≪ x

theorem K_mono {M N : Set X} (hMN : M ⊆ N) :
    K M ≤ K N := by
  intro x
  rw [EX.le_iff]
  exact ⟨hMN, le_rfl⟩

/-- The directed family of all finite constant upper-layer maps. -/
def KFamily : Set (AbramskyJung.Chapter3.ContFun X (EX X)) :=
  {f | ∃ M : Set X, M.Finite ∧ f = K M}

theorem KFamily_directed :
    DirectedSet (KFamily (X := X)) := by
  constructor
  · refine ⟨K ∅, ?_⟩
    exact ⟨∅, Set.finite_empty, rfl⟩
  · intro f hf g hg
    rcases hf with ⟨M, hMfinite, rfl⟩
    rcases hg with ⟨N, hNfinite, rfl⟩
    refine
      ⟨K (M ∪ N),
        ⟨M ∪ N, hMfinite.union hNfinite, rfl⟩,
        K_mono Set.subset_union_left,
        K_mono Set.subset_union_right⟩

/-- The constant top map. -/
def constantTop : AbramskyJung.Chapter3.ContFun X (EX X) :=
  K Set.univ

theorem KFamily_isSup :
    IsSup (KFamily (X := X)) (constantTop (X := X)) := by
  constructor
  · intro f hf
    rcases hf with ⟨M, _, rfl⟩
    exact K_mono (Set.subset_univ M)
  · intro z hz x
    rw [EX.le_iff]
    constructor
    · intro a _
      have hSingleton :
          K ({a} : Set X) ≤ z :=
        hz ⟨{a}, Set.finite_singleton a, rfl⟩
      exact
        (EX.le_iff.mp (hSingleton x)).1
          (by simp)
    · have hEmpty :
          K (∅ : Set X) ≤ z :=
        hz ⟨∅, Set.finite_empty, rfl⟩
      exact (EX.le_iff.mp (hEmpty x)).2

theorem Q_le_constantTop (hX : IsDomain X) :
    Q hX ≤ constantTop (X := X) :=
  fun _ => le_top

/-- Every function-space approximant `φ ≪ Q` is bounded by some `K_M`
with `M` finite. -/
theorem wayBelow_Q_bounded_by_finite_K
    (hX : IsDomain X)
    {φ : AbramskyJung.Chapter3.ContFun X (EX X)}
    (hφ : φ ≪ Q hX) :
    ∃ M : Set X, M.Finite ∧ φ ≤ K M := by
  rcases
      hφ KFamily_directed KFamily_isSup
        (Q_le_constantTop hX) with
    ⟨f, hf, hφf⟩
  rcases hf with ⟨M, hMfinite, rfl⟩
  exact ⟨M, hMfinite, hφf⟩

/-- `prop:finite-cover-extraction`. -/
theorem finiteCoverExtraction
    (hX : IsDomain X)
    (hFun : HasContinuousFunctionSpace X (EX X))
    (cover : FiniteRequirementCover hX) :
    IsRBDomain X := by
  classical
  let F := AbramskyJung.Chapter3.ContFun X (EX X)
  let belowQ : Set F := wayBelowLower (Q hX)
  have hBelowQDir : DirectedSet belowQ :=
    continuous_wayBelowLower_directed hFun.2 (Q hX)
  have hBelowQSup : IsSup belowQ (Q hX) :=
    continuous_wayBelowLower_isSup hFun.2 (Q hX)
  let req : X × X → F :=
    fun p => requirementStep hX p.1 p.2
  let requirements : Set F := req '' cover.pairs
  have hRequirementsFinite : requirements.Finite :=
    cover.finite_pairs.image req
  have hRequirementsSub : requirements ⊆ belowQ := by
    intro r hr
    rcases hr with ⟨p, hp, rfl⟩
    exact requirementStep_wayBelow_Q hX
      (cover.wayBelow_pairs p hp)
  rcases
      hBelowQDir.exists_upper_finite
        hRequirementsFinite hRequirementsSub with
    ⟨φ₀, hφ₀Below, hReqLeφ₀⟩
  let tail : Set F :=
    {φ | φ ∈ belowQ ∧ φ₀ ≤ φ}
  have hTailDirected : DirectedSet tail := by
    constructor
    · exact ⟨φ₀, hφ₀Below, le_rfl⟩
    · intro φ hφ ψ hψ
      rcases hBelowQDir.2 hφ.1 hψ.1 with
        ⟨χ, hχBelow, hφχ, hψχ⟩
      exact
        ⟨χ,
          ⟨hχBelow, le_trans hφ.2 hφχ⟩,
          hφχ,
          hψχ⟩
  have hTailCofinal :
      ∀ ψ ∈ belowQ, ∃ φ ∈ tail, ψ ≤ φ := by
    intro ψ hψBelow
    rcases hBelowQDir.2 hψBelow hφ₀Below with
      ⟨φ, hφBelow, hψφ, hφ₀φ⟩
    exact ⟨φ, ⟨hφBelow, hφ₀φ⟩, hψφ⟩
  have hExtractable :
      ∀ φ : F, φ ∈ tail → Nonempty (ExtractionData hX φ) := by
    intro φ hφTail
    rcases
        wayBelow_Q_bounded_by_finite_K hX hφTail.1 with
      ⟨M, hMfinite, hφK⟩
    refine
      ⟨{ finiteBound := M
         finite_finiteBound := hMfinite
         le_Q := fun x =>
           prop_2_2_2_1 hφTail.1 x
         le_K := hφK
         nonempty_B := ?_ }⟩
    intro x
    rcases cover.covers x with ⟨p, hpCover, hpWayBelow⟩
    refine ⟨p.1, ?_⟩
    have hReqMem : req p ∈ requirements := by
      change req p ∈ req '' cover.pairs
      exact ⟨p, hpCover, rfl⟩
    have hReqφ₀ : req p ≤ φ₀ :=
      hReqLeφ₀ (req p) hReqMem
    have hReqφ : req p ≤ φ :=
      le_trans hReqφ₀ hφTail.2
    have hpMem :
        p.1 ∈ EX.carrier (req p x) := by
      dsimp [req]
      simp [hpWayBelow, requirementValue]
    exact
      (EX.le_iff.mp (hReqφ x)).1 hpMem
  let data :
      ∀ i : {φ : F // φ ∈ tail}, ExtractionData hX i.1 :=
    fun i => Classical.choice (hExtractable i.1 i.2)
  let extracted :
      {φ : F // φ ∈ tail} → Deflation X :=
    fun i => (data i).deflation
  let deflations : Set (Deflation X) :=
    Set.range extracted
  have hDeflationsDirected : DirectedSet deflations := by
    constructor
    · rcases hTailDirected.1 with ⟨φ, hφTail⟩
      let i : {ψ : F // ψ ∈ tail} := ⟨φ, hφTail⟩
      exact ⟨extracted i, ⟨i, rfl⟩⟩
    · intro d hd e he
      rcases hd with ⟨i, rfl⟩
      rcases he with ⟨j, rfl⟩
      rcases hTailDirected.2 i.2 j.2 with
        ⟨χ, hχTail, hiχ, hjχ⟩
      let k : {ψ : F // ψ ∈ tail} := ⟨χ, hχTail⟩
      refine
        ⟨extracted k, ⟨k, rfl⟩, ?_, ?_⟩
      · exact ExtractionData.deflation_mono
          (data i) (data k) hiχ
      · exact ExtractionData.deflation_mono
          (data j) (data k) hjχ
  refine ⟨deflations, hDeflationsDirected, ?_⟩
  intro x
  constructor
  · intro y hy
    rcases hy with ⟨d, hd, rfl⟩
    rcases hd with ⟨i, rfl⟩
    exact (extracted i).below x
  · intro z hz
    apply (continuous_wayBelowLower_isSup hX.2.2 x).2
    intro u hu
    rcases wayBelow_interpolation hX.2.2 hu with
      ⟨v, huv, hvx⟩
    have hReqBelow :
        requirementStep hX u v ∈ belowQ :=
      requirementStep_wayBelow_Q hX huv
    rcases hTailCofinal
        (requirementStep hX u v) hReqBelow with
      ⟨φ, hφTail, hReqφ⟩
    let i : {ψ : F // ψ ∈ tail} := ⟨φ, hφTail⟩
    have huReq :
        u ∈ EX.carrier (requirementStep hX u v x) := by
      simp [requirementStep_apply, hvx, requirementValue]
    have huB : u ∈ B φ x :=
      (EX.le_iff.mp (hReqφ x)).1 huReq
    have huPoint : u ≤ (data i).point x :=
      (data i).point_greatest x huB
    have hExtractedImage :
        extracted i x ∈
          (fun d : Deflation X => d x) '' deflations := by
      exact ⟨extracted i, ⟨i, rfl⟩, rfl⟩
    exact le_trans huPoint (hz hExtractedImage)

theorem bottom_compact
    [OrderBot X] :
    Compact (⊥ : X) := by
  intro A s hA _ _
  rcases hA.1 with ⟨a, haA⟩
  exact ⟨a, haA, bot_le⟩

/-- `cor:pointed-test`. -/
theorem pointedTest
    [OrderBot X]
    (hX : IsDomain X) :
    HasContinuousFunctionSpace X (EX X) ↔ IsRBDomain X := by
  constructor
  · intro hFun
    let cover : FiniteRequirementCover hX :=
      { pairs := {((⊥ : X), (⊥ : X))}
        finite_pairs := Set.finite_singleton _
        wayBelow_pairs := by
          intro p hp
          have hpEq : p = ((⊥ : X), (⊥ : X)) := by
            simpa using hp
          subst p
          exact bottom_compact
        covers := by
          intro x
          refine ⟨((⊥ : X), (⊥ : X)), by simp, ?_⟩
          exact prop_2_2_2_2 le_rfl bottom_compact bot_le }
    exact finiteCoverExtraction hX hFun cover
  · intro hRB
    exact rb_functionSpace_continuous hX EX.isDomain hRB

end RBFunctionSpace
