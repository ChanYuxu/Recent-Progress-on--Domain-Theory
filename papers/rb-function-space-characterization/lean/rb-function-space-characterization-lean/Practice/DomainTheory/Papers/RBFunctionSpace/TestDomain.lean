import Practice.DomainTheory.Papers.RBFunctionSpace.Basic

/-!
# The algebraic test domain `E_X`

This file formalizes `lem:EX-algebraic`.  The lower layer contains precisely
the empty set and directed subsets of `X`; the upper layer contains arbitrary
subsets.  Both layers are ordered by inclusion, with the lower layer below the
upper layer.
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

universe u

namespace RBFunctionSpace

open Set
open AbramskyJung.Chapter2

def DirectedOrEmpty {α : Type u} [Preorder α] (A : Set α) : Prop :=
  A = ∅ ∨ DirectedSet A

/-- The manuscript's two-layer test poset `E_X`. -/
def EX (X : Type u) [Preorder X] :=
  {p : Set X × Bool // p.2 = false → DirectedOrEmpty p.1}

namespace EX

variable {X : Type u} [Preorder X]

instance : PartialOrder (EX X) :=
  inferInstanceAs
    (PartialOrder
      {p : Set X × Bool // p.2 = false → DirectedOrEmpty p.1})

def carrier (e : EX X) : Set X :=
  e.1.1

def layer (e : EX X) : Bool :=
  e.1.2

def lower (A : Set X) (hA : DirectedOrEmpty A) : EX X :=
  ⟨(A, false), fun _ => hA⟩

def upper (A : Set X) : EX X :=
  ⟨(A, true), by simp⟩

@[simp] theorem carrier_lower (A : Set X) (hA : DirectedOrEmpty A) :
    carrier (lower A hA) = A := rfl

@[simp] theorem carrier_upper (A : Set X) :
    carrier (upper A) = A := rfl

@[simp] theorem layer_lower (A : Set X) (hA : DirectedOrEmpty A) :
    layer (lower A hA) = false := rfl

@[simp] theorem layer_upper (A : Set X) :
    layer (upper A) = true := rfl

theorem valid_lower (e : EX X) (h : layer e = false) :
    DirectedOrEmpty (carrier e) :=
  e.2 h

theorem le_iff {e f : EX X} :
    e ≤ f ↔ carrier e ⊆ carrier f ∧ layer e ≤ layer f :=
  Iff.rfl

@[ext]
theorem ext {e f : EX X}
    (hcarrier : carrier e = carrier f)
    (hlayer : layer e = layer f) : e = f := by
  apply Subtype.ext
  exact Prod.ext hcarrier hlayer

def bottom : EX X :=
  lower ∅ (Or.inl rfl)

def top : EX X :=
  upper Set.univ

instance : OrderBot (EX X) where
  bot := bottom
  bot_le e := by
    rw [le_iff]
    refine ⟨Set.empty_subset _, ?_⟩
    exact Bool.false_le _

instance : OrderTop (EX X) where
  top := top
  le_top e := by
    rw [le_iff]
    refine ⟨Set.subset_univ _, ?_⟩
    exact Bool.le_true _

@[simp] theorem carrier_bot : carrier (⊥ : EX X) = ∅ := rfl
@[simp] theorem layer_bot : layer (⊥ : EX X) = false := rfl
@[simp] theorem carrier_top : carrier (⊤ : EX X) = Set.univ := rfl
@[simp] theorem layer_top : layer (⊤ : EX X) = true := rfl

def carrierUnion (𝒟 : Set (EX X)) : Set X :=
  ⋃ e : 𝒟, carrier e.1

def HasUpperLayer (𝒟 : Set (EX X)) : Prop :=
  ∃ e ∈ 𝒟, layer e = true

private theorem layer_false_of_not_hasUpper
    {𝒟 : Set (EX X)} (h : ¬ HasUpperLayer 𝒟)
    {e : EX X} (he : e ∈ 𝒟) :
    layer e = false := by
  cases htag : layer e with
  | false => rfl
  | true => exact (h ⟨e, he, htag⟩).elim

private theorem carrierUnion_directedOrEmpty
    {𝒟 : Set (EX X)} (h𝒟 : DirectedSet 𝒟)
    (hUpper : ¬ HasUpperLayer 𝒟) :
    DirectedOrEmpty (carrierUnion 𝒟) := by
  by_cases hEmpty : carrierUnion 𝒟 = ∅
  · exact Or.inl hEmpty
  · right
    constructor
    · exact Set.nonempty_iff_ne_empty.mpr hEmpty
    · intro a ha b hb
      change a ∈ ⋃ e : 𝒟, carrier e.1 at ha
      change b ∈ ⋃ e : 𝒟, carrier e.1 at hb
      rw [Set.mem_iUnion] at ha hb
      rcases ha with ⟨e, hae⟩
      rcases hb with ⟨f, hbf⟩
      rcases h𝒟.2 e.2 f.2 with ⟨g, hg𝒟, heg, hfg⟩
      have hag : a ∈ carrier g := (le_iff.mp heg).1 hae
      have hbg : b ∈ carrier g := (le_iff.mp hfg).1 hbf
      have hgValid :
          DirectedOrEmpty (carrier g) :=
        valid_lower g (layer_false_of_not_hasUpper hUpper hg𝒟)
      rcases hgValid with hgEmpty | hgDir
      · rw [hgEmpty] at hag
        exact False.elim (by simpa using hag)
      · rcases hgDir.2 hag hbg with ⟨c, hcg, hac, hbc⟩
        refine ⟨c, ?_, hac, hbc⟩
        change c ∈ ⋃ e : 𝒟, carrier e.1
        rw [Set.mem_iUnion]
        exact ⟨⟨g, hg𝒟⟩, hcg⟩

noncomputable def directedSup
    (𝒟 : Set (EX X)) (h𝒟 : DirectedSet 𝒟) : EX X := by
  classical
  exact
    if hUpper : HasUpperLayer 𝒟 then
      upper (carrierUnion 𝒟)
    else
      lower (carrierUnion 𝒟)
        (carrierUnion_directedOrEmpty h𝒟 hUpper)

@[simp]
theorem carrier_directedSup
    (𝒟 : Set (EX X)) (h𝒟 : DirectedSet 𝒟) :
    carrier (directedSup 𝒟 h𝒟) = carrierUnion 𝒟 := by
  unfold directedSup
  split <;> rfl

theorem layer_directedSup_eq_true_iff
    (𝒟 : Set (EX X)) (h𝒟 : DirectedSet 𝒟) :
    layer (directedSup 𝒟 h𝒟) = true ↔ HasUpperLayer 𝒟 := by
  unfold directedSup
  split <;> simp_all

theorem directedSup_isSup
    (𝒟 : Set (EX X)) (h𝒟 : DirectedSet 𝒟) :
    IsSup 𝒟 (directedSup 𝒟 h𝒟) := by
  constructor
  · intro e he
    rw [le_iff]
    constructor
    · intro x hx
      rw [carrier_directedSup]
      change x ∈ ⋃ f : 𝒟, carrier f.1
      rw [Set.mem_iUnion]
      exact ⟨⟨e, he⟩, hx⟩
    · unfold directedSup
      split
      · simp
      · have heFalse := layer_false_of_not_hasUpper ‹¬ HasUpperLayer 𝒟› he
        simp [heFalse]
  · intro z hz
    rw [le_iff]
    constructor
    · rw [carrier_directedSup]
      intro x hx
      change x ∈ ⋃ e : 𝒟, carrier e.1 at hx
      rw [Set.mem_iUnion] at hx
      rcases hx with ⟨e, hxe⟩
      exact (le_iff.mp (hz e.2)).1 hxe
    · by_cases hUpper : HasUpperLayer 𝒟
      · rw [(layer_directedSup_eq_true_iff 𝒟 h𝒟).2 hUpper]
        rcases hUpper with ⟨e, he, heUpper⟩
        have hez := (le_iff.mp (hz he)).2
        simpa [heUpper] using hez
      · have hLayer :
            layer (directedSup 𝒟 h𝒟) = false := by
          cases htag : layer (directedSup 𝒟 h𝒟)
          · rfl
          · exact
              (hUpper
                ((layer_directedSup_eq_true_iff 𝒟 h𝒟).1 htag)).elim
        simp [hLayer]

theorem isDcpoOrder : IsDcpoOrder (EX X) := by
  constructor
  · intro 𝒟 h𝒟
    exact ⟨directedSup 𝒟 h𝒟, directedSup_isSup 𝒟 h𝒟⟩
  · intro e f hef hfe
    exact le_antisymm hef hfe

private theorem exists_member_covering_finite
    {𝒟 : Set (EX X)} (h𝒟 : DirectedSet 𝒟)
    {F : Set X} (hFfinite : F.Finite)
    (hFsub : F ⊆ carrierUnion 𝒟) :
    ∃ e ∈ 𝒟, F ⊆ carrier e := by
  induction F, hFfinite using Set.Finite.induction_on with
  | empty =>
      rcases h𝒟.1 with ⟨e, he⟩
      exact ⟨e, he, Set.empty_subset _⟩
  | @insert a F haF hFfinite ih =>
      have haUnion : a ∈ carrierUnion 𝒟 :=
        hFsub (by simp)
      change a ∈ ⋃ e : 𝒟, carrier e.1 at haUnion
      rw [Set.mem_iUnion] at haUnion
      rcases haUnion with ⟨ea, hea⟩
      have hFsub' : F ⊆ carrierUnion 𝒟 := by
        intro x hx
        exact hFsub (by simp [hx])
      rcases ih hFsub' with ⟨eF, heF, hFeF⟩
      rcases h𝒟.2 ea.2 heF with ⟨g, hg, heag, heFg⟩
      refine ⟨g, hg, ?_⟩
      intro x hx
      rcases Set.mem_insert_iff.mp hx with rfl | hxF
      · exact (le_iff.mp heag).1 hea
      · exact (le_iff.mp heFg).1 (hFeF hxF)

theorem compact_lower
    {F : Set X} (hFvalid : DirectedOrEmpty F)
    (hFfinite : F.Finite) :
    Compact (lower F hFvalid) := by
  intro 𝒟 s h𝒟 hs hle
  have hsEq : s = directedSup 𝒟 h𝒟 :=
    IsSup.unique hs (directedSup_isSup 𝒟 h𝒟)
  subst s
  have hFsub : F ⊆ carrierUnion 𝒟 := by
    intro x hx
    have hmem := (le_iff.mp hle).1 hx
    simpa only [carrier_directedSup] using hmem
  rcases exists_member_covering_finite h𝒟 hFfinite hFsub with
    ⟨e, he, hFe⟩
  refine ⟨e, he, ?_⟩
  rw [le_iff]
  exact ⟨hFe, by simp⟩

theorem compact_upper
    {F : Set X} (hFfinite : F.Finite) :
    Compact (upper F) := by
  intro 𝒟 s h𝒟 hs hle
  have hsEq : s = directedSup 𝒟 h𝒟 :=
    IsSup.unique hs (directedSup_isSup 𝒟 h𝒟)
  subst s
  have hUpper : HasUpperLayer 𝒟 := by
    apply (layer_directedSup_eq_true_iff 𝒟 h𝒟).1
    have htag := (le_iff.mp hle).2
    cases hsLayer : layer (directedSup 𝒟 h𝒟) with
    | false =>
        have htag' : true ≤ false := by
          simpa only [layer_upper, hsLayer] using htag
        exact le_antisymm (Bool.false_le true) htag'
    | true => rfl
  rcases hUpper with ⟨e₀, he₀, he₀Upper⟩
  have hFsub : F ⊆ carrierUnion 𝒟 := by
    intro x hx
    have hmem := (le_iff.mp hle).1 hx
    simpa only [carrier_directedSup] using hmem
  rcases exists_member_covering_finite h𝒟 hFfinite hFsub with
    ⟨eF, heF, hFeF⟩
  rcases h𝒟.2 he₀ heF with ⟨g, hg, he₀g, heFg⟩
  refine ⟨g, hg, ?_⟩
  rw [le_iff]
  constructor
  · exact fun x hx => (le_iff.mp heFg).1 (hFeF hx)
  · have htag := (le_iff.mp he₀g).2
    simpa [he₀Upper] using htag

theorem compact_of_finite_carrier
    (e : EX X) (hfinite : (carrier e).Finite) :
    Compact e := by
  cases htag : layer e with
  | false =>
      have hEq : e = lower (carrier e) (valid_lower e htag) := by
        apply ext <;> simp [htag]
      rw [hEq]
      exact compact_lower (valid_lower e htag) hfinite
  | true =>
      have hEq : e = upper (carrier e) := by
        apply ext <;> simp [htag]
      rw [hEq]
      exact compact_upper hfinite

def lowerApproximants (e : EX X) : Set (EX X) :=
  {k | layer k = false ∧ (carrier k).Finite ∧ k ≤ e}

def upperApproximants (e : EX X) : Set (EX X) :=
  {k | layer k = true ∧ (carrier k).Finite ∧ k ≤ e}

private theorem lowerApproximants_directed
    (e : EX X) (heLayer : layer e = false) :
    DirectedSet (lowerApproximants e) := by
  have heValid := valid_lower e heLayer
  constructor
  · refine ⟨⊥, ?_⟩
    exact ⟨rfl, Set.finite_empty, bot_le⟩
  · intro k hk l hl
    rcases heValid with heEmpty | heDirected
    · have hkBot : k ≤ (⊥ : EX X) := by
        rw [le_iff]
        constructor
        · intro x hx
          have hxe : x ∈ carrier e := (le_iff.mp hk.2.2).1 hx
          simpa [heEmpty] using hxe
        · simpa [hk.1]
      have hlBot : l ≤ (⊥ : EX X) := by
        rw [le_iff]
        constructor
        · intro x hx
          have hxe : x ∈ carrier e := (le_iff.mp hl.2.2).1 hx
          simpa [heEmpty] using hxe
        · simpa [hl.1]
      exact ⟨⊥, ⟨rfl, Set.finite_empty, bot_le⟩, hkBot, hlBot⟩
    · let F₀ : Set X := carrier k ∪ carrier l
      have hF₀finite : F₀.Finite := hk.2.1.union hl.2.1
      have hF₀sub : F₀ ⊆ carrier e := by
        exact Set.union_subset
          (le_iff.mp hk.2.2).1
          (le_iff.mp hl.2.2).1
      rcases heDirected.exists_upper_finite hF₀finite hF₀sub with
        ⟨z, hze, hzUpper⟩
      let F : Set X := F₀ ∪ {z}
      have hFfinite : F.Finite :=
        hF₀finite.union (Set.finite_singleton z)
      have hFdir : DirectedSet F := by
        constructor
        · exact ⟨z, by simp [F]⟩
        · intro a ha b hb
          refine ⟨z, by simp [F], ?_, ?_⟩
          · rcases ha with haF₀ | rfl
            · exact hzUpper a haF₀
            · exact le_rfl
          · rcases hb with hbF₀ | rfl
            · exact hzUpper b hbF₀
            · exact le_rfl
      let m : EX X := lower F (Or.inr hFdir)
      refine ⟨m, ?_, ?_, ?_⟩
      · refine ⟨rfl, hFfinite, ?_⟩
        rw [le_iff]
        constructor
        · intro x hx
          rcases hx with hxF₀ | hxz
          · exact hF₀sub hxF₀
          · have hxEq : x = z := by simpa using hxz
            simpa [hxEq] using hze
        · have hmLayer : layer m = false := rfl
          rw [hmLayer, heLayer]
      · rw [le_iff]
        exact ⟨fun x hx => Or.inl (Or.inl hx), by simp [hk.1]⟩
      · rw [le_iff]
        exact ⟨fun x hx => Or.inl (Or.inr hx), by simp [hl.1]⟩

private theorem lowerApproximants_isSup
    (e : EX X) (heLayer : layer e = false) :
    IsSup (lowerApproximants e) e := by
  constructor
  · intro k hk
    exact hk.2.2
  · intro z hz
    rw [le_iff]
    constructor
    · intro x hxe
      let k : EX X :=
        lower ({x} : Set X) (Or.inr (directed_singleton x))
      have hk : k ∈ lowerApproximants e := by
        refine ⟨rfl, Set.finite_singleton x, ?_⟩
        rw [le_iff]
        refine ⟨by simpa [k] using hxe, ?_⟩
        have hkLayer : layer k = false := rfl
        rw [hkLayer, heLayer]
      exact (le_iff.mp (hz hk)).1 (by simp [k])
    · simp [heLayer]

private theorem upperApproximants_directed
    (e : EX X) (heLayer : layer e = true) :
    DirectedSet (upperApproximants e) := by
  constructor
  · refine ⟨upper ∅, ?_⟩
    refine ⟨rfl, Set.finite_empty, ?_⟩
    rw [le_iff]
    exact ⟨Set.empty_subset _, by simp [heLayer]⟩
  · intro k hk l hl
    let m : EX X := upper (carrier k ∪ carrier l)
    refine ⟨m, ?_, ?_, ?_⟩
    · refine ⟨rfl, hk.2.1.union hl.2.1, ?_⟩
      rw [le_iff]
      exact
        ⟨Set.union_subset
            (le_iff.mp hk.2.2).1
            (le_iff.mp hl.2.2).1,
          by simp [heLayer]⟩
    · rw [le_iff]
      refine ⟨Set.subset_union_left, ?_⟩
      have hmLayer : layer m = true := rfl
      rw [hk.1, hmLayer]
    · rw [le_iff]
      refine ⟨Set.subset_union_right, ?_⟩
      have hmLayer : layer m = true := rfl
      rw [hl.1, hmLayer]

private theorem upperApproximants_isSup
    (e : EX X) (heLayer : layer e = true) :
    IsSup (upperApproximants e) e := by
  constructor
  · intro k hk
    exact hk.2.2
  · intro z hz
    rw [le_iff]
    constructor
    · intro x hxe
      let k : EX X := upper ({x} : Set X)
      have hk : k ∈ upperApproximants e := by
        refine ⟨rfl, Set.finite_singleton x, ?_⟩
        rw [le_iff]
        exact ⟨by simpa [k] using hxe, by simp [heLayer]⟩
      exact (le_iff.mp (hz hk)).1 (by simp [k])
    · have hEmpty :
          upper (∅ : Set X) ∈ upperApproximants e := by
        refine ⟨rfl, Set.finite_empty, ?_⟩
        rw [le_iff]
        exact ⟨Set.empty_subset _, by simp [heLayer]⟩
      have htag := (le_iff.mp (hz hEmpty)).2
      rw [heLayer]
      exact htag

/-- `lem:EX-algebraic`: the displayed finite lower and upper elements are
compact and form a basis. -/
theorem algebraicDomain : IsAlgebraicDomain (EX X) := by
  intro e
  cases htag : layer e with
  | false =>
      refine
        ⟨lowerApproximants e,
          ?_,
          lowerApproximants_directed e htag,
          lowerApproximants_isSup e htag⟩
      intro k hk
      have hkCompact := compact_of_finite_carrier k hk.2.1
      exact
        ⟨hkCompact,
          prop_2_2_2_2 le_rfl hkCompact hk.2.2⟩
  | true =>
      refine
        ⟨upperApproximants e,
          ?_,
          upperApproximants_directed e htag,
          upperApproximants_isSup e htag⟩
      intro k hk
      have hkCompact := compact_of_finite_carrier k hk.2.1
      exact
        ⟨hkCompact,
          prop_2_2_2_2 le_rfl hkCompact hk.2.2⟩

theorem algebraicDcpo : IsAlgebraicDcpo (EX X) :=
  ⟨isDcpoOrder, algebraicDomain⟩

theorem isDomain : IsDomain (EX X) :=
  ⟨⟨⊥⟩, isDcpoOrder,
    ⟨CompactSet, algebraicDomain⟩⟩

theorem bottom_isLeast : IsLeast Set.univ (⊥ : EX X) :=
  ⟨Set.mem_univ _, fun _ _ => bot_le⟩

theorem top_isGreatest : IsGreatest Set.univ (⊤ : EX X) :=
  ⟨Set.mem_univ _, fun _ _ => le_top⟩

end EX

end RBFunctionSpace
