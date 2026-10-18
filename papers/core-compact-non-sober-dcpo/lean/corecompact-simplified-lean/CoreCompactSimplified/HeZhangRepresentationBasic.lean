import CoreCompactSimplified.HeZhangLawson
import CoreCompactSimplified.HeZhangClosed
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Sets.Closeds

/-!
The compact metrizable representation used in the proof of He--Zhang
Theorem 4.13, arXiv:2610.17759v1.

`closedLawsonTopology` is the literal pullback along complementation, not
the intrinsic Scott topology on the closed-set lattice. `principal` is the
specified map x ↦ ↓x. `hitting K` is exactly Q_K, and `diamond U` is exactly
the displayed Diamond U. Source Claim 4 is proved on these actual objects.
-/

set_option autoImplicit false

universe u

namespace CoreCompactSimplified.HeZhangRepresentation

open Set TopologicalSpace CoreCompactNonSober HeZhangLawson
open scoped Topology

noncomputable section

variable {P : Type u} [PartialOrder P]

local instance scottTopologyP : TopologicalSpace P := scottTopology P
local instance scottInstanceP : Topology.IsScott P univ := ⟨rfl⟩

/-- The actual complementation bijection c in the source. -/
def closedComplementEquiv (P : Type u) [PartialOrder P] : ScottCloseds P ≃ ScottOpens P where
  toFun := Closeds.compl
  invFun := Opens.compl
  left_inv := Closeds.compl_compl
  right_inv := Opens.compl_compl

/-- The source's tau = c⁻¹(Lawson topology of Scott opens). -/
@[implicit_reducible] def closedLawsonTopology (P : Type u) [PartialOrder P] :
    TopologicalSpace (ScottCloseds P) :=
  TopologicalSpace.induced (closedComplementEquiv P) (Topology.lawson (ScottOpens P))

local instance opensLawsonTopologyP : TopologicalSpace (ScottOpens P) :=
  Topology.lawson (ScottOpens P)
local instance closedLawsonTopologyP : TopologicalSpace (ScottCloseds P) :=
  closedLawsonTopology P

def closedComplementHomeomorph (P : Type u) [PartialOrder P] :
    ScottCloseds P ≃ₜ ScottOpens P :=
  (closedComplementEquiv P).toHomeomorphOfIsInducing ⟨rfl⟩

theorem closedComplement_le_iff (A B : ScottCloseds P) :
    closedComplementEquiv P A ≤ closedComplementEquiv P B ↔ B ≤ A :=
  compl_subset_compl

theorem closedLawson_compact_hausdorff_metrizable
    (hcore : ScottCoreCompact P) (hsecond : ScottSecondCountable P) :
    CompactSpace (ScottCloseds P) ∧ T2Space (ScottCloseds P) ∧
      SecondCountableTopology (ScottCloseds P) ∧ MetrizableSpace (ScottCloseds P) := by
  letI : SecondCountableTopology P := hsecond
  obtain ⟨hc, ht, hs, hm⟩ := opensLawson_compact_hausdorff_metrizable hcore
  letI : CompactSpace (ScottOpens P) := hc
  letI : T2Space (ScottOpens P) := ht
  letI : SecondCountableTopology (ScottOpens P) := hs
  letI : MetrizableSpace (ScottOpens P) := hm
  let c := closedComplementHomeomorph P
  exact ⟨c.symm.compactSpace, c.symm.t2Space, c.secondCountableTopology,
    c.isEmbedding.metrizableSpace⟩

/-- The closed order on M is transported with its direction reversed under c. -/
theorem closedLawson_orderClosed (hcore : ScottCoreCompact P) :
    OrderClosedTopology (ScottCloseds P) := by
  letI : OrderClosedTopology (ScottOpens P) :=
    lawson_orderClosed (coreCompact_iff_continuous_opens.mp hcore)
  let c := closedComplementHomeomorph P
  constructor
  have hclosed := isClosed_le (c.continuous.comp continuous_snd)
    (c.continuous.comp continuous_fst)
  have heq : {p : ScottCloseds P × ScottCloseds P | c p.2 ≤ c p.1} =
      {p | p.1 ≤ p.2} := by
    ext p
    exact closedComplement_le_iff p.2 p.1
  change IsClosed {p : ScottCloseds P × ScottCloseds P | c p.2 ≤ c p.1} at hclosed
  rwa [heq] at hclosed

/-- The specified order embedding eta(x) = ↓x. -/
def principal : P ↪o ScottCloseds P where
  toFun x := ⟨Iic x, isClosed_Iic⟩
  inj' := by
    intro x y h
    exact Iic_injective (congrArg (fun A : ScottCloseds P ↦ (A : Set P)) h)
  map_rel_iff' := by
    intro x y
    exact ⟨fun h ↦ h le_rfl, fun h z hz ↦ hz.trans h⟩

@[simp] theorem mem_principal (x y : P) : y ∈ principal x ↔ y ≤ x := Iff.rfl

def diamond (U : ScottOpens P) : Set (ScottCloseds P) :=
  {A | ((A : Set P) ∩ (U : Set P)).Nonempty}

theorem diamond_eq_preimage_compl_Ici (U : ScottOpens P) :
    diamond U = closedComplementEquiv P ⁻¹' (Ici U)ᶜ := by
  classical
  ext A
  change ((A : Set P) ∩ (U : Set P)).Nonempty ↔ ¬U ≤ A.compl
  constructor
  · rintro ⟨x, hxA, hxU⟩ h
    exact h hxU hxA
  · intro h
    by_contra hn
    apply h
    intro x hxU hxA
    exact hn ⟨x, hxA, hxU⟩

theorem diamond_isOpen (U : ScottOpens P) : IsOpen (diamond U) := by
  rw [diamond_eq_preimage_compl_Ici]
  exact (isOpen_compl_Ici_lawson U).preimage (closedComplementHomeomorph P).continuous

theorem principal_preimage_diamond (U : ScottOpens P) : principal ⁻¹' diamond U = U := by
  ext x
  constructor
  · rintro ⟨y, hyx, hyU⟩
    exact ((isOpen_scott_iff _).mp U.isOpen).1 hyx hyU
  · intro hx
    exact ⟨x, le_rfl, hx⟩

def hitting (K : Set P) : Set (ScottCloseds P) :=
  {A | ((A : Set P) ∩ K).Nonempty}

def compactContainingOpens (K : Set P) : Set (ScottOpens P) :=
  {U | K ⊆ (U : Set P)}

/-- Compactness of K makes Phi(K) Scott-open in the complete lattice of opens. -/
theorem compactContainingOpens_isScottOpen {K : Set P} (hK : IsCompact K) :
    @IsOpen (ScottOpens P) (Topology.scott (ScottOpens P) univ)
      (compactContainingOpens K) := by
  apply (isOpen_scott_iff _).mpr
  constructor
  · intro U V hUV hKU
    exact fun x hx ↦ hUV (hKU hx)
  · intro E hE U hU hKU
    letI : Nonempty E := hE.1.to_subtype
    have hcover : K ⊆ ⋃ e : E, (e.val : Set P) := by
      intro x hxK
      have hxU : x ∈ sSup E := by
        rw [(isLUB_sSup E).unique hU]
        exact hKU hxK
      obtain ⟨V, hVE, hxV⟩ := Opens.mem_sSup.mp hxU
      exact mem_iUnion.mpr ⟨⟨V, hVE⟩, hxV⟩
    have hdir : Directed (· ⊆ ·) (fun e : E ↦ (e.val : Set P)) := by
      intro a b
      obtain ⟨c, hc, hac, hbc⟩ := hE.2 a.val a.property b.val b.property
      exact ⟨⟨c, hc⟩, hac, hbc⟩
    obtain ⟨e, hKe⟩ := hK.elim_directed_cover (fun e : E ↦ (e.val : Set P))
      (fun e ↦ e.val.isOpen) hcover hdir
    exact ⟨e.val, e.property, hKe⟩

theorem compl_hitting_eq_preimage_containing (K : Set P) :
    (hitting K)ᶜ = closedComplementEquiv P ⁻¹' compactContainingOpens K := by
  classical
  ext A
  change ¬((A : Set P) ∩ K).Nonempty ↔ K ⊆ (A.compl : Set P)
  constructor
  · intro h x hxK hxA
    exact h ⟨x, hxA, hxK⟩
  · intro h ⟨x, hxA, hxK⟩
    exact h hxK hxA

theorem hitting_isClosed {K : Set P} (hK : IsCompact K) : IsClosed (hitting K) := by
  apply isOpen_compl_iff.mp
  rw [compl_hitting_eq_preimage_containing]
  exact (Topology.lawson_le_scott _ (compactContainingOpens_isScottOpen hK)).preimage
    (closedComplementHomeomorph P).continuous

theorem hitting_isCompact (hcore : ScottCoreCompact P) (hsecond : ScottSecondCountable P)
    {K : Set P} (hK : IsCompact K) : IsCompact (hitting K) := by
  letI : CompactSpace (ScottCloseds P) :=
    (closedLawson_compact_hausdorff_metrizable hcore hsecond).1
  exact (hitting_isClosed hK).isCompact

theorem principal_le_closed_iff (x : P) (A : ScottCloseds P) :
    principal x ≤ A ↔ x ∈ A := by
  constructor
  · intro h
    exact h le_rfl
  · intro h y hyx
    exact ((isClosed_scott_iff _).mp A.isClosed).1 hyx h

/-- Source Claim 4, on the actual Q_K and the actual eta. -/
theorem minimal_hitting_iff {K : Set P} (A : ScottCloseds P) :
    Minimal (· ∈ hitting K) A ↔
      ∃ k : P, Minimal (· ∈ K) k ∧ principal k = A := by
  constructor
  · intro hA
    obtain ⟨k, hkA, hkK⟩ := hA.1
    have hkQ : principal k ∈ hitting K := ⟨k, le_rfl, hkK⟩
    have heq : A = principal k := hA.eq_of_ge hkQ ((principal_le_closed_iff _ _).mpr hkA)
    refine ⟨k, ?_, heq.symm⟩
    apply minimal_iff.mpr
    refine ⟨hkK, ?_⟩
    intro b hbK hbk
    have hbQ : principal b ∈ hitting K := ⟨b, le_rfl, hbK⟩
    have heqb : A = principal b := hA.eq_of_ge hbQ
      ((principal.monotone hbk).trans (le_of_eq heq.symm))
    exact principal.injective (heq.symm.trans heqb)
  · rintro ⟨k, hk, rfl⟩
    apply minimal_iff.mpr
    refine ⟨⟨k, le_rfl, hk.1⟩, ?_⟩
    intro B hBQ hBk
    obtain ⟨b, hbB, hbK⟩ := hBQ
    have hbk : b ≤ k := hBk hbB
    have hkb : k = b := hk.eq_of_ge hbK hbk
    apply le_antisymm
    · exact (principal_le_closed_iff _ _).mpr (hkb ▸ hbB)
    · exact hBk

theorem minimal_hitting_eq_image (K : Set P) :
    {A : ScottCloseds P | Minimal (· ∈ hitting K) A} =
      principal '' {k : P | Minimal (· ∈ K) k} := by
  ext A
  exact minimal_hitting_iff A

end

end CoreCompactSimplified.HeZhangRepresentation
