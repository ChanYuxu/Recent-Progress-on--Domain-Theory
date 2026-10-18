import FiniteValuationApproximable.Abstract.FSClass

/-!
# Internal proof of closure of FS-domains under exponentials

This module formalizes the proof of Gierz et al., *Continuous Lattices and
Domains*, Proposition II-2.18.  Given directed FS approximate identities on
`S` and `T`, the proof uses the squares of the sandwich maps
`f ↦ b ∘ f ∘ a`.  Finite separation is obtained by the finite relation
signature from the published proof.
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

universe u v w

namespace FiniteValuationApproximable
namespace GierzInternal

open Set
open AbstractApproximation

abbrev DirectedSet {X : Type u} [Preorder X] (A : Set X) : Prop :=
  AbramskyJung.Chapter2.DirectedSet A

abbrev IsSup {X : Type u} [Preorder X] (A : Set X) (x : X) : Prop :=
  AbramskyJung.Chapter2.IsSup A x

abbrev IsDcpo (X : Type u) [Preorder X] : Prop :=
  AbramskyJung.Chapter2.IsDcpo X

abbrev ScottContinuous
    {X : Type u} {Y : Type v} [Preorder X] [Preorder Y]
    (f : X → Y) : Prop :=
  AbramskyJung.Chapter2.ScottContinuous f

abbrev ContFun (X : Type u) (Y : Type v) [Preorder X] [Preorder Y] :=
  AbramskyJung.Chapter3.ContFun X Y

section Composition

variable {A : Type u} {B : Type v} {C : Type w}
variable [Preorder A] [Preorder B] [Preorder C]

private def precompose (k : ContFun A B) : ContFun B C → ContFun A C :=
  fun g ↦ AbramskyJung.Chapter3.ContFun.comp g k

private def postcompose (k : ContFun B C) : ContFun A B → ContFun A C :=
  fun g ↦ AbramskyJung.Chapter3.ContFun.comp k g

private theorem precompose_scottContinuous
    (hC : IsDcpo C) (k : ContFun A B) :
    ScottContinuous (precompose (C := C) k) := by
  constructor
  · intro f g hfg x
    exact hfg (k x)
  · intro G s hG hs
    constructor
    · intro y hy
      rcases hy with ⟨g, hg, rfl⟩
      intro x
      exact hs.1 hg (k x)
    · intro q hq x
      have hEvalSup :=
        (AbramskyJung.Chapter3.ContFun.eval_scottContinuous hC (k x)).2 hG hs
      apply hEvalSup.2 (q x)
      intro y hy
      rcases hy with ⟨g, hg, rfl⟩
      exact hq ⟨g, hg, rfl⟩ x

private theorem postcompose_scottContinuous
    (hB : IsDcpo B) (k : ContFun B C) :
    ScottContinuous (postcompose (A := A) k) := by
  constructor
  · intro f g hfg x
    exact k.continuous.monotone (hfg x)
  · intro G s hG hs
    constructor
    · intro y hy
      rcases hy with ⟨g, hg, rfl⟩
      intro x
      exact k.continuous.monotone (hs.1 hg x)
    · intro q hq x
      have hEvalSup :=
        (AbramskyJung.Chapter3.ContFun.eval_scottContinuous hB x).2 hG hs
      have hEvalDir : DirectedSet
          ((fun g : ContFun A B ↦ g x) '' G) :=
        AbramskyJung.Chapter2.DirectedSet.image
          (AbramskyJung.Chapter3.ContFun.eval_scottContinuous hB x).monotone hG
      have hPostSup := k.continuous.maps_isSup hEvalDir hEvalSup
      apply hPostSup.2 (q x)
      intro y hy
      rcases hy with ⟨z, hz, rfl⟩
      rcases hz with ⟨g, hg, rfl⟩
      exact hq ⟨g, hg, rfl⟩ x

private def sandwich (a : ContFun A A) (b : ContFun B B) :
    ContFun A B → ContFun A B :=
  fun f ↦ AbramskyJung.Chapter3.ContFun.comp b
    (AbramskyJung.Chapter3.ContFun.comp f a)

private theorem sandwich_scottContinuous (hB : IsDcpo B)
    (a : ContFun A A) (b : ContFun B B) :
    ScottContinuous (sandwich a b) := by
  exact (postcompose_scottContinuous (A := A) hB b).comp
    (precompose_scottContinuous (C := B) hB a)

private def squareTensorMap (hB : IsDcpo B)
    (a : ContFun A A) (b : ContFun B B) :
    ContFun (ContFun A B) (ContFun A B) where
  toFun f := sandwich a b (sandwich a b f)
  continuous :=
    (sandwich_scottContinuous hB a b).comp
      (sandwich_scottContinuous hB a b)

end Composition

section FiniteSeparation

variable {A : Type u} {B : Type v}
variable [Preorder A] [Preorder B]

private noncomputable def separatorPattern
    (b : ContFun B B) (FA : Finset A) (FB : Finset B)
    (f : ContFun A B) : Finset (A × B) := by
  classical
  exact (FA.product FB).filter fun p ↦
    b (f p.1) ≤ p.2 ∧ p.2 ≤ f p.1

@[simp] private theorem mem_separatorPattern
    (b : ContFun B B) (FA : Finset A) (FB : Finset B)
    (f : ContFun A B) (x : A) (y : B) :
    (x, y) ∈ separatorPattern b FA FB f ↔
      x ∈ FA ∧ y ∈ FB ∧ b (f x) ≤ y ∧ y ≤ f x := by
  classical
  simp [separatorPattern, and_assoc]

private theorem squareTensorMap_finitelySeparated
    (hB : IsDcpo B) (a : ContFun A A) (b : ContFun B B)
    (ha : IsFinitelySeparated a) (hb : IsFinitelySeparated b) :
    IsFinitelySeparated (squareTensorMap hB a b) := by
  classical
  rcases ha with ⟨FA, hFAfinite, hFA⟩
  rcases hb with ⟨FB, hFBfinite, hFB⟩
  let FAs : Finset A := hFAfinite.toFinset
  let FBs : Finset B := hFBfinite.toFinset
  let K : Finset (A × B) := FAs.product FBs
  let pat : ContFun A B → Finset (A × B) :=
    separatorPattern b FAs FBs
  have hPatSubset (f : ContFun A B) : pat f ⊆ K := by
    simpa [pat, K, separatorPattern] using
      (Finset.filter_subset (FAs.product FBs)
        (p := fun p : A × B ↦ b (f p.1) ≤ p.2 ∧ p.2 ≤ f p.1))
  have hRangeFinite : (Set.range pat).Finite := by
    apply K.powerset.finite_toSet.subset
    rintro p ⟨f, rfl⟩
    simpa only [Finset.mem_coe, Finset.mem_powerset] using hPatSubset f
  let R := {z : Finset (A × B) // z ∈ Set.range pat}
  letI : Finite R := hRangeFinite.to_subtype
  let rep : R → ContFun A B := fun z ↦ Classical.choose z.property
  have rep_spec (z : R) : pat (rep z) = z :=
    Classical.choose_spec z.property
  let middle : ContFun A B → ContFun A B := sandwich a b
  let M : Set (ContFun A B) := Set.range (fun z : R ↦ middle (rep z))
  refine ⟨M, Set.finite_range _, ?_⟩
  intro g
  let z : R := ⟨pat g, ⟨g, rfl⟩⟩
  let m : ContFun A B := middle (rep z)
  have hmM : m ∈ M := ⟨z, rfl⟩
  have hrep : pat (rep z) = pat g := by
    simpa [z] using rep_spec z
  have hmiddle_rep_le_g : middle (rep z) ≤ g := by
    intro s
    rcases hFA s with ⟨x, hxFA, hasx, hxs⟩
    rcases hFB (g x) with ⟨y, hyFB, hbgxy, hygx⟩
    have hxFAs : x ∈ FAs := by simpa [FAs] using hxFA
    have hyFBs : y ∈ FBs := by simpa [FBs] using hyFB
    have hpat_g : (x, y) ∈ pat g := by
      simpa [pat] using And.intro hxFAs
        (And.intro hyFBs (And.intro hbgxy hygx))
    have hpat_rep : (x, y) ∈ pat (rep z) := by
      rw [hrep]
      exact hpat_g
    have hrep_bounds : b (rep z x) ≤ y ∧ y ≤ rep z x := by
      have h := (mem_separatorPattern b FAs FBs (rep z) x y).mp
        (by simpa [pat] using hpat_rep)
      exact h.2.2
    change b (rep z (a s)) ≤ g s
    calc
      b (rep z (a s)) ≤ b (rep z x) :=
        b.continuous.monotone ((rep z).continuous.monotone hasx)
      _ ≤ y := hrep_bounds.1
      _ ≤ g x := hygx
      _ ≤ g s := g.continuous.monotone hxs
  have hmiddle_g_le_rep : middle g ≤ rep z := by
    intro s
    rcases hFA s with ⟨x, hxFA, hasx, hxs⟩
    rcases hFB (rep z x) with ⟨y, hyFB, hbfx, hyfx⟩
    have hxFAs : x ∈ FAs := by simpa [FAs] using hxFA
    have hyFBs : y ∈ FBs := by simpa [FBs] using hyFB
    have hpat_rep : (x, y) ∈ pat (rep z) := by
      simpa [pat] using And.intro hxFAs
        (And.intro hyFBs (And.intro hbfx hyfx))
    have hpat_g : (x, y) ∈ pat g := by
      rw [← hrep]
      exact hpat_rep
    have hg_bounds : b (g x) ≤ y ∧ y ≤ g x := by
      have h := (mem_separatorPattern b FAs FBs g x y).mp
        (by simpa [pat] using hpat_g)
      exact h.2.2
    change b (g (a s)) ≤ rep z s
    calc
      b (g (a s)) ≤ b (g x) :=
        b.continuous.monotone (g.continuous.monotone hasx)
      _ ≤ y := hg_bounds.1
      _ ≤ rep z x := hyfx
      _ ≤ rep z s := (rep z).continuous.monotone hxs
  refine ⟨m, hmM, ?_, ?_⟩
  · intro s
    change b (b (g (a (a s)))) ≤ b (rep z (a s))
    exact b.continuous.monotone (hmiddle_g_le_rep (a s))
  · exact hmiddle_rep_le_g

end FiniteSeparation

section DirectedSquares

variable {D : Type u} [Preorder D]

private theorem squareEval_monotone (x : D) :
    Monotone (fun a : ContFun D D ↦ a (a x)) := by
  intro a b hab
  calc
    a (a x) ≤ b (a x) := hab _
    _ ≤ b (b x) := b.continuous.monotone (hab x)

private theorem squareEval_directed
    (A : DirectedFSApproximateIdentity D) (x : D) :
    DirectedSet ((fun a : ContFun D D ↦ a (a x)) '' A.maps) :=
  AbramskyJung.Chapter2.DirectedSet.image (squareEval_monotone x) A.directed

private theorem squareEval_isSup
    (A : DirectedFSApproximateIdentity D) (x : D) :
    IsSup ((fun a : ContFun D D ↦ a (a x)) '' A.maps) x := by
  constructor
  · rintro _ ⟨a, ha, rfl⟩
    calc
      a (a x) ≤ a x := (A.pointwise_sup (a x)).1 ⟨a, ha, rfl⟩
      _ ≤ x := (A.pointwise_sup x).1 ⟨a, ha, rfl⟩
  · intro y hy
    apply (A.pointwise_sup x).2 y
    rintro _ ⟨a, ha, rfl⟩
    apply (A.pointwise_sup (a x)).2 y
    rintro _ ⟨b, hb, rfl⟩
    rcases A.directed.2 ha hb with ⟨c, hc, hac, hbc⟩
    calc
      b (a x) ≤ c (a x) := hbc _
      _ ≤ c (c x) := c.continuous.monotone (hac x)
      _ ≤ y := hy ⟨c, hc, rfl⟩

end DirectedSquares

section TensorFamily

variable {A : Type u} {B : Type v}
variable [Preorder A] [Preorder B]

private theorem squareTensorMap_pair_monotone (hB : IsDcpo B) :
    Monotone (fun p : ContFun A A × ContFun B B ↦
      squareTensorMap hB p.1 p.2) := by
  intro p q hpq f x
  have hsource : p.1 (p.1 x) ≤ q.1 (q.1 x) := by
    calc
      p.1 (p.1 x) ≤ q.1 (p.1 x) := hpq.1 _
      _ ≤ q.1 (q.1 x) := q.1.continuous.monotone (hpq.1 x)
  change p.2 (p.2 (f (p.1 (p.1 x)))) ≤
    q.2 (q.2 (f (q.1 (q.1 x))))
  calc
    p.2 (p.2 (f (p.1 (p.1 x)))) ≤
        q.2 (p.2 (f (p.1 (p.1 x)))) := hpq.2 _
    _ ≤ q.2 (q.2 (f (p.1 (p.1 x)))) :=
      q.2.continuous.monotone (hpq.2 _)
    _ ≤ q.2 (q.2 (f (q.1 (q.1 x)))) :=
      q.2.continuous.monotone
        (q.2.continuous.monotone (f.continuous.monotone hsource))

end TensorFamily

/-- Gierz et al., Proposition II-2.18, proved from the two directed FS
approximate identities by the squared-sandwich construction. -/
theorem fs_exponential
    {S T : Type u} [Preorder S] [Preorder T]
    (hS : IsFSDomain S) (hT : IsFSDomain T) :
    IsFSDomain (ContFun S T) := by
  have hFunDcpoOrder : AbramskyJung.Chapter2.IsDcpoOrder (ContFun S T) := by
    constructor
    · exact AbramskyJung.Chapter3.ContFun.isDcpo_of_codomain hT.1.1
    · intro f g hfg hgf
      apply AbramskyJung.Chapter3.ContFun.ext_apply
      intro x
      exact hT.1.2 (f x) (g x) (hfg x) (hgf x)
  rcases hS.2 with ⟨AS⟩
  rcases hT.2 with ⟨AT⟩
  let pairMaps : Set (ContFun S S × ContFun T T) :=
    {p | p.1 ∈ AS.maps ∧ p.2 ∈ AT.maps}
  let tensor : ContFun S S × ContFun T T →
      ContFun (ContFun S T) (ContFun S T) :=
    fun p ↦ squareTensorMap hT.1.1 p.1 p.2
  have hPairDirected : DirectedSet pairMaps := by
    simpa [pairMaps] using
      AbramskyJung.Chapter3.directed_prod AS.directed AT.directed
  have hTensorMonotone : Monotone tensor := by
    simpa [tensor] using
      squareTensorMap_pair_monotone (A := S) (B := T) hT.1.1
  refine ⟨hFunDcpoOrder, ⟨{
    maps := tensor '' pairMaps
    directed := AbramskyJung.Chapter2.DirectedSet.image
      hTensorMonotone hPairDirected
    finitelySeparated := ?_
    pointwise_sup := ?_ }⟩⟩
  · intro H hH
    rcases hH with ⟨p, hp, rfl⟩
    have hpS : p.1 ∈ AS.maps := by simpa [pairMaps] using hp.1
    have hpT : p.2 ∈ AT.maps := by simpa [pairMaps] using hp.2
    simpa [tensor] using squareTensorMap_finitelySeparated hT.1.1 p.1 p.2
      (AS.finitelySeparated p.1 hpS) (AT.finitelySeparated p.2 hpT)
  · intro f
    constructor
    · rintro _ ⟨H, ⟨p, hp, rfl⟩, rfl⟩
      have hpS : p.1 ∈ AS.maps := by simpa [pairMaps] using hp.1
      have hpT : p.2 ∈ AT.maps := by simpa [pairMaps] using hp.2
      have ha := AS.finitelySeparated p.1 hpS
      have hb := AT.finitelySeparated p.2 hpT
      intro x
      change p.2 (p.2 (f (p.1 (p.1 x)))) ≤ f x
      calc
        p.2 (p.2 (f (p.1 (p.1 x)))) ≤
            p.2 (f (p.1 (p.1 x))) := hb.below_id _
        _ ≤ f (p.1 (p.1 x)) := hb.below_id _
        _ ≤ f x := f.continuous.monotone
          (le_trans (ha.below_id (p.1 x)) (ha.below_id x))
    · intro q hq x
      have hfSup := f.continuous.maps_isSup
        (squareEval_directed AS x) (squareEval_isSup AS x)
      apply hfSup.2 (q x)
      rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      apply (squareEval_isSup AT (f (a (a x)))).2 (q x)
      rintro _ ⟨b, hb, rfl⟩
      have hp : (a, b) ∈ pairMaps := ⟨ha, hb⟩
      have hMap : tensor (a, b) ∈ tensor '' pairMaps :=
        ⟨(a, b), hp, rfl⟩
      have hEval : tensor (a, b) f ∈
          (fun H : ContFun (ContFun S T) (ContFun S T) ↦ H f) ''
            (tensor '' pairMaps) :=
        ⟨tensor (a, b), hMap, rfl⟩
      simpa [tensor] using hq hEval x

end GierzInternal
end FiniteValuationApproximable
