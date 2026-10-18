import CoreCompactSimplified.CoreCompactLattice
import Mathlib.Data.Nat.Lattice

/-!
He–Zhang Lemmas 4.1 and 4.2. These support lemmas are used by the actual
ordinal-pruning proof in `HeZhangPruning`; the full Theorem 4.13 is proved
separately in `HeZhangProof`. They are not substitutes for that full theorem.
-/

set_option autoImplicit false

universe u

namespace CoreCompactSimplified.HeZhangSupport

open Set TopologicalSpace CoreCompactNonSober

variable {P : Type u} [PartialOrder P]

local instance : TopologicalSpace P := scottTopology P

private theorem principal_isClosed (a : P) : IsClosed (Set.Iic a) := by
  rw [← scott_closure_singleton a]
  exact isClosed_closure

private def tailLower (U : ScottOpens P) (a : ℕ → P) (m : ℕ) : Set P :=
  {x | x ∉ U ∨ ∃ n : ℕ, m ≤ n ∧ x ≤ a n}

private theorem tailLower_isClosed (U : ScottOpens P) (a : ℕ → P)
    (hfinite : ∀ b ∈ U, ∃ N : ℕ, ∀ n, N ≤ n → ¬ b ≤ a n) (m : ℕ) :
    IsClosed (tailLower U a m) := by
  classical
  have hU := (isOpen_scott_iff _).mp U.isOpen
  apply (isClosed_scott_iff _).mpr
  constructor
  · intro x y hxy hy
    rcases hy with hyU | ⟨n, hmn, hyn⟩
    · exact Or.inl (fun hxU ↦ hyU (hU.1 hxy hxU))
    · exact Or.inr ⟨n, hmn, hxy.trans hyn⟩
  · intro E hEC hE s hs
    by_cases hsU : s ∈ U
    · obtain ⟨b, hbE, hbU⟩ := hU.2 E hE s hs hsU
      obtain ⟨N, hN⟩ := hfinite b hbU
      let F : Set P := {x | x ∈ E ∧ b ≤ x}
      have hF : NonemptyDirected F := by
        refine ⟨⟨b, hbE, le_rfl⟩, ?_⟩
        intro x hx y hy
        obtain ⟨z, hzE, hxz, hyz⟩ := hE.2 x hx.1 y hy.1
        exact ⟨z, ⟨hzE, hx.2.trans hxz⟩, hxz, hyz⟩
      have hcofinal : ∀ x ∈ E, ∃ y ∈ F, x ≤ y := by
        intro x hx
        obtain ⟨y, hyE, hby, hxy⟩ := hE.2 b hbE x hx
        exact ⟨y, ⟨hyE, hby⟩, hxy⟩
      have hFs : IsLUB F s := by
        constructor
        · intro x hx
          exact hs.1 hx.1
        · intro z hz
          apply hs.2
          intro x hx
          obtain ⟨y, hyF, hxy⟩ := hcofinal x hx
          exact hxy.trans (hz hyF)
      let K : Set P := ⋃ n ∈ Finset.Ico m N, Set.Iic (a n)
      have hKclosed : IsClosed K :=
        isClosed_biUnion_finset (fun n _ ↦ principal_isClosed (a n))
      have hFK : F ⊆ K := by
        intro x hx
        have hxU : x ∈ U := hU.1 hx.2 hbU
        rcases hEC hx.1 with hxnotU | ⟨n, hmn, hxn⟩
        · exact False.elim (hxnotU hxU)
        · have hnN : n < N := by
            apply lt_of_not_ge
            intro hNn
            exact hN n hNn (hx.2.trans hxn)
          exact Set.mem_iUnion.mpr ⟨n, Set.mem_iUnion.mpr
            ⟨Finset.mem_Ico.mpr ⟨hmn, hnN⟩, hxn⟩⟩
      have hsK : s ∈ K := ((isClosed_scott_iff _).mp hKclosed).2 F hFK hF s hFs
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hsK
      obtain ⟨hnI, hsn⟩ := Set.mem_iUnion.mp hn
      exact Or.inr ⟨n, (Finset.mem_Ico.mp hnI).1, hsn⟩
    · exact Or.inl hsU

/-- He–Zhang Lemma 4.1 in the equivalent unbounded-natural-indices form.
The proof uses the printed decreasing closed-tail complements. -/
theorem infinitely_often_common_lower_unbounded (V U : ScottOpens P)
    (hVU : OpenWayBelow V U) (a : ℕ → P) (ha : ∀ n, a n ∈ V) :
    ∃ b ∈ U, ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ b ≤ a n := by
  classical
  by_contra hnone
  push Not at hnone
  have hfinite : ∀ b ∈ U, ∃ N : ℕ, ∀ n, N ≤ n → ¬ b ≤ a n := hnone
  let W : ℕ → ScottOpens P := fun m ↦
    ⟨(tailLower U a m)ᶜ, (tailLower_isClosed U a hfinite m).isOpen_compl⟩
  have hWmono : Monotone W := by
    intro m n hmn x hx
    change x ∉ tailLower U a n
    intro hxn
    apply hx
    rcases hxn with hxU | ⟨k, hnk, hxk⟩
    · exact Or.inl hxU
    · exact Or.inr ⟨k, hmn.trans hnk, hxk⟩
  have hD : DirectedOn (· ≤ ·) (Set.range W) :=
    hWmono.directed_le.directedOn_range
  have hcover : U ≤ sSup (Set.range W) := by
    intro x hxU
    obtain ⟨N, hN⟩ := hfinite x hxU
    apply Opens.mem_sSup.mpr
    refine ⟨W N, Set.mem_range_self N, ?_⟩
    intro hxC
    rcases hxC with hxnotU | ⟨n, hNn, hxn⟩
    · exact hxnotU hxU
    · exact hN n hNn hxn
  obtain ⟨Z, hZ, hVZ⟩ := hVU (Set.range W) (Set.range_nonempty W) hD hcover
  obtain ⟨m, rfl⟩ := hZ
  have hmW : a m ∈ W m := hVZ (ha m)
  exact hmW (Or.inr ⟨m, le_rfl, le_rfl⟩)

/-- Exact infinite-index-set formulation of He–Zhang Lemma 4.1.
The dcpo hypothesis is retained in the source interface, although the
printed argument proves this auxiliary result for every partial order. -/
theorem infinitely_often_common_lower (_hP : IsDcpo P) (V U : ScottOpens P)
    (hVU : OpenWayBelow V U) (a : ℕ → P) (ha : ∀ n, a n ∈ V) :
    ∃ b ∈ U, ({n : ℕ | b ≤ a n} : Set ℕ).Infinite := by
  obtain ⟨b, hbU, hb⟩ := infinitely_often_common_lower_unbounded V U hVU a ha
  refine ⟨b, hbU, Set.infinite_of_not_bddAbove ?_⟩
  rintro ⟨N, hN⟩
  obtain ⟨n, hNn, hbn⟩ := hb (N + 1)
  have hnN := hN hbn
  omega

/-- He–Zhang Lemma 4.2. Closures here are intrinsic Scott closures of the
original partial order, not closures in an auxiliary Hausdorff topology. -/
theorem closure_iInter_antitone_lower (_hP : IsDcpo P) (hcore : ScottCoreCompact P)
    (A : ℕ → Set P) (hA : Antitone A) (hlower : ∀ n, IsLowerSet (A n)) :
    closure (⋂ n, A n) = ⋂ n, closure (A n) := by
  apply Set.Subset.antisymm
  · intro x hx
    exact Set.mem_iInter.mpr (fun n ↦ closure_mono (Set.iInter_subset A n) hx)
  · intro x hx
    apply mem_closure_iff.mpr
    intro O hO hxO
    let U : ScottOpens P := ⟨O, hO⟩
    obtain ⟨V, hxV, hVU⟩ := hcore U x hxO
    have hchoose : ∀ n : ℕ, ∃ a ∈ V, a ∈ A n := by
      intro n
      obtain ⟨a, haV, haA⟩ := mem_closure_iff.mp (Set.mem_iInter.mp hx n)
        V V.isOpen hxV
      exact ⟨a, haV, haA⟩
    choose a haV haA using hchoose
    obtain ⟨b, hbU, hb⟩ := infinitely_often_common_lower_unbounded V U hVU a haV
    refine ⟨b, hbU, Set.mem_iInter.mpr ?_⟩
    intro n
    obtain ⟨k, hnk, hbak⟩ := hb n
    exact hlower n hbak (hA hnk (haA k))

end CoreCompactSimplified.HeZhangSupport

