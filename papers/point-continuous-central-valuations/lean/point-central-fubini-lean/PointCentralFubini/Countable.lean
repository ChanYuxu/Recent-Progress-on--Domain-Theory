import PointCentralFubini.Basic

set_option autoImplicit false
open Set Topology TopologicalSpace
open scoped ENNReal BigOperators
universe u v
namespace PointCentralFubini
variable {X : Type u} [TopologicalSpace X]

/-- Equation `eq:kappa`: infimum of masses of open neighbourhoods. -/
noncomputable def capacity (μ : Valuation X) (A : Set X) : ℝ≥0∞ :=
  ⨅ (U : Opens X) (_ : A ⊆ U), μ U

theorem capacity_le (μ : Valuation X) {A : Set X} (U : Opens X) (h : A ⊆ U) :
    capacity μ A ≤ μ U := iInf_le_of_le U (iInf_le _ h)

theorem capacity_mono (μ : Valuation X) {A B : Set X} (h : A ⊆ B) :
    capacity μ A ≤ capacity μ B := by
  apply le_iInf; intro U; apply le_iInf; intro hB
  exact capacity_le μ U (h.trans hB)

@[simp] theorem capacity_open (μ : Valuation X) (U : Opens X) :
    capacity μ (U : Set X) = μ U := by
  apply le_antisymm (capacity_le μ U Subset.rfl)
  exact le_iInf fun V => le_iInf fun h => μ.mono h

/-- A useful strengthening of `lem:kappa-countable`: finiteness of the
increasing sets is not needed for this capacity calculation. -/
theorem capacity_iUnion (μ : Valuation X) (A : ℕ → Set X) (hA : Monotone A) :
    capacity μ (⋃ n, A n) = ⨆ n, capacity μ (A n) := by
  classical
  apply le_antisymm
  · by_contra hle
    let c : ℝ≥0∞ := ⨆ n, capacity μ (A n)
    have hc : c < capacity μ (⋃ n, A n) := lt_of_not_ge hle
    have hcfin : c ≠ ⊤ := ne_top_of_lt hc
    obtain ⟨δ, hδ, hcδ⟩ := ENNReal.lt_iff_exists_add_pos_lt.mp hc
    let ε : ℕ → ℝ≥0∞ := fun n => (δ : ℝ≥0∞) * (2⁻¹ : ℝ≥0∞) ^ (n + 1)
    have hepos : ∀ n, ε n ≠ 0 := by
      intro n
      exact mul_ne_zero (by exact_mod_cast hδ.ne')
        (pow_ne_zero _ (by norm_num))
    have hesum : ∑' n, ε n = δ := by
      rw [show ε = fun n => (δ : ℝ≥0∞) * (2⁻¹ : ℝ≥0∞) ^ (n + 1) from rfl,
        ENNReal.tsum_mul_left, ENNReal.tsum_geometric_add_one]
      rw [ENNReal.one_sub_inv_two, inv_inv,
        ENNReal.inv_mul_cancel (by norm_num) (by norm_num), mul_one]
    have hcn : ∀ n, capacity μ (A n) ≠ ⊤ := fun n =>
      ne_top_of_le_ne_top hcfin (le_iSup (fun n => capacity μ (A n)) n)
    have hV : ∀ n, ∃ V : Opens X, A n ⊆ V ∧
        μ V < capacity μ (A n) + ε n := by
      intro n
      have hlt := ENNReal.lt_add_right (hcn n) (hepos n)
      obtain ⟨V, hV⟩ := iInf_lt_iff.mp hlt
      obtain ⟨hAV, hV⟩ := iInf_lt_iff.mp hV
      exact ⟨V, hAV, hV⟩
    choose V hAV hV using hV
    let W : ℕ → Opens X := fun n => (Finset.range (n + 1)).sup V
    have hVW : ∀ n, V n ≤ W n := fun n =>
      Finset.le_sup (f := V) (Finset.mem_range.mpr (Nat.lt_succ_self n))
    have hWstep : ∀ n, W (n + 1) = W n ⊔ V (n + 1) := by
      intro n; simp [W, Finset.range_add_one, Finset.sup_insert, sup_comm]
    have hWmono : Monotone W := by
      apply monotone_nat_of_le_succ
      intro n; rw [hWstep]; exact le_sup_left
    have hbound : ∀ n, μ (W n) ≤ capacity μ (A n) +
        ∑ k ∈ Finset.range (n + 1), ε k := by
      intro n; induction n with
      | zero => simpa [W] using (hV 0).le
      | succ n ih =>
        have hcap : capacity μ (A n) ≤ μ (W n ⊓ V (n + 1)) := by
          apply capacity_le
          intro x hx
          exact ⟨hVW n (hAV n hx), hAV (n + 1) (hA (Nat.le_succ n) hx)⟩
        apply (ENNReal.add_le_add_iff_right (hcn n)).mp
        calc
          μ (W (n + 1)) + capacity μ (A n)
              ≤ μ (W (n + 1)) + μ (W n ⊓ V (n + 1)) := add_le_add le_rfl hcap
          _ = μ (W n) + μ (V (n + 1)) := by rw [hWstep, ← μ.modular]
          _ ≤ (capacity μ (A n) + ∑ k ∈ Finset.range (n + 1), ε k) +
              (capacity μ (A (n + 1)) + ε (n + 1)) := add_le_add ih (hV _).le
          _ = (capacity μ (A (n + 1)) +
              ∑ k ∈ Finset.range (n + 1 + 1), ε k) + capacity μ (A n) := by
            rw [Finset.sum_range_succ (n := n + 1)]; ac_rfl
    have hcover : (⋃ n, A n) ⊆ (⨆ n, W n : Opens X) := by
      intro x hx; obtain ⟨n, hn⟩ := mem_iUnion.mp hx
      exact (le_iSup W n) (hVW n (hAV n hn))
    have hmass : μ (⨆ n, W n) ≤ c + δ := by
      rw [μ.map_iSup W hWmono.directed_le]
      apply iSup_le; intro n
      exact (hbound n).trans <| add_le_add (le_iSup (fun n => capacity μ (A n)) n)
        (by rw [← hesum]; exact ENNReal.sum_le_tsum _)
    exact (not_le_of_gt hcδ) ((capacity_le μ _ hcover).trans hmass)
  · apply iSup_le; intro n
    exact capacity_mono μ (subset_iUnion A n)

/-- Source contract: `lem:kappa-countable` (lemma 3.1).
Version: SHA-256 `134da69fa816824e5fefcb93a4e77a8cd5158c8aaab5ffd288ece2372e55d4e6`.
Locator: `source/manuscript.tex`, lines 239--244; no PDF was supplied.
Formalization status: `proved`; human review is pending.

Strict source TeX:
```latex
\begin{lemma}\label{lem:kappa-countable}
Let $X$ be a topological space, let $\nu\in\Val(X)$, and let $F_1\subseteq F_2\subseteq\cdots$ be finite subsets of $X$ with $A=\bigcup_nF_n$. Then
\begin{equation}\label{eq:kappa-continuity}
 \kappa_\nu(A)=\sup_{n\geq1}\kappa_\nu(F_n).
\end{equation}
\end{lemma}
```
-/
theorem capacity_finite_exhaustion (μ : Valuation X) (F : ℕ → Finset X)
    (hF : Monotone F) :
    capacity μ (⋃ n, (F n : Set X)) = ⨆ n, capacity μ (F n : Set X) :=
  capacity_iUnion μ (fun n => (F n : Set X)) hF

/-- Saturation as the intersection of all open neighbourhoods. -/
def saturation (A : Set X) : Set X :=
  {x | ∀ U : Opens X, A ⊆ U → x ∈ U}

theorem subset_saturation (A : Set X) : A ⊆ saturation A :=
  fun _ hx _ hU => hU hx

theorem capacity_saturation (μ : Valuation X) (A : Set X) :
    capacity μ (saturation A) = capacity μ A := by
  apply le_antisymm
  · apply le_iInf; intro U; apply le_iInf; intro hU
    exact capacity_le μ U (fun _ hx => hx U hU)
  · exact capacity_mono μ (subset_saturation A)

/-- Finite increasing exhaustion, including the empty countable set. -/
theorem countable_finite_exhaustion {Y : Type u} {A : Set Y} (hc : A.Countable) :
    ∃ F : ℕ → Finset Y, Monotone F ∧ (⋃ n, (F n : Set Y)) = A := by
  classical
  rcases A.eq_empty_or_nonempty with rfl | hn
  · exact ⟨fun _ => ∅, fun _ _ _ => le_rfl, by simp⟩
  · obtain ⟨f, hf⟩ := hc.exists_eq_range hn
    refine ⟨fun n => (Finset.range n).image f, ?_, ?_⟩
    · intro i j hij
      exact Finset.image_mono f (Finset.range_mono hij)
    · ext x
      simp only [mem_iUnion, Finset.mem_coe, Finset.mem_image, Finset.mem_range]
      constructor
      · rintro ⟨n, k, hk, rfl⟩
        rw [hf]; exact mem_range_self k
      · intro hx
        rw [hf] at hx
        obtain ⟨k, rfl⟩ := hx
        exact ⟨k + 1, k, Nat.lt_succ_self k, rfl⟩

/-- Source contract: `thm:countable-point` (theorem 3.2).
Version: SHA-256 `134da69fa816824e5fefcb93a4e77a8cd5158c8aaab5ffd288ece2372e55d4e6`.
Locator: `source/manuscript.tex`, lines 270--272; no PDF was supplied.
Formalization status: `proved`; human review is pending.

Strict source TeX:
```latex
\begin{theorem}\label{thm:countable-point}
Let $X$ be a topological space such that every open set is the saturation of an at most countable subset. Then $\Val(X)=\Point(X)$. In particular, every continuous valuation on a countable topological space is point-continuous.
\end{theorem}
```
-/
theorem valuation_pointContinuous_of_countable_saturations
    (hX : ∀ U : Opens X, ∃ A : Set X, A.Countable ∧ saturation A = (U : Set X))
    (μ : Valuation X) : PointContinuous μ := by
  apply (pointContinuous_iff μ).mpr
  intro U r hr
  obtain ⟨A, hc, hsat⟩ := hX U
  obtain ⟨F, hF, hFA⟩ := countable_finite_exhaustion hc
  have hcap : capacity μ A = μ U := by
    rw [← capacity_saturation, hsat, capacity_open]
  have hs : r < ⨆ n, capacity μ (F n : Set X) := by
    rw [← capacity_finite_exhaustion μ F hF, hFA, hcap]; exact hr
  obtain ⟨n, hn⟩ := lt_iSup_iff.mp hs
  refine ⟨F n, ?_, fun V hV => hn.trans_le (capacity_le μ V hV)⟩
  intro x hx
  have hxA : x ∈ A := hFA ▸ mem_iUnion.mpr ⟨n, hx⟩
  exact hsat ▸ subset_saturation A hxA

/-- The countable-space clause of theorem 3.2, without separation assumptions. -/
theorem countable_valuation_pointContinuous [Countable X] (μ : Valuation X) :
    PointContinuous μ := by
  apply valuation_pointContinuous_of_countable_saturations _ μ
  intro U
  refine ⟨U, Set.to_countable _, ?_⟩
  apply subset_antisymm
  · exact fun _ hx => hx U Subset.rfl
  · exact subset_saturation _

/-- The source's order-coinitial hypothesis; it is imposed on each open,
not on every finite Boolean truth cell. -/
def CountablyCoinitialOpens (P : Type u) [PartialOrder P] : Prop :=
  ∀ U : ScottOpens P, ∃ A : Set P, A.Countable ∧
    (∀ a ∈ A, WithScott.toScott a ∈ U) ∧
    ∀ x : P, WithScott.toScott x ∈ U → ∃ a ∈ A, a ≤ x

end PointCentralFubini
