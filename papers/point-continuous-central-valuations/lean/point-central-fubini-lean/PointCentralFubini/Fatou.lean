import PointCentralFubini.Integration
set_option autoImplicit false
open Set Topology TopologicalSpace
open scoped ENNReal BigOperators
universe u
namespace PointCentralFubini

private theorem scott_of_witness {P : Type u} [PartialOrder P] (f : P → ℝ≥0∞)
    (hm : Monotone f)
    (hw : ∀ A : Set P, A.Nonempty → DirectedOn (· ≤ ·) A →
      ∀ p, IsLUB A p → ∀ r, r < f p → ∃ a ∈ A, r < f a) : ScottContinuous f := by
  intro A hn hd p hp
  constructor
  · rintro z ⟨a,ha,rfl⟩; exact hm (hp.1 ha)
  · intro b hb
    by_contra hle
    obtain ⟨a,ha,hab⟩ := hw A hn hd p hp b (lt_of_not_ge hle)
    exact (not_le_of_gt hab) (hb (mem_image_of_mem f ha))

private theorem scott_witness {P : Type u} [PartialOrder P] {f : P → ℝ≥0∞}
    (hf : ScottContinuous f) {A : Set P} (hn : A.Nonempty)
    (hd : DirectedOn (· ≤ ·) A) {p : P} (hp : IsLUB A p)
    {r : ℝ≥0∞} (hr : r < f p) : ∃ a ∈ A, r < f a := by
  rw [scott_map_iSup f hf hn hd hp] at hr
  obtain ⟨a,ha⟩ := lt_iSup_iff.mp hr
  exact ⟨a,a.property,ha⟩

private theorem directed_constraints {P : Type u} [PartialOrder P]
    {A : Set P} (hd : DirectedOn (· ≤ ·) A) {a₀ : P} (ha₀ : a₀ ∈ A)
    (s : Finset ℕ) (G : ℕ → P → Prop)
    (hm : ∀ i, ∀ a b, a ≤ b → G i a → G i b)
    (hw : ∀ i ∈ s, ∃ a ∈ A, G i a) :
    ∃ a ∈ A, a₀ ≤ a ∧ ∀ i ∈ s, G i a := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨a₀,ha₀,le_rfl,by simp⟩
  | @insert i s hi ih =>
    obtain ⟨a,ha,ha₀a,hGa⟩ := ih (fun j hj => hw j (Finset.mem_insert_of_mem hj))
    obtain ⟨b,hb,hGb⟩ := hw i (Finset.mem_insert_self i s)
    obtain ⟨c,hc,hac,hbc⟩ := hd a ha b hb
    refine ⟨c,hc,ha₀a.trans hac,?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact hm _ b c hbc hGb
    · exact hm j a c hac (hGa j hj)

private noncomputable def fatouMinorant {P : Type u} (h : P → ℝ≥0∞)
    (f : ℕ → P → ℝ≥0∞) (N : ℕ) (p : P) : ℝ≥0∞ :=
  h p ⊓ ⨅ n ≥ N, f n p

/-- The delicate continuity step in source lemma 4.1. The lower bound h
is essential; the tail infimum alone is not asserted to be continuous. -/
theorem fatouMinorant_scott {P : Type u} [PartialOrder P]
    (h : P → ℝ≥0∞) (f : ℕ → P → ℝ≥0∞)
    (hh : ScottContinuous h) (hf : ∀ n, ScottContinuous (f n))
    (hlim : ∀ p, h p ≤ ⨆ N : ℕ, ⨅ n ≥ N, f n p) (N : ℕ) :
    ScottContinuous (fatouMinorant h f N) := by
  apply scott_of_witness
  · intro a b hab
    exact inf_le_inf (hh.monotone hab) (iInf_mono fun n => iInf_mono fun _ => (hf n).monotone hab)
  · intro A hn hd p hp r hr
    obtain ⟨q,hrq,hq⟩ := exists_between hr
    obtain ⟨a₀,ha₀,hqa₀⟩ := scott_witness hh hn hd hp (hq.trans_le inf_le_left)
    have hqtail : q < ⨆ N : ℕ, ⨅ n ≥ N, f n a₀ := hqa₀.trans_le (hlim a₀)
    obtain ⟨N₀,hN₀⟩ := lt_iSup_iff.mp hqtail
    let N' := max N N₀
    have htail : ∀ n ≥ N', q < f n a₀ := by
      intro n hn'
      exact hN₀.trans_le (iInf_le_of_le n (iInf_le _ ((le_max_right N N₀).trans hn')))
    have hfinite : ∀ n ∈ Finset.Ico N N', ∃ a ∈ A, q < f n a := by
      intro n hn'
      have hNp : q < f n p := hq.trans_le <|
        inf_le_right.trans (iInf_le_of_le n (iInf_le _ (Finset.mem_Ico.mp hn').1))
      exact scott_witness (hf n) hn hd hp hNp
    obtain ⟨a,ha,ha₀a,hGa⟩ := directed_constraints hd ha₀ (Finset.Ico N N')
      (fun n a => q < f n a) (fun n a b hab hqa => hqa.trans_le ((hf n).monotone hab)) hfinite
    refine ⟨a,ha,hrq.trans_le ?_⟩
    apply le_inf (hqa₀.trans_le (hh.monotone ha₀a)).le
    apply le_iInf; intro n; apply le_iInf; intro hNn
    by_cases hn' : N' ≤ n
    · exact (htail n hn').le.trans ((hf n).monotone ha₀a)
    · exact (hGa n (Finset.mem_Ico.mpr ⟨hNn,lt_of_not_ge hn'⟩)).le

/-- Source contract: `lem:scott-fatou` (lemma 4.1).
Version: SHA-256 `134da69fa816824e5fefcb93a4e77a8cd5158c8aaab5ffd288ece2372e55d4e6`.
Locator: `source/manuscript.tex`, lines 303--314; no PDF was supplied.
Formalization status: `proved`; human review is pending.

Strict source TeX:
```latex
\begin{lemma}\label{lem:scott-fatou}
Let $P$ be a dcpo, let $\xi\in\Val(P)$, and let $h,h_1,h_2,\ldots:P\to\Rbar$ be Scott-continuous. If
\[
 h(p)\leq\liminf_{n\to\infty}h_n(p)
 \qquad(p\in P),
\]
then
\begin{equation}\label{eq:scott-fatou}
 \int_P h\dd\xi
 \leq\liminf_{n\to\infty}\int_P h_n\dd\xi.
\end{equation}
\end{lemma}
```
-/
theorem scott_fatou (P : Type u) [PartialOrder P] (_hP : IsDcpo P)
    (ξ : DValuation P) (h : P → ℝ≥0∞) (f : ℕ → P → ℝ≥0∞)
    (hh : ScottContinuous h) (hf : ∀ n, ScottContinuous (f n))
    (hlim : ∀ p, h p ≤ ⨆ N : ℕ, ⨅ n ≥ N, f n p) :
    integral ξ (fun p => h (WithScott.ofScott p)) ≤
      ⨆ N : ℕ, ⨅ n ≥ N, integral ξ (fun p => f n (WithScott.ofScott p)) := by
  have hmono : Monotone (fatouMinorant h f) := by
    intro N M hNM p
    apply inf_le_inf le_rfl
    apply le_iInf; intro n; apply le_iInf; intro hMn
    exact iInf_le_of_le n (iInf_le _ (hNM.trans hMn))
  have hsup : ∀ p, h p = ⨆ N, fatouMinorant h f N p := by
    intro p
    simp only [fatouMinorant]
    rw [← inf_iSup_eq]
    exact (inf_eq_left.mpr (hlim p)).symm
  have he := fpr_integral_iSup ξ
    (fun N p => fatouMinorant h f N (WithScott.ofScott p))
    (fun N => scott_isLSC (fatouMinorant_scott h f hh hf hlim N))
    (fun N M => ⟨max N M, hmono (le_max_left N M),hmono (le_max_right N M)⟩)
  rw [show (fun p : WithScott P => ⨆ N, fatouMinorant h f N (WithScott.ofScott p)) =
    (fun p => h (WithScott.ofScott p)) from funext fun p => (hsup _).symm] at he
  rw [he]
  apply iSup_le; intro N
  apply le_trans (b := ⨅ n ≥ N, integral ξ (fun p => f n (WithScott.ofScott p)))
  · apply le_iInf; intro n; apply le_iInf; intro hn
    apply integral_mono ξ; intro p
    exact inf_le_right.trans (iInf_le_of_le n (iInf_le _ hn))
  · exact le_iSup (fun M : ℕ => ⨅ n ≥ M,
      integral ξ (fun p => f n (WithScott.ofScott p))) N
end PointCentralFubini
