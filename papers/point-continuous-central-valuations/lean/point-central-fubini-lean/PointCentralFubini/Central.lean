import PointCentralFubini.Literature
import PointCentralFubini.CountableDcpo
import PointCentralFubini.Incidence
set_option autoImplicit false
open Set Topology TopologicalSpace
open scoped ENNReal
universe u v w
namespace PointCentralFubini
variable {P : Type u} {Q : Type v} [PartialOrder P] [PartialOrder Q]

theorem sectionValue_isLSC (μ : DValuation P) (W : ScottOpens (P × Q)) :
    IsLSC (fun y : WithScott Q => μ (sectionMap W (WithScott.ofScott y))) :=
  scott_isLSC ((sectionMap_scott W).comp μ.continuous)

theorem sliceValue_isLSC (ν : DValuation Q) (W : ScottOpens (P × Q)) :
    IsLSC (fun x : WithScott P => ν (sliceRight W (WithScott.ofScott x))) := by
  have hs := innerIntegral_scott ν (fun z => indicator W (WithScott.toScott z))
    ((isLSC_scott_iff _).mp (indicator_isLSC W))
  have he : (fun x : P => integral ν
      (fun y => indicator W (WithScott.toScott (x,WithScott.ofScott y)))) =
      (fun x => ν (sliceRight W x)) := by
    funext x; exact integral_indicator ν (sliceRight W x)
  rw [he] at hs
  exact scott_isLSC hs

theorem OpenCommute.scale_left {μ : DValuation P} {ν : DValuation Q}
    (h : OpenCommute μ ν) (a : ℝ≥0∞) (ha : a ≠ ⊤) : OpenCommute (μ.scale a) ν := by
  intro W
  change integral (μ.scale a) (fun x => ν (sliceRight W (WithScott.ofScott x))) =
    integral ν (fun y => a * μ (sectionMap W (WithScott.ofScott y)))
  rw [integral_scale μ a ha, fpr_integral_smul ν a _ (sectionValue_isLSC μ W)]
  exact congrArg (fun x => a*x) (h W)

theorem OpenCommute.scale_right {μ : DValuation P} {ν : DValuation Q}
    (h : OpenCommute μ ν) (a : ℝ≥0∞) (ha : a ≠ ⊤) : OpenCommute μ (ν.scale a) := by
  intro W
  change integral μ (fun x => a * ν (sliceRight W (WithScott.ofScott x))) =
    integral (ν.scale a) (fun y => μ (sectionMap W (WithScott.ofScott y)))
  rw [fpr_integral_smul μ a _ (sliceValue_isLSC ν W),integral_scale ν a ha]
  exact congrArg (fun x => a*x) (h W)

theorem openCommute_iSup_left (μ : DValuation P) (ν : DValuation Q)
    {ι : Type w} [Nonempty ι] (μi : ι → DValuation P) (hd : Directed (· ≤ ·) μi)
    (hμ : ∀ U, μ U = ⨆ i, μi i U) (hcomm : ∀ i, OpenCommute (μi i) ν) : OpenCommute μ ν := by
  intro W
  rw [integral_valuation_iSup μ μi hd hμ _ (sliceValue_isLSC ν W)]
  have he : (fun y : WithScott Q => μ (sectionMap W (WithScott.ofScott y))) =
      (fun y => ⨆ i, μi i (sectionMap W (WithScott.ofScott y))) := funext fun y => hμ _
  rw [he, fpr_integral_iSup ν _ (fun i => sectionValue_isLSC (μi i) W)
    (fun i j => by
      obtain ⟨k,hik,hjk⟩ := hd i j
      exact ⟨k,fun y => hik _,fun y => hjk _⟩)]
  exact iSup_congr fun i => hcomm i W

theorem openCommute_iSup_right (μ : DValuation P) (ν : DValuation Q)
    {ι : Type w} [Nonempty ι] (νi : ι → DValuation Q) (hd : Directed (· ≤ ·) νi)
    (hν : ∀ U, ν U = ⨆ i, νi i U) (hcomm : ∀ i, OpenCommute μ (νi i)) : OpenCommute μ ν := by
  intro W
  rw [integral_valuation_iSup ν νi hd hν _ (sectionValue_isLSC μ W)]
  have he : (fun x : WithScott P => ν (sliceRight W (WithScott.ofScott x))) =
      (fun x => ⨆ i, νi i (sliceRight W (WithScott.ofScott x))) := funext fun x => hν _
  rw [he, fpr_integral_iSup μ _ (fun i => sliceValue_isLSC (νi i) W)
    (fun i j => by
      obtain ⟨k,hik,hjk⟩ := hd i j
      exact ⟨k,fun x => hik _,fun x => hjk _⟩)]
  exact iSup_congr fun i => hcomm i W

/-- Finite-mass normalization from the EXACT open-set subprobability theorem. -/
theorem finite_point_openCommute (hP : IsDcpo P) (hQ : IsDcpo Q)
    (μ : DValuation P) (ν : DValuation Q) (hpoint : PointContinuous μ)
    (hμ : μ.Finite) (hν : ν.Finite) : OpenCommute μ ν := by
  have ho := jlmz_open_fubini P Q hP hQ
    (μ.scale μ.normalizer⁻¹) (ν.scale ν.normalizer⁻¹)
    (Valuation.pointContinuous_scale hpoint _)
    (Valuation.normalized_subprobability hμ) (Valuation.normalized_subprobability hν)
  have he := (ho.scale_left μ.normalizer (Valuation.normalizer_ne_top hμ)).scale_right
    ν.normalizer (Valuation.normalizer_ne_top hν)
  simpa only [Valuation.unnormalize hμ,Valuation.unnormalize hν] using he

/-- Finite point-continuous valuations are central against arbitrary partners. -/
theorem finite_point_central (hP : IsDcpo P) (μ : DValuation P)
    (hpoint : PointContinuous μ) (hμ : μ.Finite) : Central.{u,v} μ := by
  intro Q _ hQ ν
  apply (commute_iff_openCommute μ ν).mpr
  obtain ⟨A,hn,hd,hfin,hA⟩ := heckmann_bounded_approximation (WithScott Q) ν
  letI : Nonempty A := hn.to_subtype
  refine openCommute_iSup_right μ ν (fun i : A => i.val) ?_ hA ?_
  · intro i j
    obtain ⟨k,hk,hik,hjk⟩ := hd i i.property j j.property
    exact ⟨⟨k,hk⟩,hik,hjk⟩
  · intro i
    exact finite_point_openCommute hP hQ μ i.val hpoint hμ (hfin i i.property)

/-- Source contract: `cor:point-central` (corollary 2.5).
Version: SHA-256 `134da69fa816824e5fefcb93a4e77a8cd5158c8aaab5ffd288ece2372e55d4e6`.
Locator: `source/manuscript.tex`, lines 166--168; no PDF was supplied.
Formalization status: `proved`; human review is pending.

Strict source TeX:
```latex
\begin{corollary}\label{cor:point-central}
For every dcpo $P$, $\Point(P)\subseteq\Central(P)\subseteq\Val(P)$.
\end{corollary}
```
-/
theorem point_central (P : Type u) [PartialOrder P] (hP : IsDcpo P)
    (μ : DValuation P) (hpoint : PointContinuous μ) : Central.{u,v} μ := by
  intro Q _ hQ ν
  apply (commute_iff_openCommute μ ν).mpr
  obtain ⟨A,hn,hd,hfin,hA⟩ := heckmann_point_bounded_approximation (WithScott P) μ hpoint
  letI : Nonempty A := hn.to_subtype
  refine openCommute_iSup_left μ ν (fun i : A => i.val) ?_ hA ?_
  · intro i j
    obtain ⟨k,hk,hik,hjk⟩ := hd i i.property j j.property
    exact ⟨⟨k,hk⟩,hik,hjk⟩
  · intro i
    exact (commute_iff_openCommute i.val ν).mp
      (finite_point_central hP i.val (hfin i i.property).2 (hfin i i.property).1 Q hQ ν)

/-- Source corollary 3.3: every countable dcpo is a Fubini object. -/
theorem countable_fubini (P : Type u) [PartialOrder P] [Countable P] (hP : IsDcpo P) :
    FubiniObject.{u,v} P :=
  countable_fubini_of_pointCentral point_central P hP

theorem coinitial_fubini (P : Type u) [PartialOrder P] (hP : IsDcpo P)
    (hco : CountablyCoinitialOpens P) : FubiniObject.{u,v} P :=
  coinitial_fubini_of_pointCentral point_central P hP hco

/-- Source contract: `cor:countable-dcpo` (corollary 3.3).
Version: SHA-256 `134da69fa816824e5fefcb93a4e77a8cd5158c8aaab5ffd288ece2372e55d4e6`.
Locator: `source/manuscript.tex`, lines 284--286; no PDF was supplied.
Formalization status: `proved`; human review is pending.

Strict source TeX:
```latex
\begin{corollary}\label{cor:countable-dcpo}
Let $P$ be a dcpo such that every Scott-open subset has an at most countable order-coinitial subset. Then $\Val(P)=\Point(P)=\Central(P)$. In particular, every countable dcpo is a Fubini object.
\end{corollary}
```
-/
theorem coinitial_classes (P : Type u) [PartialOrder P] (hP : IsDcpo P)
    (hco : CountablyCoinitialOpens P) :
    (Set.univ : Set (DValuation P)) = {μ | PointContinuous μ} ∧
      {μ : DValuation P | PointContinuous μ} = {μ | Central.{u,v} μ} := by
  constructor
  · ext μ; exact ⟨fun _ => coinitial_valuation_pointContinuous P hP hco μ,fun _ => trivial⟩
  · ext μ
    exact ⟨point_central P hP μ,fun _ => coinitial_valuation_pointContinuous P hP hco μ⟩

/-- The finite-to-all clause used in source proposition 2.2 and theorem 4.7. -/
theorem fubini_of_finite (P : Type u) [PartialOrder P]
    (hfin : ∀ μ : DValuation P, μ.Finite → Central.{u,v} μ) : FubiniObject.{u,v} P := by
  intro μ Q _ hQ ν
  apply (commute_iff_openCommute μ ν).mpr
  obtain ⟨A,hn,hd,hfinite,hA⟩ := heckmann_bounded_approximation (WithScott P) μ
  letI : Nonempty A := hn.to_subtype
  refine openCommute_iSup_left μ ν (fun i : A => i.val) ?_ hA ?_
  · intro i j
    obtain ⟨k,hk,hik,hjk⟩ := hd i i.property j j.property
    exact ⟨⟨k,hk⟩,hik,hjk⟩
  · exact fun i => (commute_iff_openCommute _ _).mp (hfin i.val (hfinite i i.property) Q hQ ν)
end PointCentralFubini
