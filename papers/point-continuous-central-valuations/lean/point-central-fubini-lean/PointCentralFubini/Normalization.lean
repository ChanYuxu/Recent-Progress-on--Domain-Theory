import PointCentralFubini.Central
set_option autoImplicit false
open Set Topology TopologicalSpace
open scoped ENNReal
universe u v
namespace PointCentralFubini
variable {P : Type u} {Q : Type v} [PartialOrder P] [PartialOrder Q]

/-- The source's original subprobability convention, including its [0,1]
integrand restriction. -/
def CentralSubprob (μ : DValuation P) : Prop :=
  μ.Subprobability ∧ ∀ (Q : Type v) [PartialOrder Q], IsDcpo Q →
    ∀ ν : DValuation Q, ν.Subprobability →
      ∀ h : P × Q → ℝ≥0∞, ScottContinuous h → (∀ z, h z ≤ 1) →
        integral μ (fun x => integral ν (fun y => h (WithScott.ofScott x,WithScott.ofScott y))) =
          integral ν (fun y => integral μ (fun x => h (WithScott.ofScott x,WithScott.ofScott y)))

private theorem openCommute_of_subprob (μ : DValuation P) (hμ : CentralSubprob.{u,v} μ)
    (hQ : IsDcpo Q) (ν : DValuation Q) (hν : ν.Subprobability) : OpenCommute μ ν := by
  intro W
  have he := hμ.2 Q hQ ν hν (fun z => indicator W (WithScott.toScott z))
    ((isLSC_scott_iff _).mp (indicator_isLSC W)) (by
      classical
      intro z
      change (if WithScott.toScott z ∈ W then (1 : ℝ≥0∞) else 0) ≤ 1
      split_ifs <;> simp)
  change iteratedLeft μ ν (indicator W) = iteratedRight μ ν (indicator W) at he
  rwa [iteratedLeft_indicator,iteratedRight_indicator] at he

/-- Source proposition 2.2, equality of the two centrality conventions. -/
theorem centralSubprob_iff (μ : DValuation P) :
    CentralSubprob.{u,v} μ ↔ μ.Subprobability ∧ Central.{u,v} μ := by
  constructor
  · intro hμ; refine ⟨hμ.1,?_⟩
    intro Q _ hQ ν
    apply (commute_iff_openCommute μ ν).mpr
    obtain ⟨A,hn,hd,hfin,hA⟩ := heckmann_bounded_approximation (WithScott Q) ν
    letI : Nonempty A := hn.to_subtype
    refine openCommute_iSup_right μ ν (fun i : A => i.val) ?_ hA ?_
    · intro i j
      obtain ⟨k,hk,hik,hjk⟩ := hd i i.property j j.property
      exact ⟨⟨k,hk⟩,hik,hjk⟩
    · intro i
      have hi := hfin i i.property
      have he := (openCommute_of_subprob μ hμ hQ (i.val.scale i.val.normalizer⁻¹)
        (Valuation.normalized_subprobability hi)).scale_right
          i.val.normalizer (Valuation.normalizer_ne_top hi)
      simpa only [Valuation.unnormalize hi] using he
  · rintro ⟨hprob,hcentral⟩
    exact ⟨hprob,fun Q _ hQ ν _ h hh _ => hcentral Q hQ ν h hh⟩

 theorem Central.scale {μ : DValuation P} (hμ : Central.{u,v} μ)
    (a : ℝ≥0∞) (ha : a ≠ ⊤) : Central.{u,v} (μ.scale a) := by
  intro Q _ hQ ν
  exact (commute_iff_openCommute _ _).mpr
    (((commute_iff_openCommute μ ν).mp (hμ Q hQ ν)).scale_left a ha)

/-- Source contract: `prop:normalization` (proposition 2.2).
Version: SHA-256 `134da69fa816824e5fefcb93a4e77a8cd5158c8aaab5ffd288ece2372e55d4e6`.
Locator: `source/manuscript.tex`, lines 143--145; no PDF was supplied.
Formalization status: `proved`; human review is pending.

Strict source TeX:
```latex
\begin{proposition}\label{prop:normalization}
For every dcpo $P$, $\CentralSub(P)=\Central(P)\cap\ValSub(P)$. The following conditions are equivalent: all subprobability valuations on $P$ are central in the subprobability sense; all finite continuous valuations on $P$ are central in the extended sense; all continuous valuations on $P$ are central in the extended sense.
\end{proposition}
```
-/
theorem normalization (P : Type u) [PartialOrder P] :
    ((∀ μ : DValuation P, μ.Subprobability → CentralSubprob.{u,v} μ) ↔
      (∀ μ : DValuation P, μ.Finite → Central.{u,v} μ)) ∧
    ((∀ μ : DValuation P, μ.Finite → Central.{u,v} μ) ↔ FubiniObject.{u,v} P) := by
  constructor
  · constructor
    · intro h μ hfin
      have hc := (centralSubprob_iff _).mp (h (μ.scale μ.normalizer⁻¹)
        (Valuation.normalized_subprobability hfin)) |>.2
      have he := hc.scale μ.normalizer (Valuation.normalizer_ne_top hfin)
      simpa only [Valuation.unnormalize hfin] using he
    · intro h μ hprob
      exact (centralSubprob_iff μ).mpr ⟨hprob,h μ
        (ne_top_of_le_ne_top (by norm_num) hprob)⟩
  · exact ⟨fubini_of_finite P,fun h μ _ => h μ⟩

private theorem incidence_eval_isLSC (ξ : DValuation (ScottOpens P)) :
    IsLSC (fun x : WithScott P => ξ (neighbourhoodMap P (WithScott.ofScott x))) :=
  scott_isLSC ((neighbourhoodMap_scott P).comp ξ.continuous)

 theorem IncidenceIdentity.scale {μ : DValuation P} {ξ : DValuation (ScottOpens P)}
    (h : IncidenceIdentity μ ξ) (a : ℝ≥0∞) (ha : a ≠ ⊤) :
    IncidenceIdentity μ (ξ.scale a) := by
  unfold IncidenceIdentity at h ⊢
  change integral (ξ.scale a) (fun U => μ (WithScott.ofScott U)) =
    integral μ (fun x => a * ξ (neighbourhoodMap P (WithScott.ofScott x)))
  rw [integral_scale ξ a ha, fpr_integral_smul μ a _ (incidence_eval_isLSC ξ)]
  exact congrArg (fun x => a*x) h

/-- Finite incidence tests suffice, source corollary 2.9. -/
theorem incidence_of_finite_tests (μ : DValuation P)
    (hfinite : ∀ ξ : DValuation (ScottOpens P), ξ.Finite → IncidenceIdentity μ ξ)
    (ξ : DValuation (ScottOpens P)) : IncidenceIdentity μ ξ := by
  obtain ⟨A,hn,hd,hfin,hA⟩ := heckmann_bounded_approximation (WithScott (ScottOpens P)) ξ
  letI : Nonempty A := hn.to_subtype
  have hdir : Directed (· ≤ ·) (fun i : A => i.val) := by
    intro i j
    obtain ⟨k,hk,hik,hjk⟩ := hd i i.property j j.property
    exact ⟨⟨k,hk⟩,hik,hjk⟩
  unfold IncidenceIdentity
  rw [integral_valuation_iSup ξ (fun i : A => i.val) hdir hA _ (scott_isLSC μ.continuous)]
  have he : (fun x : WithScott P => ξ (neighbourhoodMap P (WithScott.ofScott x))) =
      (fun x => ⨆ i : A, i.val (neighbourhoodMap P (WithScott.ofScott x))) :=
    funext fun x => hA _
  rw [he, fpr_integral_iSup μ _ (fun i : A => incidence_eval_isLSC i.val)
    (fun i j => by
      obtain ⟨k,hik,hjk⟩ := hdir i j
      exact ⟨k,fun x => hik _,fun x => hjk _⟩)]
  exact iSup_congr fun i => hfinite i.val (hfin i i.property)

/-- Source contract: `cor:incidence-subprobability` (corollary 2.9).
Version: SHA-256 `134da69fa816824e5fefcb93a4e77a8cd5158c8aaab5ffd288ece2372e55d4e6`.
Locator: `source/manuscript.tex`, lines 225--227; no PDF was supplied.
Formalization status: `proved`; human review is pending.

Strict source TeX:
```latex
\begin{corollary}\label{cor:incidence-subprobability}
A continuous valuation $\mu\in\Val(P)$ is central if and only if \eqref{eq:incidence} holds for every finite continuous valuation $\xi$ on $\sigma(P)$, equivalently, for every $\xi\in\ValSub(\sigma(P))$.
\end{corollary}
```
-/
theorem central_iff_finite_incidence (μ : DValuation P) :
    (Central.{u,u} μ ↔ ∀ ξ : DValuation (ScottOpens P), ξ.Finite → IncidenceIdentity μ ξ) ∧
    (Central.{u,u} μ ↔ ∀ ξ : DValuation (ScottOpens P), ξ.Subprobability → IncidenceIdentity μ ξ) := by
  have hf : Central.{u,u} μ ↔ ∀ ξ : DValuation (ScottOpens P), ξ.Finite → IncidenceIdentity μ ξ :=
    ⟨fun h ξ _ => incidence_of_central μ h ξ,
      fun h => central_of_incidence μ (incidence_of_finite_tests μ h)⟩
  refine ⟨hf,?_⟩
  constructor
  · intro h ξ _; exact incidence_of_central μ h ξ
  · intro h; apply hf.mpr; intro ξ hξ
    have he := (h (ξ.scale ξ.normalizer⁻¹) (Valuation.normalized_subprobability hξ)).scale
      ξ.normalizer (Valuation.normalizer_ne_top hξ)
    simpa only [Valuation.unnormalize hξ] using he
end PointCentralFubini
