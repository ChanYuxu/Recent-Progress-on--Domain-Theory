import PointCentralFubini.Integration

set_option autoImplicit false
open Set Topology TopologicalSpace
open scoped ENNReal
universe u v w z
namespace PointCentralFubini
variable {X : Type u} [TopologicalSpace X]

/-- The functional interface in the source's cited FPR Theorem 3.5. -/
structure FunctionalLaws (F : (X → ℝ≥0∞) → ℝ≥0∞) : Prop where
  add : ∀ f g, IsLSC f → IsLSC g → F (f + g) = F f + F g
  smul : ∀ a f, IsLSC f → F (fun x => a * f x) = a * F f
  iSup : ∀ {ι : Type u} [Nonempty ι] (f : ι → X → ℝ≥0∞),
    (∀ i, IsLSC (f i)) → Directed (· ≤ ·) f →
    F (fun x => ⨆ i, f i x) = ⨆ i, F (f i)

/-- Verified cited reference: uniqueness in the FPR Theorem 3.5 bijection.
The two functionals are only required to agree on indicators of OPEN sets. -/
axiom fpr_functional_unique (F G : (X → ℝ≥0∞) → ℝ≥0∞)
    (hF : FunctionalLaws F) (hG : FunctionalLaws G)
    (hFG : ∀ U : Opens X, F (indicator U) = G (indicator U)) :
    ∀ f, IsLSC f → F f = G f

/-- LSC is continuity into the Scott version of `[0,∞]`. -/
theorem isLSC_iff_continuous (f : X → ℝ≥0∞) : IsLSC f ↔
    Continuous (fun x => WithScott.toScott (f x)) := by
  constructor
  · intro hf; apply continuous_def.mpr; intro S hs
    rcases Topology.IsScott.isOpen_iff_Iic_compl_or_univ S |>.mp hs with rfl | ⟨a,rfl⟩
    · simp
    · convert hf (WithScott.ofScott a) using 1
      ext x
      change (¬ f x ≤ WithScott.ofScott a) ↔ WithScott.ofScott a < f x
      exact not_le
  · intro hf r
    exact (scott_Ioi_open r).preimage hf

theorem isLSC_scott_iff {P : Type u} [Preorder P] (f : WithScott P → ℝ≥0∞) :
    IsLSC f ↔ ScottContinuous (fun x : P => f (WithScott.toScott x)) := by
  rw [isLSC_iff_continuous, scott_continuous_iff]
  rfl

 theorem indicator_isLSC (U : Opens X) : IsLSC (indicator U) := by
  classical
  intro r
  by_cases hr : r < 1
  · have he : {x | r < indicator U x} = (U : Set X) := by
      ext x; by_cases hx : x ∈ U <;> simp [indicator,hx,hr]
    rw [he]; exact U.isOpen
  · have he : {x | r < indicator U x} = (∅ : Set X) := by
      ext x; by_cases hx : x ∈ U <;> simp [indicator,hx,hr]
    rw [he]; exact isOpen_empty

variable {P : Type u} {Q : Type v} [PartialOrder P] [PartialOrder Q]

noncomputable def iteratedLeft (μ : DValuation P) (ν : DValuation Q)
    (f : WithScott (P × Q) → ℝ≥0∞) : ℝ≥0∞ :=
  integral μ (fun x => integral ν
    (fun y => f (WithScott.toScott (WithScott.ofScott x,WithScott.ofScott y))))

noncomputable def iteratedRight (μ : DValuation P) (ν : DValuation Q)
    (f : WithScott (P × Q) → ℝ≥0∞) : ℝ≥0∞ :=
  integral ν (fun y => integral μ
    (fun x => f (WithScott.toScott (WithScott.ofScott x,WithScott.ofScott y))))

 theorem slice_isLSC (f : WithScott (P × Q) → ℝ≥0∞) (hf : IsLSC f) (x : P) :
    IsLSC (fun y : WithScott Q => f (WithScott.toScott (x,WithScott.ofScott y))) := by
  exact hf.comp ((scott_continuous_iff _).mp
    ((ScottContinuous.const x).prodMk ScottContinuous.id))

 theorem innerLeft_isLSC (ν : DValuation Q) (f : WithScott (P × Q) → ℝ≥0∞)
    (hf : IsLSC f) : IsLSC (fun x : WithScott P => integral ν
      (fun y => f (WithScott.toScott (WithScott.ofScott x,WithScott.ofScott y)))) := by
  exact scott_isLSC (innerIntegral_scott ν _ ((isLSC_scott_iff f).mp hf))

 theorem iteratedLeft_laws (μ : DValuation P) (ν : DValuation Q) :
    FunctionalLaws (iteratedLeft μ ν) := by
  constructor
  · intro f g hf hg
    have he : (fun x : WithScott P => integral ν
        (fun y => (f+g) (WithScott.toScott (WithScott.ofScott x,WithScott.ofScott y)))) =
      (fun x => integral ν (fun y => f (WithScott.toScott (WithScott.ofScott x,WithScott.ofScott y)))) +
      (fun x => integral ν (fun y => g (WithScott.toScott (WithScott.ofScott x,WithScott.ofScott y)))) := by
      funext x
      exact fpr_integral_add ν _ _ (slice_isLSC f hf _) (slice_isLSC g hg _)
    unfold iteratedLeft; rw [he]
    exact fpr_integral_add μ _ _ (innerLeft_isLSC ν f hf) (innerLeft_isLSC ν g hg)
  · intro a f hf
    have he : (fun x : WithScott P => integral ν
        (fun y => a * f (WithScott.toScott (WithScott.ofScott x,WithScott.ofScott y)))) =
      (fun x => a * integral ν
        (fun y => f (WithScott.toScott (WithScott.ofScott x,WithScott.ofScott y)))) := by
      funext x
      exact fpr_integral_smul ν a _ (slice_isLSC f hf _)
    unfold iteratedLeft; rw [he]
    exact fpr_integral_smul μ a _ (innerLeft_isLSC ν f hf)
  · intro ι _ f hf hd
    have he : (fun x : WithScott P => integral ν
        (fun y => ⨆ i, f i (WithScott.toScott (WithScott.ofScott x,WithScott.ofScott y)))) =
      (fun x => ⨆ i, integral ν
        (fun y => f i (WithScott.toScott (WithScott.ofScott x,WithScott.ofScott y)))) := by
      funext x
      apply fpr_integral_iSup ν _ (fun i => slice_isLSC (f i) (hf i) _)
      intro i j; obtain ⟨k,hik,hjk⟩ := hd i j
      exact ⟨k,fun y => hik _,fun y => hjk _⟩
    unfold iteratedLeft; rw [he]
    apply fpr_integral_iSup μ _ (fun i => innerLeft_isLSC ν (f i) (hf i))
    intro i j; obtain ⟨k,hik,hjk⟩ := hd i j
    exact ⟨k,fun x => integral_mono ν (fun y => hik _),
      fun x => integral_mono ν (fun y => hjk _)⟩

/-- Scott-open sections in the other coordinate. -/
def sliceRight (W : ScottOpens (P × Q)) (x : P) : ScottOpens Q := by
  refine ⟨{y | WithScott.toScott (x,WithScott.ofScott y) ∈ W}, ?_⟩
  exact W.isOpen.preimage ((scott_continuous_iff _).mp
    ((ScottContinuous.const x).prodMk ScottContinuous.id))

/-- Characteristic-function Fubini tests, as in JLMZ Theorem 21. -/
def OpenCommute (μ : DValuation P) (ν : DValuation Q) : Prop :=
  ∀ W : ScottOpens (P × Q),
    integral μ (fun x => ν (sliceRight W (WithScott.ofScott x))) =
      integral ν (fun y => μ (sectionMap W (WithScott.ofScott y)))

end PointCentralFubini

namespace PointCentralFubini
open Set Topology TopologicalSpace
open scoped ENNReal
variable {P : Type u} {Q : Type v} [PartialOrder P] [PartialOrder Q]

def swapScott : WithScott (Q × P) → WithScott (P × Q) :=
  fun z => WithScott.toScott (WithScott.ofScott z).swap

theorem swapScott_continuous : Continuous (swapScott (P := P) (Q := Q)) :=
  (scott_continuous_iff _).mp (ScottContinuous.snd.prodMk ScottContinuous.fst)

theorem iteratedRight_laws (μ : DValuation P) (ν : DValuation Q) :
    FunctionalLaws (iteratedRight μ ν) := by
  have h := iteratedLeft_laws ν μ
  constructor
  · intro f g hf hg
    exact h.add (f ∘ swapScott) (g ∘ swapScott)
      (hf.comp swapScott_continuous) (hg.comp swapScott_continuous)
  · intro a f hf
    exact h.smul a (f ∘ swapScott) (hf.comp swapScott_continuous)
  · intro ι _ f hf hd
    exact h.iSup (fun i => f i ∘ swapScott) (fun i => (hf i).comp swapScott_continuous)
      (fun i j => by
        obtain ⟨k,hik,hjk⟩ := hd i j
        exact ⟨k,fun x => hik _,fun x => hjk _⟩)

theorem iteratedLeft_indicator (μ : DValuation P) (ν : DValuation Q)
    (W : ScottOpens (P × Q)) : iteratedLeft μ ν (indicator W) =
      integral μ (fun x => ν (sliceRight W (WithScott.ofScott x))) := by
  apply integral_congr μ
  intro x
  exact integral_indicator ν (sliceRight W (WithScott.ofScott x))

theorem iteratedRight_indicator (μ : DValuation P) (ν : DValuation Q)
    (W : ScottOpens (P × Q)) : iteratedRight μ ν (indicator W) =
      integral ν (fun y => μ (sectionMap W (WithScott.ofScott y))) := by
  apply integral_congr ν
  intro y
  exact integral_indicator μ (sectionMap W (WithScott.ofScott y))

/-- Open tests suffice for arbitrary nonnegative Scott-continuous integrands.
Uses precisely the cited functional representation theorem, not a product
measure or an assumption that Scott product and topological product coincide. -/
theorem commute_iff_openCommute (μ : DValuation P) (ν : DValuation Q) :
    Commute μ ν ↔ OpenCommute μ ν := by
  constructor
  · intro h W
    have hh := h (fun z => indicator W (WithScott.toScott z))
      ((isLSC_scott_iff _).mp (indicator_isLSC W))
    change iteratedLeft μ ν (indicator W) = iteratedRight μ ν (indicator W) at hh
    rwa [iteratedLeft_indicator,iteratedRight_indicator] at hh
  · intro ho h hh
    have he := fpr_functional_unique (iteratedLeft μ ν) (iteratedRight μ ν)
      (iteratedLeft_laws μ ν) (iteratedRight_laws μ ν)
      (fun W => by rw [iteratedLeft_indicator,iteratedRight_indicator]; exact ho W)
      (fun z => h (WithScott.ofScott z)) (scott_isLSC hh)
    exact he
end PointCentralFubini
