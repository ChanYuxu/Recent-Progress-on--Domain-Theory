import CantorFubini.ValuationStrength
import CantorFubini.ValuationIntegral
import CantorFubini.ValuationIntegralLinearity

/-! Integral continuity and the actual subprobability valuation monad on DCPO.
Every law below is proved for the actual integration/pushforward constructions.
The commutativity obstruction will compare the two categorical composites of
the constructed strength and multiplication. -/

set_option autoImplicit false
open Set Topology TopologicalSpace CategoryTheory
open scoped ENNReal Classical MonoidalCategory
universe u v

namespace CantorFubini

theorem ennreal_scott_Ioi_isOpen (a : ℝ≥0∞) :
    IsOpen {b : WithScott ℝ≥0∞ | a < WithScott.ofScott b} := by
  have hc : IsClosed (Iic (WithScott.toScott a)) := isClosed_Iic
  convert hc.isOpen_compl using 1
  ext b
  change (a < WithScott.ofScott b) ↔ ¬ WithScott.ofScott b ≤ a
  exact lt_iff_not_ge

theorem scottContinuous_isVLSC {D : Type u} [PartialOrder D]
    {f : D → ℝ≥0∞} (hf : ScottContinuous f) :
    IsVLSC (fun x : WithScott D => f (WithScott.ofScott x)) := by
  intro a
  exact (ennreal_scott_Ioi_isOpen a).preimage ((scott_continuous_iff f).mp hf)

namespace SubprobValuation
variable {X : Type u} [TopologicalSpace X]

theorem integral_scottContinuous {f : X → ℝ≥0∞} (hf : IsVLSC f) :
    ScottContinuous (fun μ : SubprobValuation X => vIntegral μ.val f) := by
  intro S hn hd p hp
  let g : S → SubprobValuation X := Subtype.val
  have hg : Directed (· ≤ ·) g := hd.directed_val
  have hl : IsLUB S (directedSup g hg) := by
    simpa only [g, Subtype.range_val] using directedSup_isLUB g hg
  rw [hp.unique hl]
  letI : Nonempty S := hn.to_subtype
  have he := vIntegral_iSup_valuation (fun s : S => s.val.val)
    (directedSup g hg).val hg (fun _ => rfl) hf
  change IsLUB ((fun μ : SubprobValuation X => vIntegral μ.val f) '' S)
    (vIntegral (directedSup g hg).val f)
  rw [he]
  convert (isLUB_iSup : IsLUB (range (fun s : S => vIntegral s.val.val f))
    (⨆ s : S, vIntegral s.val.val f)) using 1
  ext a
  simp only [mem_image, mem_range, Subtype.exists, exists_prop]

theorem integral_le_one (μ : SubprobValuation X) {f : X → ℝ≥0∞}
    (hf : ∀ x, f x ≤ 1) : vIntegral μ.val f ≤ 1 := by
  calc
    vIntegral μ.val f ≤ vIntegral μ.val (fun _ => 1) := vIntegral_mono μ.val hf
    _ = μ.val ⊤ := by rw [vIntegral_const, one_mul]
    _ ≤ 1 := μ.property

theorem integral_dirac (x : X) {f : X → ℝ≥0∞} (hf : IsVLSC f) :
    vIntegral (dirac x).val f = f x := by
  apply vIntegral_of_dirac_mass _ x _ hf
  intro U
  change (if x ∈ U then 1 else 0) = (U : Set X).indicator (fun _ => 1) x
  by_cases hx : x ∈ U <;> simp [hx]

end SubprobValuation

namespace DCPO

theorem valuationEvaluation_isVLSC (D : DCPO.{u}) (U : ScottOpens D) :
    IsVLSC (fun μ : WithScott (valuations D) => (WithScott.ofScott μ).val U) :=
  scottContinuous_isVLSC (SubprobValuation.evaluation_scottContinuous U)

theorem kernelIntegral_isVLSC {D : DCPO.{u}} {X : Type v} [TopologicalSpace X]
    (k : D → SubprobValuation X) (hk : ScottContinuous k)
    {f : X → ℝ≥0∞} (hf : IsVLSC f) :
    IsVLSC (fun x : WithScott D => vIntegral (k (WithScott.ofScott x)).val f) :=
  scottContinuous_isVLSC (hk.comp (SubprobValuation.integral_scottContinuous hf))

def kernelEval {D E : DCPO.{u}} (k : D ⟶ valuations E) (U : ScottOpens E) :
    WithScott D → ℝ≥0∞ := fun x => (k (WithScott.ofScott x)).val U

theorem kernelEval_isVLSC {D E : DCPO.{u}} (k : D ⟶ valuations E) (U : ScottOpens E) :
    IsVLSC (kernelEval k U) :=
  scottContinuous_isVLSC ((hom_scottContinuous k).comp
    (SubprobValuation.evaluation_scottContinuous U))

/-- The actual Kleisli extension, constructed by integrating the kernel's
open-set evaluations. Strictness, modularity and arbitrary directed continuity
are proved here, rather than postulated in a bundled operation. -/
noncomputable def bindValuation {D E : DCPO.{u}} (μ : valuations D)
    (k : D ⟶ valuations E) : Valuation (WithScott E) where
  mass U := vIntegral μ.val (kernelEval k U)
  strict := by
    have he : kernelEval k ⊥ = fun _ => 0 := funext (fun x => (k _).val.strict)
    rw [he, vIntegral_zero]
  modular U V := by
    rw [← vIntegral_add μ.val (kernelEval_isVLSC k U) (kernelEval_isVLSC k V),
      ← vIntegral_add μ.val (kernelEval_isVLSC k (U ⊔ V))
        (kernelEval_isVLSC k (U ⊓ V))]
    congr 1
    funext x
    exact (k (WithScott.ofScott x)).val.modular U V
  continuous := by
    intro A hn hd p hp
    letI : Nonempty A := hn.to_subtype
    have hA : Directed (· ≤ ·) (fun s : A => (s : ScottOpens E)) := hd.directed_val
    have hp' : p = ⨆ s : A, (s : ScottOpens E) := by
      apply hp.unique
      simpa only [Subtype.range_val] using
        (isLUB_iSup : IsLUB (range (fun s : A => (s : ScottOpens E))) (⨆ s : A, s.val))
    have he : kernelEval k p = fun x => ⨆ s : A, kernelEval k s.val x := by
      funext x
      exact hp' ▸ (k (WithScott.ofScott x)).val.map_iSup _ hA
    have hdir : Directed (· ≤ ·) (fun s : A => kernelEval k s.val) := by
      intro s t
      obtain ⟨r, hsr, htr⟩ := hA s t
      exact ⟨r, (fun x => (k _).val.mono hsr), (fun x => (k _).val.mono htr)⟩
    have hi : vIntegral μ.val (kernelEval k p) =
        ⨆ s : A, vIntegral μ.val (kernelEval k s.val) := by
      rw [he]
      exact vIntegral_iSup_directed μ.val (fun s : A => kernelEval k s.val)
        (fun s => kernelEval_isVLSC k s.val) hdir
    change IsLUB ((fun U => vIntegral μ.val (kernelEval k U)) '' A)
      (vIntegral μ.val (kernelEval k p))
    rw [hi]
    convert (isLUB_iSup : IsLUB
      (range (fun s : A => vIntegral μ.val (kernelEval k s.val)))
      (⨆ s : A, vIntegral μ.val (kernelEval k s.val))) using 1
    ext a
    simp only [mem_image, mem_range, Subtype.exists, exists_prop]

noncomputable def bind {D E : DCPO.{u}} (μ : valuations D)
    (k : D ⟶ valuations E) : valuations E :=
  ⟨bindValuation μ k, SubprobValuation.integral_le_one μ
    (fun x => (k (WithScott.ofScott x)).property)⟩

@[simp] theorem bind_apply {D E : DCPO.{u}} (μ : valuations D)
    (k : D ⟶ valuations E) (U : ScottOpens E) :
    (bind μ k).val U = vIntegral μ.val (kernelEval k U) := rfl

noncomputable def extend {D E : DCPO.{u}} (k : D ⟶ valuations E) :
    valuations D ⟶ valuations E :=
  hom (fun μ => bind μ k) (SubprobValuation.scottContinuous_of_evaluations
    (fun U => SubprobValuation.integral_scottContinuous (kernelEval_isVLSC k U)))

@[simp] theorem extend_apply {D E : DCPO.{u}} (k : D ⟶ valuations E)
    (μ : valuations D) : extend k μ = bind μ k := rfl

theorem bind_dirac {D E : DCPO.{u}} (x : D) (k : D ⟶ valuations E) :
    bind (point D x) k = k x := by
  apply SubprobValuation.ext
  intro U
  exact SubprobValuation.integral_dirac (WithScott.toScott x) (kernelEval_isVLSC k U)

theorem bind_point (D : DCPO.{u}) (μ : valuations D) : bind μ (point D) = μ := by
  apply SubprobValuation.ext
  intro U
  have he : kernelEval (point D) U = (U : Set (WithScott D)).indicator (fun _ => 1) := by
    funext x
    change (if x ∈ U then 1 else 0) = (U : Set (WithScott D)).indicator (fun _ => 1) x
    by_cases hx : x ∈ U <;> simp [hx]
  change vIntegral μ.val (kernelEval (point D) U) = μ.val U
  rw [he, vIntegral_indicator, one_mul]

/-- Substitution for the constructed extension. The proof identifies the
concrete iterated-integral functional by its proved indicator and directed
continuity laws. It does not exchange the order of two integrations. -/
theorem bind_integral {D E : DCPO.{u}} (μ : valuations D)
    (k : D ⟶ valuations E) {f : WithScott E → ℝ≥0∞} (hf : IsVLSC f) :
    vIntegral (bind μ k).val f =
      vIntegral μ.val (fun x : WithScott D => vIntegral (k (WithScott.ofScott x)).val f) := by
  let L : (WithScott E → ℝ≥0∞) → ℝ≥0∞ :=
    fun g => vIntegral μ.val (fun x => vIntegral (k (WithScott.ofScott x)).val g)
  apply (vIntegral_unique (bind μ k).val L ?_ ?_ ?_ hf).symm
  · change vIntegral μ.val (fun x => vIntegral (k (WithScott.ofScott x)).val (fun _ => 0)) = 0
    simp only [vIntegral_zero]
  · intro g hg U c hc
    have he : (fun x : WithScott D => vIntegral (k (WithScott.ofScott x)).val
        (fun y => g y + (U : Set (WithScott E)).indicator (fun _ => c) y)) =
        fun x : WithScott D => vIntegral (k (WithScott.ofScott x)).val g +
          c * (k (WithScott.ofScott x)).val U := by
      funext x
      exact vIntegral_add_indicator _ hg U c hc
    change vIntegral μ.val _ = vIntegral μ.val _ + c * (bind μ k).val U
    rw [he]
    change vIntegral μ.val (fun x : WithScott D =>
      vIntegral (k (WithScott.ofScott x)).val g + c * kernelEval k U x) =
      vIntegral μ.val (fun x : WithScott D => vIntegral (k (WithScott.ofScott x)).val g) +
        c * vIntegral μ.val (kernelEval k U)
    rw [vIntegral_add μ.val (kernelIntegral_isVLSC k (hom_scottContinuous k) hg)
      ((kernelEval_isVLSC k U).const_mul c),
      vIntegral_const_mul μ.val c (kernelEval_isVLSC k U)]
  · intro g hg hm
    have he : (fun x : WithScott D => vIntegral (k (WithScott.ofScott x)).val
        (fun y => ⨆ n : ℕ, g n y)) =
        fun x : WithScott D => ⨆ n : ℕ, vIntegral (k (WithScott.ofScott x)).val (g n) := by
      funext x
      exact vIntegral_iSup_directed _ g hg hm.directed_le
    have hinner : ∀ n, IsVLSC (fun x : WithScott D =>
        vIntegral (k (WithScott.ofScott x)).val (g n)) :=
      fun n => kernelIntegral_isVLSC k (hom_scottContinuous k) (hg n)
    have hmono : Monotone (fun n => fun x : WithScott D =>
        vIntegral (k (WithScott.ofScott x)).val (g n)) := by
      intro n m hnm x
      exact vIntegral_mono _ (hm hnm)
    change vIntegral μ.val _ = ⨆ n, vIntegral μ.val _
    rw [he, vIntegral_iSup_directed μ.val _ hinner hmono.directed_le]

/-- The actual multiplication integrates the evaluation functions. -/
noncomputable def join (D : DCPO.{u}) : valuations (valuations D) ⟶ valuations D :=
  extend (𝟙 (valuations D))

@[simp] theorem join_apply (D : DCPO.{u}) (μ : valuations (valuations D))
    (U : ScottOpens D) :
    (join D μ).val U = vIntegral μ.val
      (fun ν : WithScott (valuations D) => (WithScott.ofScott ν).val U) := rfl

theorem valuationMap_integral {D E : DCPO.{u}} (f : D ⟶ E) (μ : valuations D)
    {g : WithScott E → ℝ≥0∞} (hg : IsVLSC g) :
    vIntegral (valuationMap f μ).val g = vIntegral μ.val
      (fun x : WithScott D => g (WithScott.toScott (f (WithScott.ofScott x)))) :=
  vIntegral_push μ.val _ ((scott_continuous_iff f).mp (hom_scottContinuous f)) hg

theorem join_naturality {D E : DCPO.{u}} (f : D ⟶ E) :
    valuationMap (valuationMap f) ≫ join E = join D ≫ valuationMap f := by
  apply Hom.ext
  intro μ
  apply SubprobValuation.ext
  intro U
  change (join E (valuationMap (valuationMap f) μ)).val U =
    (valuationMap f (join D μ)).val U
  rw [join_apply, valuationMap_integral _ _ (valuationEvaluation_isVLSC E U)]
  rfl

noncomputable def joinNatural : valuationFunctor ⋙ valuationFunctor ⟶ valuationFunctor where
  app := join
  naturality := by
    intro D E f
    exact join_naturality f

theorem join_left_unit (D : DCPO.{u}) : point (valuations D) ≫ join D = 𝟙 (valuations D) := by
  apply Hom.ext
  intro μ
  exact bind_dirac μ (𝟙 (valuations D))

theorem join_right_unit (D : DCPO.{u}) : valuationMap (point D) ≫ join D = 𝟙 (valuations D) := by
  apply Hom.ext
  intro μ
  apply SubprobValuation.ext
  intro U
  change (join D (valuationMap (point D) μ)).val U = μ.val U
  rw [join_apply, valuationMap_integral _ _ (valuationEvaluation_isVLSC D U)]
  exact congrArg (fun ν : valuations D => ν.val U) (bind_point D μ)

theorem join_assoc (D : DCPO.{u}) :
    valuationMap (join D) ≫ join D = join (valuations D) ≫ join D := by
  apply Hom.ext
  intro μ
  apply SubprobValuation.ext
  intro U
  change (join D (valuationMap (join D) μ)).val U =
    (join D (join (valuations D) μ)).val U
  rw [join_apply, valuationMap_integral _ _ (valuationEvaluation_isVLSC D U)]
  change vIntegral μ.val _ =
    vIntegral (bind μ (𝟙 (valuations (valuations D)))).val
      (fun ν : WithScott (valuations D) => (WithScott.ofScott ν).val U)
  rw [bind_integral _ _ (valuationEvaluation_isVLSC D U)]
  rfl

/-- The subprobability continuous-valuation monad on the actual category of
DCPOs and Scott-continuous maps. All three monad laws are kernel proofs. -/
noncomputable def valuationMonad : CategoryTheory.Monad DCPO.{u} where
  toFunctor := valuationFunctor
  η := pointNatural
  μ := joinNatural
  assoc := join_assoc
  left_unit := join_left_unit
  right_unit := join_right_unit

theorem strength_join (D E : DCPO.{u}) :
    prodMap (𝟙 D) (join E) ≫ strength D E =
      strength D (valuations E) ≫ valuationMap (strength D E) ≫ join (prod D E) := by
  apply Hom.ext
  intro z
  apply SubprobValuation.ext
  intro U
  change (join E z.2).val (leftSection U z.1) =
    (join (prod D E) (valuationMap (strength D E) (strength D (valuations E) z))).val U
  rw [join_apply, join_apply,
    valuationMap_integral _ _ (valuationEvaluation_isVLSC (prod D E) U)]
  symm
  exact vIntegral_push z.2.val _
    ((scott_continuous_iff (insertLeft D (valuations E) z.1)).mp (hom_scottContinuous _))
    ((valuationEvaluation_isVLSC (prod D E) U).comp_continuous _
      ((scott_continuous_iff (strength D E)).mp (hom_scottContinuous _)))

/-- The actual monad equipped with its canonical tensorial strength, including
the proved compatibility of strength with unit and multiplication. -/
noncomputable def valuationMonadStrength : CartesianMonadStrength valuationMonad where
  toCartesianFunctorStrength := valuationFunctorStrength
  unit := strength_point
  multiplication := strength_join

def rightSection {D E : DCPO.{u}} (U : ScottOpens (prod D E)) (y : E) : ScottOpens D :=
  Opens.comap ⟨fun x : WithScott D => WithScott.toScott (WithScott.ofScott x, y),
    ((scott_continuous_iff (insertRight D E y)).mp (hom_scottContinuous _))⟩ U

theorem strength_integral (D E : DCPO.{u}) (z : prod D (valuations E))
    {g : WithScott (prod D E) → ℝ≥0∞} (hg : IsVLSC g) :
    vIntegral (strength D E z).val g = vIntegral z.2.val
      (fun y : WithScott E => g (WithScott.toScott (z.1, WithScott.ofScott y))) :=
  vIntegral_push z.2.val _
    ((scott_continuous_iff (insertLeft D E z.1)).mp (hom_scottContinuous _)) hg

theorem costrength_eq_push (D E : DCPO.{u}) (z : prod (valuations D) E) :
    costrength D E z = z.1.push
      (fun x : WithScott D => WithScott.toScott (WithScott.ofScott x, z.2))
      ((scott_continuous_iff (insertRight D E z.2)).mp (hom_scottContinuous _)) := by
  apply SubprobValuation.ext
  intro U
  rfl

theorem costrength_integral (D E : DCPO.{u}) (z : prod (valuations D) E)
    {g : WithScott (prod D E) → ℝ≥0∞} (hg : IsVLSC g) :
    vIntegral (costrength D E z).val g = vIntegral z.1.val
      (fun x : WithScott D => g (WithScott.toScott (WithScott.ofScott x, z.2))) := by
  rw [costrength_eq_push]
  exact vIntegral_push z.1.val _
    ((scott_continuous_iff (insertRight D E z.2)).mp (hom_scottContinuous _)) hg

/-- Evaluation of the first categorical composite. This is a theorem about
the actual multiplication and strength, obtained by their pushforward laws. -/
theorem doubleLeft_apply (D E : DCPO.{u}) (μ : valuations D) (ν : valuations E)
    (U : ScottOpens (prod D E)) :
    (valuationMonadStrength.doubleLeft D E (μ, ν)).val U =
      vIntegral μ.val (fun x : WithScott D => ν.val (leftSection U (WithScott.ofScott x))) := by
  change (join (prod D E)
    (valuationMap (strength D E) (costrength D (valuations E) (μ, ν)))).val U = _
  rw [join_apply, valuationMap_integral _ _ (valuationEvaluation_isVLSC (prod D E) U)]
  exact costrength_integral D (valuations E) (μ, ν)
    ((valuationEvaluation_isVLSC (prod D E) U).comp_continuous _
      ((scott_continuous_iff (strength D E)).mp (hom_scottContinuous _)))

/-- Evaluation of the second canonical categorical composite. -/
theorem doubleRight_apply (D E : DCPO.{u}) (μ : valuations D) (ν : valuations E)
    (U : ScottOpens (prod D E)) :
    (valuationMonadStrength.doubleRight D E (μ, ν)).val U =
      vIntegral ν.val (fun y : WithScott E => μ.val (rightSection U (WithScott.ofScott y))) := by
  change (join (prod D E)
    (valuationMap (costrength D E) (strength (valuations D) E (μ, ν)))).val U = _
  rw [join_apply, valuationMap_integral _ _ (valuationEvaluation_isVLSC (prod D E) U)]
  exact strength_integral (valuations D) E (μ, ν)
    ((valuationEvaluation_isVLSC (prod D E) U).comp_continuous _
      ((scott_continuous_iff (costrength D E)).mp (hom_scottContinuous _)))

end DCPO
end CantorFubini
