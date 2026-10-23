import CHFubini.Choquet
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! The exact main conclusion is encoded separately from its existence proof.
`PaperMainClaim` is currently a proposition definition, NOT a theorem.
In particular this module does not prove the main theorem by taking its
construction or conclusions as parameters.
-/

set_option autoImplicit false
open Set Topology TopologicalSpace MeasureTheory
open scoped ENNReal
namespace CHFubini

/-- The source's n≥1 convention is reindexed as n+1 for Lean's n:ℕ. -/
noncomputable def intervalLength (ε : ℝ) (n : ℕ) : ℝ := ε * (1 / 2 : ℝ) ^ (n + 1)

/-- Equation (1.2). Multipliability for 0<ε<1 is a separate proof obligation. -/
noncomputable def qEpsilon (ε : ℝ) : ℝ := 1 - ∏' n : ℕ, (1 - intervalLength ε n)

/-- Main Theorem 1.1, including its actual probability valuations, two
iterated Choquet integrals, order-product Scott open, and both Scott profiles.
The witnesses live in Type 0, as do the manuscript's circle/subset constructions.
-/
def CounterexampleAt (ε : ℝ) : Prop :=
  ∃ (P : Type) (orderP : PartialOrder P) (L : Type) (latticeL : CompleteLattice L),
    letI := orderP
    letI := latticeL
    IsDcpo P ∧ FirstCountableTopology (WithScott P) ∧ IsSober (WithScott P) ∧
    IsWellFiltered (WithScott P) ∧ IsWellFiltered (WithScott L) ∧
    ∃ (μ : DValuation P) (ρ : DValuation L) (W : ScottOpens (P × L)),
      μ.Probability ∧ ρ.Probability ∧
      choquetIntegral ρ
          (fun V => choquetIntegral μ (indicator (leftSection W (WithScott.ofScott V)))) = 1 ∧
      choquetIntegral μ
          (fun C => choquetIntegral ρ (indicator (rightSection W (WithScott.ofScott C)))) =
            ENNReal.ofReal (qEpsilon ε) ∧
      0 < qEpsilon ε ∧ qEpsilon ε ≤ ε ∧ ε < 1 ∧
      ScottContinuous (fun V : L => μ (leftSection W V)) ∧
      ScottContinuous (fun C : P => ρ (rightSection W C))

/-- Statement of the source main theorem. No evidence is introduced here. -/
def PaperMainClaim : Prop := CH → ∀ ε : ℝ, 0 < ε → ε < 1 → CounterexampleAt ε

end CHFubini
