import ZFCFubini.Evaluation
import ZFCFubini.RandomOpen
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! Full source main statement. This file defines a proposition, not its
existence proof. The actual construction must discharge every clause. -/

set_option autoImplicit false
open Set TopologicalSpace Topology
namespace ZFCFubini

noncomputable def sourceQ : ℝ := 1 - ∏' n : ℕ, (1 - 2 * radius n)

def MainStatement : Prop :=
  ∃ (P : Type) (orderP : PartialOrder P),
    letI := orderP
    IsDcpo P ∧
    ∃ (ν : ProbabilityValuation (WithScott P))
      (η : ProbabilityValuation (WithScott (ScottOpens P))),
      ScottContinuous (incidence P) ∧
      paperIntegral η (fun H => paperIntegral ν
        (fun p => (incidence P (WithScott.ofScott p, WithScott.ofScott H)).val)) = 1 ∧
      paperIntegral ν (fun p => paperIntegral η
        (fun H => (incidence P (WithScott.ofScott p, WithScott.ofScott H)).val)) = sourceQ ∧
      0 < sourceQ ∧ sourceQ ≤ 1 / 64 ∧
      ScottContinuous (fun H : ScottOpens P => realMass ν H) ∧
      ScottContinuous (fun p : P => realMass η (evaluationOpen p))

end ZFCFubini
