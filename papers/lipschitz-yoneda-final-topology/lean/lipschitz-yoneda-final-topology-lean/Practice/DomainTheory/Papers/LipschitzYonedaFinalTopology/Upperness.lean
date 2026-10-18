import Mathlib.Topology.Inseparable
import Practice.DomainTheory.Papers.LipschitzYonedaFinalTopology.QuasiMetric

/-!
# Upperness of layerwise-open subsets

This is `lem:upper` from the manuscript.  The proof uses only cofinal integer
layers, the fact that the ambient function space has its Scott topology, and
the exact restriction theorem for specialization along subtype embeddings.
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

open Set Topology
open scoped NNReal ENNReal Topology

universe u

namespace LipschitzYonedaFinalTopology
namespace QuasiMetric

variable {X : Type u} (d : QuasiMetric X)

/-- Lemma `lem:upper`: a subset of `𝓛∞` which is open on every fixed
integer Lipschitz layer is upward closed for the pointwise order. -/
theorem layerwiseOpen_isUpper
    {U : Set d.LInf}
    (hU : ∀ n : ℕ,
      IsOpen ((↑) ⁻¹' U : Set (d.integerLayer n))) :
    IsUpperSet U := by
  intro f g hfg hfU
  obtain ⟨nf, hnf⟩ := d.integerLayer_cover f
  obtain ⟨ng, hng⟩ := d.integerLayer_cover g
  let n := max nf ng
  have hfn : f ∈ d.integerLayer n :=
    d.integerLayer_mono (le_max_left _ _) hnf
  have hgn : g ∈ d.integerLayer n :=
    d.integerLayer_mono (le_max_right _ _) hng
  let fn : d.integerLayer n := ⟨f, hfn⟩
  let gn : d.integerLayer n := ⟨g, hgn⟩
  have hfgAmbient : (f.1 : d.LSpace) ≤ g.1 := hfg
  have hspecAmbient : (g.1 : d.LSpace) ⤳ f.1 := by
    rw [specializes_iff_forall_open]
    intro O hO hfO
    exact (Topology.IsScott.isUpperSet_of_isOpen (D := Set.univ) hO)
      hfgAmbient hfO
  have hspecInf : g ⤳ f :=
    (subtype_specializes_iff g f).2 hspecAmbient
  have hspecLayer : gn ⤳ fn :=
    (subtype_specializes_iff gn fn).2 hspecInf
  exact hspecLayer.mem_open (hU n) hfU

end QuasiMetric
end LipschitzYonedaFinalTopology
