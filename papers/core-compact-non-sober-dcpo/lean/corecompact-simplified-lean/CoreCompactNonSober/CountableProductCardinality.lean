import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.Logic.Encodable.Basic

/-! # Cardinal upper bound for countable products of countable alphabets -/

set_option autoImplicit false

namespace CoreCompactNonSober

open Cardinal

theorem mk_countable_pi_le_continuum {ι : Type} [Countable ι]
    (X : ι → Type) [∀ i, Countable (X i)] :
    Cardinal.mk ((i : ι) → X i) ≤ Cardinal.continuum := by
  let enc (i : ι) : Encodable (X i) := Encodable.ofCountable (X i)
  let f : ((i : ι) → X i) → (ι → ℕ) :=
    fun x i ↦ @Encodable.encode (X i) (enc i) (x i)
  have hf : Function.Injective f := by
    intro x y h
    funext i
    exact @Encodable.encode_injective (X i) (enc i) (x i) (y i) (congrFun h i)
  calc
    Cardinal.mk ((i : ι) → X i) ≤ Cardinal.mk (ι → ℕ) := Cardinal.mk_le_of_injective hf
    _ = Cardinal.aleph0 ^ Cardinal.mk ι := by simp
    _ ≤ Cardinal.aleph0 ^ Cardinal.aleph0 :=
      Cardinal.power_le_power_left Cardinal.aleph0_ne_zero Cardinal.mk_le_aleph0
    _ = Cardinal.continuum := Cardinal.aleph0_power_aleph0

end CoreCompactNonSober
