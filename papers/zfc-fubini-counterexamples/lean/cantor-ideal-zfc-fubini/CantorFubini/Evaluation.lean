/- Adapted from ZFC_Fubini_Lean/ZFCFubini/Evaluation.lean; original SHA256 a977a3d895dc253211cd4c28cd50e6225ff67beb210b8b3018e25bd683ca3fbe. Current source is formalized-manuscript.tex. -/
import CantorFubini.PaperIntegral

/-! The literal incidence function on the ORDER product and the real [0,1]
Scott codomain. No ordinary product topology is substituted. -/

set_option autoImplicit false
open Set Topology TopologicalSpace
open scoped Classical
universe u
namespace CantorFubini

noncomputable def unitIndicator {P : Type u} [PartialOrder P]
    (W : ScottOpens P) (p : P) : UnitInterval := by
  classical
  exact if WithScott.toScott p ∈ W then unitOne else unitZero

theorem unitIndicator_scottContinuous {P : Type u} [PartialOrder P]
    (W : ScottOpens P) : ScottContinuous (unitIndicator W) := by
  classical
  have hup : IsUpperSet (W : Set (WithScott P)) :=
    IsScott.isUpperSet_of_isOpen (D := univ) W.isOpen
  have hacc : DirSupInaccOn univ (W : Set (WithScott P)) :=
    (IsScott.isOpen_iff_isUpperSet_and_dirSupInaccOn (D := univ)).mp W.isOpen |>.2
  intro D hn hd p hp
  by_cases hpW : WithScott.toScott p ∈ W
  · have he : unitIndicator W p = unitOne := by simp [unitIndicator, hpW]
    rw [he]
    refine ⟨?_, ?_⟩
    · rintro b ⟨d, _, rfl⟩
      exact (unitIndicator W d).property.2
    · intro b hb
      obtain ⟨d, hdD, hdW⟩ := hacc (mem_univ _) hn hd hp hpW
      have hdW' : WithScott.toScott d ∈ W := hdW
      have hd1 : unitIndicator W d = unitOne := by
        change (if d ∈ W then unitOne else unitZero) = unitOne
        exact if_pos hdW
      simpa only [hd1] using hb (mem_image_of_mem (unitIndicator W) hdD)
  · have hall : ∀ d ∈ D, unitIndicator W d = unitZero := by
      intro d hdD
      have hdW : WithScott.toScott d ∉ W := fun hw => hpW (hup (hp.1 hdD) hw)
      simp [unitIndicator, hdW]
    have he : unitIndicator W p = unitZero := by simp [unitIndicator, hpW]
    rw [he]
    refine ⟨?_, ?_⟩
    · rintro b ⟨d, hdD, rfl⟩
      rw [hall d hdD]
    · intro b hb
      obtain ⟨d, hdD⟩ := hn
      simpa only [hall d hdD] using hb (mem_image_of_mem (unitIndicator W) hdD)

def incidenceSet (P : Type u) [PartialOrder P] : Set (P × ScottOpens P) :=
  {z | WithScott.toScott z.1 ∈ z.2}

theorem incidenceSet_isOpen (P : Type u) [PartialOrder P] :
    IsOpen (WithScott.ofScott ⁻¹' incidenceSet P) := by
  rw [IsScott.isOpen_iff_isUpperSet_and_dirSupInaccOn (D := univ)]
  refine ⟨?_, ?_⟩
  · intro a b hab ha
    exact hab.2 ((IsScott.isUpperSet_of_isOpen (D := univ) a.2.isOpen) hab.1 ha)
  · intro D _ hn hd z hlub hz
    have hfst : IsLUB (Prod.fst '' D) z.1 := ScottContinuous.fst hn hd hlub
    have hsnd : IsLUB (Prod.snd '' D) z.2 := ScottContinuous.snd hn hd hlub
    have hH : z.2 = sSup (Prod.snd '' D) := hsnd.unique (isLUB_sSup _)
    have hzH : WithScott.toScott z.1 ∈ sSup (Prod.snd '' D) := hH ▸ hz
    obtain ⟨H, hHD, hpH⟩ := Opens.mem_sSup.mp hzH
    obtain ⟨a, haD, rfl⟩ := hHD
    have hdir : DirectedOn (· ≤ ·) (Prod.fst '' D) :=
      directedOn_image.mpr (hd.mono (fun {_ _} h => h.1))
    have hacc : DirSupInaccOn univ (a.2 : Set (WithScott P)) :=
      (IsScott.isOpen_iff_isUpperSet_and_dirSupInaccOn (D := univ)).mp a.2.isOpen |>.2
    obtain ⟨p, hpD, hp⟩ := hacc (mem_univ _) (hn.image Prod.fst) hdir hfst hpH
    obtain ⟨b, hbD, rfl⟩ := hpD
    obtain ⟨c, hcD, hac, hbc⟩ := hd a haD b hbD
    refine ⟨c, hcD, ?_⟩
    exact hac.2 ((IsScott.isUpperSet_of_isOpen (D := univ) a.2.isOpen) hbc.1 hp)

def incidenceOpen (P : Type u) [PartialOrder P] : ScottOpens (P × ScottOpens P) :=
  ⟨WithScott.ofScott ⁻¹' incidenceSet P, incidenceSet_isOpen P⟩

noncomputable def incidence (P : Type u) [PartialOrder P] :
    P × ScottOpens P → UnitInterval := unitIndicator (incidenceOpen P)

theorem incidence_scottContinuous (P : Type u) [PartialOrder P] :
    ScottContinuous (incidence P) := unitIndicator_scottContinuous _

@[simp] theorem incidence_value (P : Type u) [PartialOrder P]
    (p : P) (H : ScottOpens P) :
    (incidence P (p, H)).val = if WithScott.toScott p ∈ H then 1 else 0 := by
  classical
  by_cases hp : WithScott.toScott p ∈ H <;>
    simp [incidence, unitIndicator, incidenceOpen, incidenceSet, unitOne, unitZero, hp]

def evaluationOpen {P : Type u} [PartialOrder P] (p : P) : ScottOpens (ScottOpens P) := by
  refine ⟨{H | WithScott.toScott p ∈ WithScott.ofScott H}, ?_⟩
  have hc : ScottContinuous (fun H : ScottOpens P => (p, H)) :=
    (ScottContinuous.const p).prodMk ScottContinuous.id
  exact (incidenceOpen P).isOpen.preimage ((scott_continuous_iff _).mp hc)

end CantorFubini
