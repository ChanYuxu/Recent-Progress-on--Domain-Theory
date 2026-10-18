import ChainApproximation.Matrix
import ChainApproximation.LongChains

/-!
# Cofinality obstruction to interpolation

Source `prop:obstruction`. This module handles the countable-limit matrix
argument and the cofinality of the left endpoint without replacing either
argument by an assumption in the main theorem.
-/

set_option autoImplicit false

universe u

namespace ChainApproximation

open Set Cardinal

variable {P : Type u} [PartialOrder P]

theorem noninterpolating_not_compact {x y : P} (hxy : ChainBelow x y)
    (hn : ¬ RelComp ChainBelow ChainBelow x y) :
    ¬ ChainBelow x x ∧ ¬ ChainBelow y y :=
  ⟨fun hx ↦ hn ⟨x, hx, hxy⟩, fun hy ↦ hn ⟨y, hxy, hy⟩⟩

theorem noninterpolating_intermediate_kappa (hP : IsChainContinuous P)
    {x y z : P} (hn : ¬ RelComp ChainBelow ChainBelow x y)
    (hxz : x ≤ z) (hzy : ChainBelow z y) : kappa z = kappa x := by
  by_contra hne
  exact hn ⟨z, chainBelow_of_le_kappa_ne hP hxz (Ne.symm hne), hzy⟩

/-- The countable-limit case of the source obstruction proof. Each row is
approximated at the same cofinality as `x`; the two cases are handled by a
countable cofinal union or by the transfinite matrix, respectively. -/
theorem interpolates_of_nat_approximation (hdcpo : IsDcpo P) (hP : IsChainContinuous P)
    {x y : P} (hxy : ChainBelow x y) (f : ℕ → P) (hf : Monotone f)
    (hxf : ∀ n, x ≤ f n) (hfy : ∀ n, ChainBelow (f n) y)
    (hfLub : IsLUB (Set.range f) y) : RelComp ChainBelow ChainBelow x y := by
  classical
  by_contra hn
  have hxx : ¬ ChainBelow x x := (noninterpolating_not_compact hxy hn).1
  have hκ : Cardinal.aleph0 ≤ kappa x := kappa_aleph0_le hP hxx
  have hκf : ∀ n, kappa (f n) = kappa x :=
    fun n ↦ noninterpolating_intermediate_kappa hP hn (hxf n) (hfy n)
  by_cases hcount : kappa x = Cardinal.aleph0
  · have hex : ∀ n, ∃ b : ℕ → P, Monotone b ∧
        (∀ m, ChainBelow (b m) (f n)) ∧
        (∀ a, ChainBelow a (f n) → ∃ m, a ≤ b m) ∧ IsLUB (Set.range b) (f n) :=
      fun n ↦ hP.nat_section ((hκf n).trans hcount)
    choose b hbmono hbmem hbcof hblub using hex
    let D : Set P := {a | ∃ n, ChainBelow a (f n)}
    have hD : NonemptyDirected D := by
      refine ⟨⟨b 0 0, 0, hbmem 0 0⟩, ?_⟩
      rintro a ⟨n, han⟩ c ⟨m, hcm⟩
      have ha : ChainBelow a (f (max n m)) := han.mono le_rfl (hf (le_max_left _ _))
      have hc : ChainBelow c (f (max n m)) := hcm.mono le_rfl (hf (le_max_right _ _))
      obtain ⟨d, hd, had, hcd⟩ := (hP.section_directed (f (max n m))).2 a ha c hc
      exact ⟨d, ⟨max n m, hd⟩, had, hcd⟩
    let A : Set P := Set.range (fun nm : ℕ × ℕ ↦ b nm.1 nm.2)
    have hAD : A ⊆ D := by
      rintro _ ⟨⟨n, m⟩, rfl⟩
      exact ⟨n, hbmem n m⟩
    have hAcof : ∀ d ∈ D, ∃ a ∈ A, d ≤ a := by
      rintro d ⟨n, hdn⟩
      obtain ⟨m, hdm⟩ := hbcof n d hdn
      exact ⟨b n m, Set.mem_range_self (n, m), hdm⟩
    have hDLub : IsLUB D y := by
      refine ⟨?_, ?_⟩
      · rintro a ⟨n, han⟩
        exact han.le.trans (hfy n).le
      · intro q hq
        apply hfLub.2
        rintro _ ⟨n, rfl⟩
        exact (hP.section_lub (f n)).2 (fun a ha ↦ hq ⟨n, ha⟩)
    obtain ⟨c, hcmono, hcmem, hccof⟩ := countable_cofinal_chain hD
      (Set.countable_range _) hAD hAcof
    have hcLub : IsLUB (Set.range c) y := by
      refine ⟨?_, ?_⟩
      · rintro _ ⟨n, rfl⟩
        exact hDLub.1 (hcmem n)
      · intro q hq
        apply hDLub.2
        intro d hd
        obtain ⟨n, hdn⟩ := hccof d hd
        exact hdn.trans (hq (Set.mem_range_self _))
    obtain ⟨_, ⟨n, rfl⟩, hxcn⟩ := (chainBelow_iff_sup hdcpo x y).mp hxy
      (Set.range c) ⟨Set.range_nonempty _, hcmono.isChain_range⟩ y hcLub le_rfl
    obtain ⟨m, hcnm⟩ := hcmem n
    exact hn ⟨f m, hcnm.mono hxcn le_rfl, hfy m⟩
  · have hlarge : Cardinal.aleph0 < kappa x := lt_of_le_of_ne hκ (Ne.symm hcount)
    let I : ℕ → Set P := fun n ↦ chainSection (f n)
    have hI : ∀ n, HasCofinalChain (I n) := fun n ↦ hP.section_hasCofinalChain (f n)
    have hnest : ∀ n, I n ⊆ I (n + 1) := fun n ↦ chainSection_mono (hf (Nat.le_succ n))
    have hcard : ∀ n, Order.cof (I n) = kappa x := hκf
    have hex : ∀ n, ∃ b : CofinalIndex (kappa x) → I n,
        IsCofinal (Set.range b) := by
      intro n
      have h := (hI n).enumerate
      rwa [hcard n] at h
    choose b hbcof using hex
    obtain ⟨e, hemem, hbe, hecol, herow⟩ :=
      exists_monotone_matrix I hI hnest (kappa x) hκ hcard b
    have havoid : ∀ n a, ¬ x ≤ e n a := by
      intro n a hx
      exact hn ⟨f n, (hemem n a).mono hx le_rfl, hfy n⟩
    have hcolumns : ∀ a, ∃ d, IsLUB (Set.range (fun n ↦ e n a)) d :=
      fun a ↦ hdcpo _ ⟨Set.range_nonempty _, (hecol a).isChain_range.directedOn⟩
    choose d hd using hcolumns
    have hdavoid : ∀ a, ¬ x ≤ d a := by
      intro a hxa
      have hcof : Order.cof (Set.range (fun n ↦ e n a)) ≤ Cardinal.aleph0 := by
        apply (Order.cof_le_cardinalMk _).trans
        haveI : Countable (Set.range (fun n ↦ e n a)) := (Set.countable_range _).to_subtype
        exact Cardinal.mk_le_aleph0_iff.mpr inferInstance
      have hne : kappa x ≠ Order.cof (Set.range (fun n ↦ e n a)) :=
        ne_of_gt (hcof.trans_lt hlarge)
      obtain ⟨_, ⟨n, rfl⟩, hxn⟩ := exists_ge_of_le_lub_kappa_ne hP
        ⟨Set.range_nonempty _, (hecol a).isChain_range⟩ (hd a) hxa hne
      exact havoid n a hxn
    have hdmono : Monotone d := by
      intro a c hac
      apply (hd a).2
      rintro _ ⟨n, rfl⟩
      exact (herow n hac).trans ((hd c).1 (Set.mem_range_self _))
    haveI : Nonempty (CofinalIndex (kappa x)) :=
      Cardinal.mk_ne_zero_iff.mp (by
        rw [cofinalIndex_card]
        exact ne_of_gt (Cardinal.aleph0_pos.trans hlarge))
    have hdLub : IsLUB (Set.range d) y := by
      refine ⟨?_, ?_⟩
      · rintro _ ⟨a, rfl⟩
        apply (hd a).2
        rintro _ ⟨n, rfl⟩
        exact (hemem n a).le.trans (hfy n).le
      · intro q hq
        apply hfLub.2
        rintro _ ⟨n, rfl⟩
        apply (hP.section_lub (f n)).2
        intro z hz
        obtain ⟨_, ⟨a, rfl⟩, hza⟩ := hbcof n ⟨z, hz⟩
        exact (show z ≤ (b n a).val from hza).trans (hbe n a) |>.trans
          ((hd a).1 (Set.mem_range_self n)) |>.trans (hq (Set.mem_range_self a))
    obtain ⟨_, ⟨a, rfl⟩, hxa⟩ := (chainBelow_iff_sup hdcpo x y).mp hxy
      (Set.range d) ⟨Set.range_nonempty _, hdmono.isChain_range⟩ y hdLub le_rfl
    exact hdavoid a hxa

theorem noninterpolating_right_ne_aleph0 (hdcpo : IsDcpo P) (hP : IsChainContinuous P)
    {x y : P} (hxy : ChainBelow x y) (hn : ¬ RelComp ChainBelow ChainBelow x y) :
    kappa y ≠ Cardinal.aleph0 := by
  intro hκy
  obtain ⟨f, hf, hfy, _, hLub⟩ := hP.nat_section hκy
  obtain ⟨_, ⟨n₀, rfl⟩, hxn⟩ := (chainBelow_iff_sup hdcpo x y).mp hxy
    (Set.range f) ⟨Set.range_nonempty _, hf.isChain_range⟩ y hLub le_rfl
  let g : ℕ → P := fun n ↦ f (n + n₀)
  have hg : Monotone g := fun a b hab ↦ hf (Nat.add_le_add_right hab _)
  have hglub : IsLUB (Set.range g) y := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨n, rfl⟩
      exact (hfy _).le
    · intro q hq
      apply hLub.2
      rintro _ ⟨n, rfl⟩
      exact (hf (Nat.le_add_right n n₀)).trans (hq (Set.mem_range_self n))
  exact hn (interpolates_of_nat_approximation hdcpo hP hxy g hg
    (fun n ↦ hxn.trans (hf (Nat.le_add_left n₀ n))) (fun n ↦ hfy _) hglub)

theorem strictMono_nat_range_cof {f : ℕ → P} (hf : StrictMono f) :
    Order.cof (Set.range f) = Cardinal.aleph0 := by
  letI : LinearOrder (Set.range f) := chainLinearOrder _ hf.monotone.isChain_range
  haveI : Nonempty (Set.range f) := (Set.range_nonempty f).to_subtype
  haveI : Countable (Set.range f) := (Set.countable_range f).to_subtype
  haveI : NoMaxOrder (Set.range f) := ⟨by
    rintro ⟨_, n, rfl⟩
    exact ⟨⟨f (n + 1), Set.mem_range_self _⟩, hf (Nat.lt_succ_self n)⟩⟩
  exact Order.cof_eq_aleph0

theorem strictMono_nat_lub_not_mem {f : ℕ → P} (hf : StrictMono f)
    {p : P} (hp : IsLUB (Set.range f) p) : p ∉ Set.range f := by
  rintro ⟨n, rfl⟩
  exact not_le_of_gt (hf (Nat.lt_succ_self n)) (hp.1 (Set.mem_range_self (n + 1)))

/-- The left endpoint of any noninterpolating pair has countable cofinality.
This is the part of source `prop:obstruction` needed to rule out two consecutive
failures. The exact right cofinality is proved separately. -/
theorem noninterpolating_left_aleph0 (hdcpo : IsDcpo P) (hP : IsChainContinuous P)
    {x y : P} (hxy : ChainBelow x y) (hn : ¬ RelComp ChainBelow ChainBelow x y) :
    kappa x = Cardinal.aleph0 := by
  classical
  have hyy : ¬ ChainBelow y y := (noninterpolating_not_compact hxy hn).2
  have hκy : Cardinal.aleph0 < kappa y := lt_of_le_of_ne (kappa_aleph0_le hP hyy)
    (Ne.symm (noninterpolating_right_ne_aleph0 hdcpo hP hxy hn))
  let S := chainSection y
  have hS : HasCofinalChain S := hP.section_hasCofinalChain y
  haveI : NoMaxOrder S := ⟨hS.exists_gt (ne_of_gt (Cardinal.one_lt_aleph0.trans hκy))⟩
  obtain ⟨g, hg, hg0⟩ := Nat.exists_strictMono' (⟨x, hxy⟩ : S)
  let f : ℕ → P := fun n ↦ (g n).val
  have hf : StrictMono f := fun i j hij ↦ hg hij
  have hsmall : Cardinal.mk (Set.range g) < Order.cof S := by
    haveI : Countable (Set.range g) := (Set.countable_range g).to_subtype
    exact (Cardinal.mk_le_aleph0_iff.mpr inferInstance).trans_lt hκy
  obtain ⟨b, hb⟩ := hS.small_bounded (Set.range g) hsmall
  obtain ⟨z, hz⟩ := hdcpo (Set.range f) ⟨Set.range_nonempty _, hf.monotone.isChain_range.directedOn⟩
  have hzb : z ≤ b.val := hz.2 (by
    rintro _ ⟨n, rfl⟩
    exact hb (Set.mem_range_self n))
  have hzy : ChainBelow z y := b.property.mono hzb le_rfl
  have hxz : x ≤ z := by
    have hfx : f 0 = x := congrArg Subtype.val hg0
    rw [← hfx]
    exact hz.1 (Set.mem_range_self 0)
  have hκz : kappa z = Cardinal.aleph0 :=
    (kappa_eq_cof_of_not_mem hP ⟨Set.range_nonempty _, hf.monotone.isChain_range⟩ hz
      (strictMono_nat_lub_not_mem hf hz)).trans (strictMono_nat_range_cof hf)
  exact (noninterpolating_intermediate_kappa hP hn hxz hzy).symm.trans hκz

/-- Two failures of interpolation cannot be adjacent. This theorem discharges
the logical premise of the square argument without an additional hypothesis. -/
theorem adjacent_interpolates (hdcpo : IsDcpo P) (hP : IsChainContinuous P)
    {a b c : P} (hab : ChainBelow a b) (hbc : ChainBelow b c) :
    RelComp ChainBelow ChainBelow a b ∨ RelComp ChainBelow ChainBelow b c := by
  by_contra hn
  push Not at hn
  exact noninterpolating_right_ne_aleph0 hdcpo hP hab hn.1
    (noninterpolating_left_aleph0 hdcpo hP hbc hn.2)

/-- The exact right-end cofinality in source `prop:obstruction`. A strictly
increasing aleph-one chain above `x` would have a supremum of cofinality
aleph-one below another approximant of `y`, contradicting the left cofinality. -/
theorem noninterpolating_right_aleph_one (hdcpo : IsDcpo P) (hP : IsChainContinuous P)
    {x y : P} (hxy : ChainBelow x y) (hn : ¬ RelComp ChainBelow ChainBelow x y) :
    kappa y = Cardinal.aleph 1 := by
  classical
  have hκx : kappa x = Cardinal.aleph0 := noninterpolating_left_aleph0 hdcpo hP hxy hn
  have hyy : ¬ ChainBelow y y := (noninterpolating_not_compact hxy hn).2
  have hκy : Cardinal.aleph0 < kappa y := lt_of_le_of_ne (kappa_aleph0_le hP hyy)
    (Ne.symm (noninterpolating_right_ne_aleph0 hdcpo hP hxy hn))
  apply le_antisymm
  · by_contra hnot
    have hlarge : Cardinal.aleph 1 < kappa y := lt_of_not_ge hnot
    let S := chainSection y
    have hS : HasCofinalChain S := hP.section_hasCofinalChain y
    obtain ⟨g, hg, hxg⟩ := hS.strictMono_above_of_lt
      (Cardinal.aleph0_le_aleph 1) hlarge ⟨x, hxy⟩
    let f : CofinalIndex (Cardinal.aleph 1) → P := fun a ↦ (g a).val
    have hf : StrictMono f := fun a b hab ↦ hg hab
    haveI : NoMaxOrder (CofinalIndex (Cardinal.aleph 1)) :=
      Cardinal.noMaxOrder (Cardinal.aleph0_le_aleph 1)
    haveI : Nonempty (CofinalIndex (Cardinal.aleph 1)) :=
      Cardinal.mk_ne_zero_iff.mp (by
        rw [cofinalIndex_card]
        exact Cardinal.isRegular_aleph_one.ne_zero)
    obtain ⟨b, hb⟩ := hS.small_bounded (Set.range g)
      (Cardinal.mk_range_le.trans_lt ((cofinalIndex_card _).trans_lt hlarge))
    obtain ⟨z, hz⟩ := hdcpo (Set.range f)
      ⟨Set.range_nonempty _, hf.monotone.isChain_range.directedOn⟩
    have hzb : z ≤ b.val := hz.2 (by
      rintro _ ⟨a, rfl⟩
      exact hb (Set.mem_range_self a))
    have hzy : ChainBelow z y := b.property.mono hzb le_rfl
    have hxz : x ≤ z := by
      calc
        x ≤ f (Classical.arbitrary _) := hxg _
        _ ≤ z := hz.1 (Set.mem_range_self _)
    have hκz : kappa z = Cardinal.aleph 1 :=
      (kappa_eq_cof_of_not_mem hP ⟨Set.range_nonempty _, hf.monotone.isChain_range⟩ hz
        (strictMono_lub_not_mem hf hz)).trans
          ((cof_range_strictMono hf).trans (regular_cofinalIndex_cof Cardinal.isRegular_aleph_one))
    have hbad : Cardinal.aleph 1 = Cardinal.aleph0 := hκz.symm.trans
      ((noninterpolating_intermediate_kappa hP hn hxz hzy).trans hκx)
    exact Cardinal.aleph0_lt_aleph_one.ne hbad.symm
  · exact Cardinal.aleph_one_le_iff.mpr hκy

/-- Source `prop:obstruction`, all three conclusions. -/
theorem obstruction (hdcpo : IsDcpo P) (hP : IsChainContinuous P)
    {x y : P} (hxy : ChainBelow x y) (hn : ¬ RelComp ChainBelow ChainBelow x y) :
    kappa x = Cardinal.aleph0 ∧ kappa y = Cardinal.aleph 1 ∧
      ∀ z, x ≤ z → ChainBelow z y → kappa z = Cardinal.aleph0 := by
  have hx := noninterpolating_left_aleph0 hdcpo hP hxy hn
  exact ⟨hx, noninterpolating_right_aleph_one hdcpo hP hxy hn,
    fun z hxz hzy ↦ (noninterpolating_intermediate_kappa hP hn hxz hzy).trans hx⟩

end ChainApproximation
