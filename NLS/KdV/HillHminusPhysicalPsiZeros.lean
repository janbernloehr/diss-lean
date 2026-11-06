import NLS.KdV.HillHminusRealPsiCharts
import NLS.KdV.HillHminusOneMiuraAllLabels
import NLS.KdV.MiuraHillPsiRetainedZeros

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.KdV

/-- Choose the actual numerator chart with its zero-frequency energy below
all real characteristic roots, then retain that nonzero characteristic
throughout the common complex source neighborhood. -/
theorem exists_hillHminusPsiChart_real_form_outside_shift
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q) (M : ℝ) :
    ∃ P : HillHminusPsiChart, ∃ c : ℝ, 0<c ∧ M<c ∧
      P.miura.energyShift=(c : ℂ)^2 ∧ q∈P.source ∧
      (∀ a∈P.miura.domain, IsRealPeriodOneHminusOne a → ∀ k : ℤ,
        P.miura.lift a (-k)=conj (P.miura.lift a k)) ∧
      (∀ a∈P.miura.domain, hillHminusRadicand a (-P.miura.energyShift)≠0) ∧
      SourceLemma12_12Data (by norm_num) (by norm_num)
        P.family.originalDomain P.family.domain P.family.roots := by
  obtain ⟨P,c,hc,hMc,hshift,hqP,hreal,hest⟩ :=
    exists_hillHminusPsiChart_real_form_with_original_estimates q hq
      (max M (|hillHminusLabels q hq 0|+1))
  have hMc' : M<c := (le_max_left _ _).trans_lt hMc
  have hlarge : |hillHminusLabels q hq 0|+1<c := (le_max_right _ _).trans_lt hMc
  have hbelow : -c^2<hillHminusLabels q hq 0 := by
    have hbound := neg_abs_le (hillHminusLabels q hq 0)
    have hnonneg := abs_nonneg (hillHminusLabels q hq 0)
    nlinarith
  have hnonzero : hillHminusRadicand q (-P.miura.energyShift)≠0 := by
    intro hz
    obtain ⟨j,hj⟩ := (hillHminusLabels_roots_iff q hq _).mp hz
    have he : -c^2=hillHminusLabels q hq j := by
      apply Complex.ofReal_injective
      simpa only [hshift,ofReal_neg,ofReal_pow] using hj
    have hm := monotone_hillHminusLabels q hq (Nat.zero_le j)
    linarith
  let U : Set PeriodOneHminusOne := {a | hillHminusRadicand a (-P.miura.energyShift)≠0}
  have hcontinuous : Continuous (fun a => hillHminusRadicand a (-P.miura.energyShift)) := by
    apply continuous_iff_continuousAt.mpr
    intro a
    exact ((analyticOnNhd_hillHminusRadicand_joint (-P.miura.energyShift,a) (mem_univ _)).comp
      (f := fun b : PeriodOneHminusOne => (-P.miura.energyShift,b))
      (analyticAt_const.prod analyticAt_id)).continuousAt
  have hU : IsOpen U := (isClosed_singleton.isOpen_compl).preimage hcontinuous
  let C : HillHminusMiuraChart :=
    ⟨P.miura.domain∩U,P.miura.domain_open.inter hU,P.miura.energyShift,
      P.miura.lift,P.miura.lift_analytic.mono inter_subset_left,
      fun a ha => P.miura.image a ha.1⟩
  let Q : HillHminusPsiChart := ⟨C,P.family⟩
  exact ⟨Q,c,hc,hMc',hshift,⟨⟨hqP.1,hnonzero⟩,hqP.2⟩,
    (fun a ha => hreal a ha.1),(fun a ha => ha.2),hest⟩

/-- Every original physical endpoint slot, including the bottom and all
collapsed low pairs, agrees with the actual squared Dirac enumeration. -/
theorem HillHminusPsiChart.original_labels_eq_squared_miuraDirac
    (P : HillHminusPsiChart) (q : RealPeriodOneHillPotential)
    (hq : hillOriginalHminusSource q.val∈P.source)
    (hreal : ∀ a∈P.miura.domain, IsRealPeriodOneHminusOne a → ∀ k : ℤ,
      P.miura.lift a (-k)=conj (P.miura.lift a k))
    (houtside : hillHminusRadicand (hillOriginalHminusSource q.val) (-P.miura.energyShift)≠0)
    (c : ℝ) (hshift : P.miura.energyShift=(c : ℂ)^2) :
    hillRealLabels q.val q.property.1 q.property.2=
      hillMiuraSquaredLabels (P.miura.lift (hillOriginalHminusSource q.val)) (c^2) := by
  let u : PeriodOneRealL2 := ⟨P.miura.lift (hillOriginalHminusSource q.val),
    hreal _ hq.1 (hillOriginalHminusSource_real q.val q.property.2)⟩
  have hi : periodOneMiura u.val=hillOriginalHminusSource q.val+
      periodOneL2Inclusion (lp.single 2 0 ((c^2 : ℝ) : ℂ)) := by
    have h := P.miura.image _ hq.1
    rw [hshift] at h
    simpa only [ofReal_pow] using h
  have ho : hillHminusRadicand (hillOriginalHminusSource q.val) (-((c^2 : ℝ) : ℂ))≠0 := by
    simpa only [hshift,ofReal_pow] using houtside
  have h := hillHminusLabels_eq_squared_miuraDirac (hillOriginalHminusSource q.val)
    (hillOriginalHminusSource_real q.val q.property.2) u (c^2) hi ho
  simpa only [hillHminusLabels_original_source q] using h

/-- The actual analytic energy numerator has a zero in EVERY retained
ORIGINAL physical gap, with the same positive indices, also at collapse. -/
theorem HillHminusPsiChart.exists_original_retained_gap_zero
    (P : HillHminusPsiChart) (q : RealPeriodOneHillPotential)
    (hq : hillOriginalHminusSource q.val∈P.source)
    (hreal : ∀ a∈P.miura.domain, IsRealPeriodOneHminusOne a → ∀ k : ℤ,
      P.miura.lift a (-k)=conj (P.miura.lift a k))
    (houtside : hillHminusRadicand (hillOriginalHminusSource q.val) (-P.miura.energyShift)≠0)
    (c : ℝ) (hshift : P.miura.energyShift=(c : ℂ)^2)
    (n m : ℕ+) (hmn : m≠n) :
    ∃ E : ℝ, E∈Icc (hillRealLabels q.val q.property.1 q.property.2 (2*(m:ℕ)-1))
      (hillRealLabels q.val q.property.1 q.property.2 (2*(m:ℕ))) ∧
      P.numerator n ((E:ℂ),hillOriginalHminusSource q.val)=0 := by
  let u : PeriodOneRealL2 := ⟨P.miura.lift (hillOriginalHminusSource q.val),
    hreal _ hq.1 (hillOriginalHminusSource_real q.val q.property.2)⟩
  obtain ⟨x,hx,hzero⟩ := P.family.exists_retained_energy_zero u n m hmn
  have he := P.original_labels_eq_squared_miuraDirac q hq hreal houtside c hshift
  have hleft : hillRealLabels q.val q.property.1 q.property.2 (2*(m:ℕ)-1)=
      (hillMiuraDiracLeft u.val ((m:ℕ):ℤ)).re^2-c^2 := by
    simpa only [hillMiuraSquaredLabels,hillMiuraPositiveFrequencies_left _ _ m.pos] using congrFun he (2*(m:ℕ)-1)
  have hright : hillRealLabels q.val q.property.1 q.property.2 (2*(m:ℕ))=
      (hillMiuraDiracRight u.val ((m:ℕ):ℤ)).re^2-c^2 := by
    simpa only [hillMiuraSquaredLabels,hillMiuraPositiveFrequencies_right _ _ m.pos] using congrFun he (2*(m:ℕ))
  have hpos := hillMiura_positive_gap_left_pos u ((m:ℕ):ℤ) (by exact_mod_cast m.pos)
  change 0<(hillMiuraDiracLeft u.val ((m:ℕ):ℤ)).re at hpos
  refine ⟨x^2-c^2,?_,?_⟩
  · rw [hleft,hright]
    constructor <;> nlinarith [hx.1,hx.2]
  · change P.family.numerator n (((x^2-c^2 : ℝ):ℂ)+P.miura.energyShift,u.val)=0
    have henergy : (((x^2-c^2 : ℝ):ℂ)+P.miura.energyShift)=(x:ℂ)^2 := by
      rw [hshift,ofReal_sub,ofReal_pow,ofReal_pow,sub_add_cancel]
    rw [henergy]
    exact hzero

end NLS.KdV
