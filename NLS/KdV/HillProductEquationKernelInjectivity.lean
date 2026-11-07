import NLS.KdV.HillProductEquationDataDirection
import NLS.KdV.HillProductVariationGrowth
import NLS.KdV.HillRetainedPeriodUniqueness

/-! Full kernel injectivity of the actual real Hill period Jacobian.
Normalize the entire data variation by its omitted period; the proved
all-period uniqueness forces a scalar multiple of the original product.
Filled root evaluation then recovers every component of the direction. -/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch

theorem sequenceJacobian_actual_real_kernel_eq_zero (P : HillProductEquationPatch) (n : ℕ+)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q)
    (h : lp (fun _ : ℕ+ => ℂ) 2)
    (hk : P.sequenceJacobian n (hillHminusPsiZeroDisplacement n ⟨q,hr⟩,q) h = 0) : h = 0 := by
  let B := P.parent.parent.miuraBall.actionBall
  have hb := (P.parent.subset (P.subset hq)).1
  let u : PeriodOneRealL2 := ⟨B.lift q,B.lift_real q hb hr⟩
  let c : ℂ := B.shift
  let d := hillHminusPsiZeroDisplacement n ⟨q,hr⟩
  let F := hillEnergyProductDataVariation n d h
  let G : ℂ → ℂ := fun E => hillEnergySequenceProduct n (E,d)
  let D := fun m : ℕ+ => P.isolating.periodCircle (P.sourcePsi q) (P.image q hq).2 ((m:ℕ):ℤ)
    (P.centers ((m:ℕ):ℤ)) (P.radii ((m:ℕ):ℤ)) (P.radii_pos ((m:ℕ):ℤ)) (P.discs_eq ((m:ℕ):ℤ))
  have hn : h n = 0 := P.sequenceJacobian_kernel_omitted_zero n q hq hr h hk
  have hd : (c,d) ∈ LpSequence.quadraticFrequencyDomain Real.pi :=
    P.parent.actual_zero_data_mem_frequencyDomain n q (P.subset hq) hr
  have hβ : hillIndependentFrequency (c,d) ((n:ℕ):ℤ) ≠ 0 := by
    intro hz
    apply Complex.slitPlane_ne_zero (hd n)
    change hillEnergySequenceZero n d+c = 0
    rw [← hillIndependentFrequency_positive_sq (c,d) n,hz,zero_pow (by decide)]
  have hF : AnalyticOnNhd ℂ F univ := analyticOnNhd_hillEnergyProductDataVariation n d h
  have hG : AnalyticOnNhd ℂ G univ := by
    intro E _
    exact (analyticAt_hillEnergySequenceProduct n (E,d)).comp (f := fun w : ℂ => (w,d))
      (analyticAt_id.prod analyticAt_const)
  have hFp (m : ℕ+) (hmn : m ≠ n) : hillEnergyNumeratorPeriod c (hillMiuraDiagonal u.val) (D m) F = 0 :=
    P.sequenceJacobian_kernel_retained_period_zero n m hmn q hq hr h hk (D m) rfl rfl
  have hGp (m : ℕ+) (hmn : m ≠ n) : hillEnergyNumeratorPeriod c (hillMiuraDiagonal u.val) (D m) G = 0 :=
    P.parent.product_off_diagonal_period_zero n m hmn q (P.subset hq) hr (D m)
  have hGn : hillEnergyNumeratorPeriod c (hillMiuraDiagonal u.val) (D n) G ≠ 0 := by
    intro hz
    have hp := P.parent.product_period_scalar n n q (P.subset hq) hr (D n)
    change hillEnergyProductFixedPeriod n c (hillMiuraDiagonal u.val) (D n) d = 0 at hz
    rw [if_pos rfl,hz,mul_zero] at hp
    exact zero_ne_one hp
  obtain ⟨A,hA⟩ := hillEnergyNumerator_eq_scalar_of_retained_periods u c n D F G hF hG hFp hGp hGn
    (hillEnergyProductDataVariation_pullback_sub_sine n c d h hd hβ hn)
    (hillEnergySequenceProduct_pullback_sub_sine n c d)
  ext m
  by_cases hmn : m = n
  · subst m
    exact hn
  · have hz : F (hillEnergySequenceZero m d) = 0 := by
      rw [hA]
      change A*hillEnergySequenceProduct n (hillEnergySequenceZero m d,d) = 0
      rw [hillEnergySequenceProduct_retained_root n m hmn d,mul_zero]
    have he := hillEnergyProductDataVariation_at_retained_root n m hmn d h
    change F (hillEnergySequenceZero m d) = _ at he
    rw [hz] at he
    exact (mul_eq_zero.mp he.symm).resolve_left
      (hillEnergyProductCoordinateDerivative_real_diagonal_ne_zero n m hmn ⟨q,hr⟩)

theorem sequenceJacobian_actual_real_injective (P : HillProductEquationPatch) (n : ℕ+)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q) :
    Function.Injective (P.sequenceJacobian n (hillHminusPsiZeroDisplacement n ⟨q,hr⟩,q)) := by
  intro a b hab
  have hk : P.sequenceJacobian n (hillHminusPsiZeroDisplacement n ⟨q,hr⟩,q) (a-b) = 0 := by
    rw [map_sub,hab,sub_self]
  exact sub_eq_zero.mp (P.sequenceJacobian_actual_real_kernel_eq_zero n q hq hr (a-b) hk)

end NLS.KdV.HillProductEquationPatch
