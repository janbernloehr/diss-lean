import NLS.ZakharovShabat.L2WholeLineReality

/-! # The zero physical potential on the original whole line -/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory
namespace NLS.ZakharovShabat

theorem ae_intervalL2Representative_zero :
    intervalL2Representative (0 : IntervalPairL2) =ᵐ[volume.restrict (Ioc 0 1)] (fun _ => 0) := by
  filter_upwards [Lp.coeFn_zero ℂ 2 (volume.restrict (Ioc (0 : ℝ) 1))] with t ht
  change ((0 : IntervalL2) t,(0 : IntervalL2) t) = (0,0)
  rw [ht]
  rfl

theorem isClassicalRealType_intervalL2_zero :
    IsClassicalRealType (intervalL2Representative (0 : IntervalPairL2)) := by
  filter_upwards [ae_intervalL2Representative_zero] with t ht
  rw [ht]
  simp

theorem ae_l2WholeLinePotential_zero :
    l2WholeLinePotential (0 : IntervalPairL2) =ᵐ[volume] (fun _ => 0) :=
  ae_l2WholeLinePotential_property 0 (fun v => v = 0) ae_intervalL2Representative_zero

end NLS.ZakharovShabat
