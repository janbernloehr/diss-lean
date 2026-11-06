import NLS.KdV.MiuraCanonicalEndpoints
import NLS.KdV.HillMiuraTraceOrder

/-! # Real and ordered endpoints of the actual Miura Dirac source -/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.ZakharovShabat
namespace NLS.KdV

theorem hillMiuraDiracPair_real (u : PeriodOneRealL2) (n : ℤ) :
    (hillMiuraDiracLeft u.val n).im = 0 ∧ (hillMiuraDiracRight u.val n).im = 0 := by
  apply canonicalPeriodicEndpoints_im_eq_zero_of_realType (by norm_num) (by norm_num)
  exact isRealType_periodOnePotential _ (isRealType_hillMiuraDiagonal u)

theorem hillMiuraDiracPair_ordered (u : Coeff 2) (n : ℤ) :
    (hillMiuraDiracLeft u n).re ≤ (hillMiuraDiracRight u n).re :=
  NLS.ComplexAnalysis.re_le_of_complexLexLE
    ((canonicalPeriodicEndpoints_spec (by norm_num) (by norm_num)
      (periodOnePotential (hillMiuraDiagonal u)) (periodOnePotential_mem _)).2.1 n)

end NLS.KdV
