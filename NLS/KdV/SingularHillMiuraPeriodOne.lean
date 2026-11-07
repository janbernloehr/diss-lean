import NLS.KdV.SingularHillMiuraDirac
import NLS.KdV.PeriodOneHminusOneOriginal
import NLS.KdV.HminusOneMiuraTrace
import NLS.SequenceSpaces.PeriodDoublingYoung

/-! Exact unit-period to native period-two Miura realization, with no
coefficient, frequency or original-distribution normalization left implicit. -/
noncomputable section
open Complex
open scoped ENNReal ComplexConjugate
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.SmoothPeriodicTest NLS.Fourier.PeriodicFourierLebesgue
open NLS.ZakharovShabat

theorem singularHillMiuraPotential_periodDouble (u : Coeff 2) :
    singularHillMiuraPotential (Coeff.periodDouble u) = periodOneOriginal (periodOneMiura u) := by
  apply Subtype.ext
  apply Distribution.ext_coefficients
  intro n
  by_cases hn : n % 2 = 0
  · have he : n = 2*(n/2) := by omega
    have hp := congrArg (fun a : Coeff ⊤ => a (2*(n/2)))
      (Coeff.periodDouble_youngConvolution youngRelation_two_two_top u u)
    have hs : (∑' j : ℤ, Coeff.periodDouble u (2*(n/2)-j)*Coeff.periodDouble u j) =
        ∑' j : ℤ, u (n/2-j)*u j := by
      simpa only [Coeff.periodDouble_even,Coeff.youngConvolution_apply] using hp.symm
    rw [he,singularHillMiuraPotential_coefficient,periodOneOriginal_even,
      periodOneMiura_apply,Coeff.periodDouble_even,hs]
    push_cast
    ring
  · have he : n = 2*(n/2)+1 := by omega
    have hp := congrArg (fun a : Coeff ⊤ => a (2*(n/2)+1))
      (Coeff.periodDouble_youngConvolution youngRelation_two_two_top u u)
    have hs : (∑' j : ℤ, Coeff.periodDouble u (2*(n/2)+1-j)*Coeff.periodDouble u j) = 0 := by
      simpa only [Coeff.periodDouble_odd,Coeff.youngConvolution_apply] using hp.symm
    rw [he,singularHillMiuraPotential_coefficient,periodOneOriginal_odd,
      Coeff.periodDouble_odd,hs,mul_zero,zero_add]

theorem periodDouble_realType_diagonal (u : PeriodOneRealL2) :
    IsRealType (Coeff.periodDouble u.val,Coeff.periodDouble u.val) := by
  intro n
  change Coeff.periodDouble u.val n = conj (Coeff.periodDouble u.val (-n))
  by_cases hn : n % 2 = 0
  · have he : n = 2*(n/2) := by omega
    rw [he,show -(2*(n/2)) = 2*(-(n/2)) by ring,
      Coeff.periodDouble_even,Coeff.periodDouble_even]
    simpa only [neg_neg] using u.property (-(n/2))
  · have he : n = 2*(n/2)+1 := by omega
    rw [he,show -(2*(n/2)+1) = 2*(-(n/2)-1)+1 by ring,
      Coeff.periodDouble_odd,Coeff.periodDouble_odd,map_zero]

theorem periodOneOriginal_L2_native (a : Coeff 2) :
    periodOneOriginal (periodOneL2Inclusion a) = l2OriginalHminus (Coeff.periodDouble a) := by
  rw [periodOneOriginal_L2]
  apply Subtype.ext
  apply Distribution.ext_coefficients
  intro n
  rw [hillL2HminusOne_coefficient,periodOneL2OriginalCoefficients_apply,l2OriginalHminus_coefficient]

theorem periodOneOriginal_add_constant (q : PeriodOneHminusOne) (c : ℂ) :
    periodOneOriginal (q+periodOneL2Inclusion (lp.single 2 0 c)) =
      periodOneOriginal q+l2OriginalHminus (lp.single 2 0 c) := by
  rw [map_add,periodOneOriginal_L2_native,periodDouble_single_zero]

end NLS.KdV
