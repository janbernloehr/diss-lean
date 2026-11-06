import NLS.KdV.NativeHillPhysicalSource
import NLS.Fourier.PeriodOneFourierUniqueness
import NLS.Fourier.ContinuousSynthesisReality

/-! # Canonical continuous physical source of original native H^m potentials -/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.Fourier NLS.ZakharovShabat
open scoped ComplexConjugate ENNReal
namespace NLS.KdV

/-- The original H1 representative, with no change of unit-period coefficients. -/
def nativeHillContinuousSource (m : ℕ) (hm : 1≤m) (q : ScalarSobolev m) :
    C(AddCircle (2 : ℝ),ℂ) :=
  periodOneSobolevSynthesis (hierarchySobolevToScalarDomain m hm q)

theorem nativeHillContinuousSource_periodic (m : ℕ) (hm : 1≤m) (q : ScalarSobolev m) :
    Function.Periodic (fun x : ℝ => nativeHillContinuousSource m hm q (x : AddCircle (2 : ℝ))) 1 :=
  periodOneSobolevSynthesis_periodic _

theorem nativeHillContinuousSource_coefficient (m : ℕ) (hm : 1≤m) (q : ScalarSobolev m) (n : ℤ) :
    periodOneCoefficient (fun x : ℝ => nativeHillContinuousSource m hm q (x : AddCircle (2 : ℝ))) n = q.val n := by
  rw [nativeHillContinuousSource,periodOneCoefficient_periodOneSobolevSynthesis,hierarchySobolevToScalarDomain_apply]

/-- Equality with ANY actual continuous periodic physical realization. -/
theorem nativeHillContinuousSource_eq_of_coefficients (m : ℕ) (hm : 1≤m) (q : ScalarSobolev m)
    (f : ℝ → ℂ) (hf : Continuous f) (hp : Function.Periodic f 1)
    (hc : ∀ n : ℤ, q.val n=periodOneCoefficient f n) :
    (fun x : ℝ => nativeHillContinuousSource m hm q (x : AddCircle (2 : ℝ))) = f := by
  apply periodOneSobolevSynthesis_eq_of_coefficients _ f hf hp
  intro n
  rw [hierarchySobolevToScalarDomain_apply,hc]

/-- The canonical continuous input is the SAME original physical Hill source. -/
theorem hillContinuousCoefficients_nativeHillContinuousSource (m : ℕ) (hm : 1≤m) (q : ScalarSobolev m)
    (hr : ∀ n : ℤ, q.val (-n)=conj (q.val n)) :
    hillContinuousCoefficients (nativeHillContinuousSource m hm q) = (nativeHillPhysicalSource m q hr).val := by
  have he := periodTwoCoefficient_eq_periodDouble
    (fun x : ℝ => nativeHillContinuousSource m hm q (x : AddCircle (2 : ℝ)))
    (nativeHillContinuousSource_periodic m hm q)
    ((continuous_periodOneSobolevSynthesis _).intervalIntegrable 0 1)
    (WeightedCoeff.sobolevToL2 (Nat.cast_nonneg m) q) (by
      intro n
      rw [nativeHillContinuousSource_coefficient,WeightedCoeff.sobolevToL2_apply])
  apply Subtype.ext
  funext n
  have hn := congrFun he n
  rw [periodTwoCoefficient_circle] at hn
  rw [hillContinuousCoefficients_apply]
  rw [←SpectralWeight.toCoeff_apply,nativeHillPhysicalSource_toCoeff]
  exact hn

/-- A real native source has an everywhere real continuous representative. -/
theorem nativeHillContinuousSource_real (m : ℕ) (hm : 1≤m) (q : ScalarSobolev m)
    (hr : ∀ n : ℤ, q.val (-n)=conj (q.val n)) (x : AddCircle (2 : ℝ)) :
    (nativeHillContinuousSource m hm q x).im=0 := by
  obtain ⟨y,rfl⟩ := QuotientAddGroup.mk_surjective x
  let a : Coeff 1 := WeightedCoeff.sobolevToL1CLM 2 (by simp) (hierarchySobolevToScalarDomain m hm q)
  have ha (n : ℤ) : a n=q.val n := by
    simp only [a,WeightedCoeff.sobolevToL1CLM_apply,hierarchySobolevToScalarDomain_apply]
  change (continuousSynthesis (Coeff.periodDouble a) (y : AddCircle (2 : ℝ))).im=0
  apply continuousSynthesis_im_eq_zero_of_reflection
  intro n
  by_cases hn : n%2=0
  · have he : n=2*(n/2) := by omega
    rw [he,show -(2*(n/2))=2*(-(n/2)) by ring,Coeff.periodDouble_even,Coeff.periodDouble_even,ha,ha,hr]
  · have he : n=2*(n/2)+1 := by omega
    rw [he,show -(2*(n/2)+1)=2*(-(n/2)-1)+1 by ring,Coeff.periodDouble_odd,Coeff.periodDouble_odd,map_zero]

end NLS.KdV
