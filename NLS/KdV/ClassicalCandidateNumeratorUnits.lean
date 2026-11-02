import NLS.KdV.ClassicalNormalizedZeros
import NLS.KdV.ClassicalSignedCriticalProduct

/-! # Nonvanishing filled critical basis factors on candidate discs

Complete signed critical labeling excludes other critical roots throughout
the candidate disc. At the filled own critical energy the actual second
derivative supplies the nonzero value.
-/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV
namespace ClassicalAllContourPeriodData
variable {N : ℕ} {V : Set (NLS.LinearVolterra.Curve ℂ)} {A : ℝ}
variable (D : ClassicalAllContourPeriodData N V A)
include D

theorem candidate_discriminant_derivative_zero_iff (k : ℕ+)
    (t : NLS.Coeff 2 × NLS.LinearVolterra.Curve ℂ) (ht : t ∈ classicalHillCandidateDomain V) :
    deriv (classicalHillDiscriminant t.2) (classicalHillCandidateEnergy N k t) = 0 ↔
      classicalHillCandidateEnergy N k t = classicalHillUniformCriticalPoint N k t.2 := by
  constructor
  · intro hz
    obtain ⟨M,hlabel⟩ := (D.signedCritical_product t.2 ht.2).1
    have hfreq : deriv (canonicalDiscriminant (by simp) (classicalHillCoefficientPotential t.2))
        (classicalHillCandidateFrequency N k t) = 0 := by
      rw [classicalHill_frequency_derivative_eq]
      change (2*classicalHillCandidateFrequency N k t)*
        deriv (classicalHillDiscriminant t.2) (classicalHillCandidateEnergy N k t) = 0
      rw [hz,mul_zero]
    obtain ⟨j,hj⟩ := (hlabel.exhaustive _).mp hfreq
    have hjk : j = (k : ℤ) := by
      by_contra hne
      have hgap : (1 : ℝ) ≤ |((j-(k : ℤ) : ℤ) : ℝ)| := by
        exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hne)
      have h1 : ‖(Real.pi : ℂ)*j-classicalHillCandidateFrequency N k t‖ < Real.pi/8 := by
        rw [← hj,norm_sub_rev]
        exact D.signedCritical_close t.2 ht.2 j
      have h2 := mem_closedBall_iff_norm.mp (D.candidate_frequency_mem_disc k t ht)
      have hb := norm_sub_le_norm_sub_add_norm_sub ((Real.pi : ℂ)*j)
        (classicalHillCandidateFrequency N k t) ((Real.pi : ℂ)*(k : ℤ))
      rw [norm_free_center_sub] at hb
      simp only [Int.cast_natCast] at hb
      nlinarith [Real.pi_pos,mul_le_mul_of_nonneg_left hgap Real.pi_pos.le]
    rw [hjk,classicalHillSignedCritical_positive] at hj
    change (classicalHillCandidateFrequency N k t)^2 = _
    rw [← hj,sq_sqrt]
  · intro he
    rw [he]
    exact D.critical_zero k t.2 ht.2

theorem numerator_at_critical_ne_zero (k : ℕ+) (q : NLS.LinearVolterra.Curve ℂ) (hq : q ∈ V) :
    classicalHillUniformNumerator N k (classicalHillUniformCriticalPoint N k q,q) ≠ 0 := by
  have hF := analyticOnNhd_classicalHillDiscriminantDerivative.mono
    (subset_univ (univ ×ˢ V))
  dsimp only [classicalHillUniformNumerator]
  rw [parametricMovingDividedDifference_center _ _ hF q hq]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
    (by exact_mod_cast k.ne_zero)) (by exact_mod_cast Real.pi_ne_zero)) (D.critical_simple k q hq)

theorem candidate_numerator_ne_zero (k : ℕ+)
    (t : NLS.Coeff 2 × NLS.LinearVolterra.Curve ℂ) (ht : t ∈ classicalHillCandidateDomain V) :
    classicalHillUniformNumerator N k (classicalHillCandidateEnergy N k t,t.2) ≠ 0 := by
  intro hz
  have hf := D.numerator_factor k t.2 ht.2 (classicalHillCandidateEnergy N k t)
  rw [hz,mul_zero] at hf
  have hc : (2*(k : ℂ)*Real.pi) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast k.ne_zero)) (by exact_mod_cast Real.pi_ne_zero)
  have hd := (mul_eq_zero.mp hf.symm).resolve_left hc
  have he := (D.candidate_discriminant_derivative_zero_iff k t ht).mp hd
  rw [he] at hz
  exact D.numerator_at_critical_ne_zero k t.2 ht.2 hz

end ClassicalAllContourPeriodData
end NLS.KdV
