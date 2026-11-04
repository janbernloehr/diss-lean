import NLS.SequenceSpaces.TwoPoleReciprocalEnvelope
import NLS.SequenceSpaces.ShiftedHolderDecay

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal Classical

namespace NLS.Coeff



/-- Absolute summability for reciprocal factors centered at zero and n. -/
def separatedReciprocalEnvelope (n : ℤ) : Coeff 1 :=
  WeightedCoeff.holderProduct (puncturedLattice 2 (by norm_num))
    (shift n (puncturedLattice 2 (by norm_num)))

@[simp] theorem separatedReciprocalEnvelope_apply (n k : ℤ) :
    separatedReciprocalEnvelope n k=(k : ℂ)⁻¹*((k-n : ℤ) : ℂ)⁻¹ := by
  have h (m : ℤ) : puncturedLattice 2 (by norm_num) m=(m : ℂ)⁻¹ := by
    by_cases hm : m=0 <;> simp [puncturedLattice_apply,hm]
  change puncturedLattice 2 (by norm_num) k*puncturedLattice 2 (by norm_num) (k-n)=_
  rw [h,h]

theorem norm_separatedReciprocalEnvelope_le (n : ℤ) : ‖separatedReciprocalEnvelope n‖≤4 := by
  calc
    _ ≤ ‖WeightedCoeff.holderProduct (p := 2) (q := 2)‖ *
        ‖puncturedLattice 2 (by norm_num)‖ * ‖shift n (puncturedLattice 2 (by norm_num))‖ :=
      (WeightedCoeff.holderProduct (p := 2) (q := 2)).le_opNorm₂ _ _
    _ ≤ 1*2*2 := by
      apply mul_le_mul
      · exact mul_le_mul WeightedCoeff.norm_holderProduct_le norm_puncturedLattice_two_le
          (norm_nonneg _) (by norm_num)
      · simpa only [norm_shift] using norm_puncturedLattice_two_le
      · exact norm_nonneg _
      · norm_num
    _ = _ := by norm_num

theorem norm_separatedReciprocalEnvelope_eq_pairing (n : ℤ) :
    ‖separatedReciprocalEnvelope n‖=∑' m : ℤ,
      ‖puncturedLattice 2 (by norm_num) m‖*‖shift n (puncturedLattice 2 (by norm_num)) m‖ := by
  rw [show ‖separatedReciprocalEnvelope n‖=∑' m : ℤ, ‖separatedReciprocalEnvelope n m‖ from by
    simpa only [ENNReal.toReal_one,Real.rpow_one] using
      (lp.hasSum_norm (p := 1) (by simp) (separatedReciprocalEnvelope n)).tsum_eq.symm]
  apply tsum_congr
  intro m
  exact norm_mul _ _

/-- The complete l1 norm vanishes when the two centers separate. -/
theorem tendsto_norm_separatedReciprocalEnvelope_zero :
    Tendsto (fun n : ℤ => ‖separatedReciprocalEnvelope n‖) cofinite (𝓝 0) := by
  simpa only [norm_separatedReciprocalEnvelope_eq_pairing] using
    tendsto_tsum_norm_mul_shift_zero (p := 2) (q := 2) (by simp) (by simp)
      (show (2 : ℝ≥0∞).toReal.HolderConjugate (2 : ℝ≥0∞).toReal from Real.HolderConjugate.two_two)
      (puncturedLattice 2 (by norm_num)) (puncturedLattice 2 (by norm_num))

end NLS.Coeff
