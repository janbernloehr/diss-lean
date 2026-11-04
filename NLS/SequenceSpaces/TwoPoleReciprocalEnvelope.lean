import NLS.SequenceSpaces.PuncturedLattice
import NLS.SequenceSpaces.Embedding

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal Classical

namespace NLS.Coeff



private theorem puncturedLattice_two_apply_eq_inv (k : ℤ) :
    puncturedLattice 2 (by norm_num) k = (k : ℂ)⁻¹ := by
  by_cases hk : k=0 <;> simp [puncturedLattice_apply,hk]

/-- The two shifted reciprocal factors form an absolutely summable envelope. -/
def twoPoleReciprocalEnvelope (n : ℤ) : Coeff 1 :=
  WeightedCoeff.holderProduct (shift n (puncturedLattice 2 (by norm_num))) (shift (-n) (puncturedLattice 2 (by norm_num)))

@[simp] theorem twoPoleReciprocalEnvelope_apply (n k : ℤ) :
    twoPoleReciprocalEnvelope n k = ((k-n : ℤ) : ℂ)⁻¹*((k+n : ℤ) : ℂ)⁻¹ := by
  change (puncturedLattice 2 (by norm_num)) (k-n)*(puncturedLattice 2 (by norm_num)) (k-(-n)) = _
  simp only [sub_neg_eq_add,puncturedLattice_two_apply_eq_inv]

theorem norm_twoPoleReciprocalEnvelope_le (n : ℤ) : ‖twoPoleReciprocalEnvelope n‖ ≤ 4 := by
  calc
    _ ≤ ‖WeightedCoeff.holderProduct (p := 2) (q := 2)‖ *
        ‖shift n (puncturedLattice 2 (by norm_num))‖ * ‖shift (-n) (puncturedLattice 2 (by norm_num))‖ :=
      (WeightedCoeff.holderProduct (p := 2) (q := 2)).le_opNorm₂ _ _
    _ ≤ 1*2*2 := by
      apply mul_le_mul
      · exact mul_le_mul WeightedCoeff.norm_holderProduct_le
          (by simpa only [norm_shift] using norm_puncturedLattice_two_le)
          (norm_nonneg _) (by norm_num)
      · simpa only [norm_shift] using norm_puncturedLattice_two_le
      · exact norm_nonneg _
      · norm_num
    _ = _ := by norm_num

end NLS.Coeff
