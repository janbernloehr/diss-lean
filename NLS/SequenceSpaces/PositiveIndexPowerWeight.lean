import NLS.SequenceSpaces.PositiveIndexWeight
import NLS.SequenceSpaces.PuncturedLattice

/-! # Bounded reciprocals of positive-index power weights -/
noncomputable section
open scoped ENNReal
namespace NLS.Coeff

def positiveIndexPowerReciprocal (r : ℕ) : Coeff ⊤ :=
  ⟨fun m => (positiveIndexWeight m^r)⁻¹,memℓp_infty ⟨1,by
    rintro _ ⟨m,rfl⟩
    change ‖(positiveIndexWeight m^r)⁻¹‖ ≤ 1
    rw [norm_inv,norm_pow]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (one_le_norm_positiveIndexWeight m))⟩⟩

@[simp] theorem positiveIndexPowerReciprocal_apply (r : ℕ) (m : ℤ) :
    positiveIndexPowerReciprocal r m = (positiveIndexWeight m^r)⁻¹ := rfl

def positiveReciprocalHilbert : Coeff 2 :=
  ⟨fun m => if 0 < m then (m : ℂ)⁻¹ else 0,by
    apply (lp.memℓp (puncturedLattice 2 (by norm_num))).mono'
    intro m
    by_cases hm : 0 < m
    · simp only [if_pos hm,puncturedLattice_apply,if_neg (ne_of_gt hm),le_refl]
    · simp only [if_neg hm,norm_zero]
      exact norm_nonneg _⟩

@[simp] theorem positiveReciprocalHilbert_apply (m : ℤ) :
    positiveReciprocalHilbert m = if 0 < m then (m : ℂ)⁻¹ else 0 := rfl

theorem norm_positiveReciprocalHilbert_le : ‖positiveReciprocalHilbert‖ ≤ 2 := by
  apply le_trans (lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0) ?_) norm_puncturedLattice_two_le
  intro m
  by_cases hm : 0 < m
  · simp only [positiveReciprocalHilbert_apply,if_pos hm,puncturedLattice_apply,if_neg (ne_of_gt hm),le_refl]
  · simp only [positiveReciprocalHilbert_apply,if_neg hm,norm_zero]
    exact norm_nonneg _

end NLS.Coeff
