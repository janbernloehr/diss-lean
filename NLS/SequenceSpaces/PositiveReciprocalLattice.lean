import NLS.SequenceSpaces.PuncturedLattice

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal

namespace NLS.Coeff



def positivePuncturedLattice (p : ℝ≥0∞) (hp : 1 < p) : Coeff p :=
  ⟨fun m : ℤ => if 0 < m then (m : ℂ)⁻¹ else 0, by
    apply (memlp_puncturedLattice hp).norm.mono
    intro m
    by_cases hm : 0 < m
    · simp only [if_pos hm,if_neg (by omega : m ≠ 0)]
      exact le_rfl
    · simp only [if_neg hm,norm_zero]
      exact norm_nonneg _⟩

theorem positivePuncturedLattice_apply (p : ℝ≥0∞) (hp : 1 < p) (m : ℤ) :
    positivePuncturedLattice p hp m = if 0 < m then (m : ℂ)⁻¹ else 0 := rfl

theorem positivePuncturedLattice_natSucc (p : ℝ≥0∞) (hp : 1 < p) (k : ℕ) :
    positivePuncturedLattice p hp ((k+1 : ℕ) : ℤ) = ((k+1 : ℕ) : ℂ)⁻¹ := by
  rw [positivePuncturedLattice_apply,if_pos (by omega : 0 < ((k+1 : ℕ) : ℤ))]
  push_cast
  rfl

theorem norm_positivePuncturedLattice_two_le :
    ‖positivePuncturedLattice 2 (by norm_num)‖ ≤ 2 := by
  apply le_trans (b := ‖puncturedLattice 2 (by norm_num)‖)
  · apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    intro m
    by_cases hm : 0 < m
    · simp only [positivePuncturedLattice_apply,if_pos hm,puncturedLattice_apply,
        if_neg (by omega : m ≠ 0)]
      exact le_rfl
    · simp only [positivePuncturedLattice_apply,if_neg hm,norm_zero]
      exact norm_nonneg _
  · exact norm_puncturedLattice_two_le

end NLS.Coeff
