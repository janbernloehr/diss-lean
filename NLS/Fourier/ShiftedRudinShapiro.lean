import NLS.Fourier.RudinShapiroCoefficients
import NLS.SequenceSpaces.Translation

/-!
# Disjoint Rudin–Shapiro frequency blocks

Multiplying the polynomial P_(2j) by frequency 4^j moves its unit-norm
coefficients to [4^j, 2*4^j). These blocks are disjoint, and the uniform norm
is at most sqrt(2)*2^j. Both sharpness examples in Appendix A use this family.
-/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal ZeroAtInfty
namespace NLS.Fourier
variable {L : ℝ} [Fact (0 < L)]

/-- The polynomial P_(2j) shifted to the block beginning at frequency 4^j. -/
def shiftedRudinShapiro (j : ℕ) : C(AddCircle L,ℂ) :=
  fourier (4^j : ℕ) * (rudinShapiroPair (2*j)).1

/-- The polynomial length agrees with the selected frequency-block size. -/
theorem pow_two_mul_eq_four_pow (j : ℕ) : (2:ℕ)^(2*j) = 4^j := by
  rw [pow_mul]
  norm_num

/-- Every coefficient in the shifted block has norm one; all others vanish. -/
theorem shiftedRudinShapiro_coeff_norm (j : ℕ) (k : ℤ) :
    ‖fourierCoeff (shiftedRudinShapiro (L := L) j) k‖ =
      if (4^j:ℕ) ≤ k ∧ k < 2*(4^j:ℕ) then 1 else 0 := by
  rw [shiftedRudinShapiro,fourierCoeff_fourier_mul,(rudinShapiro_coeff_norm (2*j) (k-(4^j:ℕ))).1,
    pow_two_mul_eq_four_pow]
  have he : (0 ≤ k-(4^j:ℕ) ∧ k-(4^j:ℕ) < (4^j:ℕ)) ↔
      ((4^j:ℕ) ≤ k ∧ k < 2*(4^j:ℕ)) := by omega
  simp only [he]

/-- Distinct blocks have no common frequency. -/
theorem shiftedRudinShapiro_blocks_disjoint {i j : ℕ} (hij : i ≠ j) (k : ℤ)
    (hi : (4^i:ℕ) ≤ k ∧ k < 2*(4^i:ℕ)) : ¬((4^j:ℕ) ≤ k ∧ k < 2*(4^j:ℕ)) := by
  intro hj
  rcases lt_or_gt_of_ne hij with h | h
  · have hp : 4^i*4 ≤ (4:ℕ)^j := by
      rw [← pow_succ]
      exact Nat.pow_le_pow_right (by norm_num) h
    have hp' : ((4^i*4:ℕ):ℤ) ≤ (4^j:ℕ) := by exact_mod_cast hp
    have hi0 : (0:ℤ) < (4^i:ℕ) := by positivity
    push_cast at hp'
    omega
  · have hp : 4^j*4 ≤ (4:ℕ)^i := by
      rw [← pow_succ]
      exact Nat.pow_le_pow_right (by norm_num) h
    have hp' : ((4^j*4:ℕ):ℤ) ≤ (4^i:ℕ) := by exact_mod_cast hp
    have hj0 : (0:ℤ) < (4^j:ℕ) := by positivity
    push_cast at hp'
    omega

/-- The uniform norm grows at most as the square root of the block length. -/
theorem norm_shiftedRudinShapiro_le (j : ℕ) :
    ‖shiftedRudinShapiro (L := L) j‖ ≤ Real.sqrt 2 * (2:ℝ)^j := by
  have hN : (2:ℝ)^(2*j+1) = 2*((2:ℝ)^j)^2 := by
    rw [pow_succ,show 2*j = j*2 by omega,pow_mul]
    ring
  calc
    _ ≤ ‖(rudinShapiroPair (L := L) (2*j)).1‖ := by
      simpa only [shiftedRudinShapiro,fourier_norm,one_mul] using
        norm_mul_le (fourier (4^j:ℕ) : C(AddCircle L,ℂ)) (rudinShapiroPair (2*j)).1
    _ ≤ Real.sqrt (2^(2*j+1)) := norm_rudinShapiro_le (2*j)
    _ = _ := by rw [hN,Real.sqrt_mul (by norm_num),Real.sqrt_sq (by positivity)]

open SmoothPeriodicTest

/-- An original smooth Fourier mode has the expected physical-circle realization. -/
theorem toContinuousCLM_mode (k : ℤ) :
    toContinuousCLM (mode k : SmoothPeriodicTest L) = fourier k := by
  ext y
  obtain ⟨x,rfl⟩ := QuotientAddGroup.mk_surjective y
  rw [toContinuousCLM_apply,mode_apply_physical,fourier_coe_apply]
  congr 1
  ring

/-- The finite frequency support of the jth shifted polynomial. -/
def shiftedRudinShapiroBlock (j : ℕ) : Finset ℤ :=
  Finset.Ico (4^j:ℕ) (2*(4^j:ℕ))

/-- Finite Fourier synthesis recovers the actual shifted continuous polynomial. -/
theorem continuousFourierPolynomial_shiftedRudinShapiro (j : ℕ) :
    continuousFourierPolynomial (shiftedRudinShapiroBlock j)
      (fourierCoeff (shiftedRudinShapiro (L := L) j)) = shiftedRudinShapiro (L := L) j := by
  apply ContinuousMap.toLp_injective (p := 2) AddCircle.haarAddCircle (𝕜 := ℂ)
  apply circleLp_fourierCoeff_injective
  funext k
  dsimp only
  rw [fourierCoeff_congr_ae (ContinuousMap.coeFn_toLp _ _),
    fourierCoeff_congr_ae (ContinuousMap.coeFn_toLp _ _),continuousFourierPolynomial_coefficient]
  split_ifs with hk
  · rfl
  · symm
    apply norm_eq_zero.mp
    rw [shiftedRudinShapiro_coeff_norm,if_neg (by simpa only [shiftedRudinShapiroBlock,Finset.mem_Ico] using hk)]

end NLS.Fourier
