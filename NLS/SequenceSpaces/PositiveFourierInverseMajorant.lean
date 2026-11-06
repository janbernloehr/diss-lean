import NLS.SequenceSpaces.QuadraticPoleKernel
import NLS.SequenceSpaces.PositiveReciprocalLattice
import NLS.SequenceSpaces.TwoSequenceBound
import NLS.SequenceSpaces.Reflection

/-! # Positive Hilbert sequences controlled by Fourier data and inverse indices -/
noncomputable section
open scoped ENNReal
namespace NLS.Coeff

def positiveFamilyCoordinates (f : ℕ+ → ℂ) (j : ℤ) : ℂ :=
  if hj : 0 < j then f (positivePoleIndex j hj) else 0

def positiveFamilySequence (f : ℕ+ → ℂ) : Coeff 2 :=
  ofFunctionOrZero 2 (positiveFamilyCoordinates f)

theorem positiveFamilyCoordinates_nat (f : ℕ+ → ℂ) (k : ℕ+) :
    positiveFamilyCoordinates f (k : ℤ) = f k := by
  rw [positiveFamilyCoordinates,dif_pos (by exact_mod_cast k.pos)]
  congr 1


theorem positiveFamilySequence_bound (f : ℕ+ → ℂ) (u : Coeff 2) (C D : ℝ)
    (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hf : ∀ k : ℕ+, ‖f k‖ ≤ C*(‖u (k : ℤ)‖+‖u (-(k : ℤ))‖+D/(k : ℝ))) :
    Memℓp (positiveFamilyCoordinates f) 2 ∧
      ‖positiveFamilySequence f‖ ≤ C*(2*‖u‖+2*D) := by
  let d := positivePuncturedLattice 2 (by norm_num)
  let A : Coeff 2 := magnitude u+magnitude (reflection u)+(D : ℂ) • magnitude d
  let B : Coeff 2 := (C : ℂ) • A
  have hB (j : ℤ) : ‖B j‖ = C*(‖u j‖+‖u (-j)‖+D*‖d j‖) := by
    simp only [B,A,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,lp.coeFn_add,Pi.add_apply,
      magnitude_apply,reflection_apply,← Complex.ofReal_mul,← Complex.ofReal_add,
      Complex.norm_real,Real.norm_of_nonneg (by positivity : 0 ≤ C*(‖u j‖+‖u (-j)‖+D*‖d j‖))]
  have hdom (j : ℤ) : ‖positiveFamilyCoordinates f j‖ ≤ ‖B j‖ := by
    rw [hB]
    by_cases hj : 0 < j
    · rw [positiveFamilyCoordinates,dif_pos hj]
      let k := positivePoleIndex j hj
      have hk : (k : ℤ) = j := by
        change (j.toNat : ℤ) = j
        exact Int.toNat_of_nonneg hj.le
      have hkr : (k : ℝ) = j := positivePoleIndex_real j hj
      have hd : ‖d j‖ = 1/(j : ℝ) := by
        rw [positivePuncturedLattice_apply,if_pos hj,norm_inv]
        rw [show (j : ℂ) = ((j : ℝ) : ℂ) by norm_cast,Complex.norm_real,Real.norm_eq_abs,
          abs_of_pos (by exact_mod_cast hj : (0 : ℝ) < j),one_div]
      have h := hf k
      rw [hk,hkr] at h
      exact h.trans_eq (by rw [hd]; ring)
    · rw [positiveFamilyCoordinates,dif_neg hj,norm_zero]
      positivity
  have hmem : Memℓp (positiveFamilyCoordinates f) 2 := (lp.memℓp B).mono' hdom
  refine ⟨hmem,?_⟩
  have hnorm : ‖positiveFamilySequence f‖ ≤ ‖B‖ := by
    apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    intro j
    rw [positiveFamilySequence,ofFunctionOrZero_apply_of_mem 2 _ hmem]
    exact hdom j
  apply hnorm.trans
  rw [show ‖B‖ = ‖(C : ℂ)‖*‖A‖ from norm_smul _ _,Complex.norm_real,Real.norm_of_nonneg hC]
  apply mul_le_mul_of_nonneg_left _ hC
  have hA : ‖A‖ ≤ ‖magnitude u‖+‖magnitude (reflection u)‖+‖(D : ℂ) • magnitude d‖ :=
    (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
  simp only [norm_magnitude,reflection.norm_map,norm_smul,Complex.norm_real,Real.norm_of_nonneg hD] at hA
  have hd : ‖d‖ ≤ 2 := norm_positivePuncturedLattice_two_le
  nlinarith

end NLS.Coeff
