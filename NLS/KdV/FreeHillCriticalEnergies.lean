import NLS.ComplexAnalysis.RightHalfPlaneSquareRoot
import NLS.KdV.FreeFrequencyPsi
import NLS.KdV.ClassicalBranchPrimitive

/-! # The complete actual free Hill critical energy set

The free origin has derivative -1. The global squared-frequency chain
identity and the exact sine zero set give every positive critical label.
-/
noncomputable section
open Set Complex NLS.ComplexAnalysis
namespace NLS.KdV

/-- The free energy origin is not a critical point: its actual derivative is -1. -/
theorem deriv_classicalHillDiscriminant_zero_energy : deriv (classicalHillDiscriminant 0) 0 = -1 := by
  have he : classicalHillDiscriminant 0 = fun z => 2*squaredCosh (-z) := by
    funext z
    rw [classicalHillDiscriminant_zero]
    have h := squaredCosh_neg_sq (sqrt z)
    rw [sq_sqrt] at h
    rw [h]
  rw [he]
  have hneg : HasDerivAt squaredCosh (1/2 : ℂ) (-(0 : ℂ)) := by simpa using hasDerivAt_squaredCosh_zero
  have hd := (hneg.comp (h := fun z : ℂ => -z) 0
    ((hasDerivAt_id (0 : ℂ)).neg)).const_mul 2
  convert hd.deriv using 1 <;> norm_num

/-- The global frequency pullback of the actual free energy derivative. -/
theorem classicalHill_free_frequency_derivative (z : ℂ) :
    (2*z)*deriv (classicalHillDiscriminant 0) (z^2) = -2*sin z := by
  have he : (fun w : ℂ => classicalHillDiscriminant 0 (w^2)) = fun w => 2*cos w := by
    funext w
    rw [classicalHillDiscriminant_zero]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp (sq_sqrt (w^2)) with h | h
    · rw [h]
    · rw [h,cos_neg]
  have hd := ((analyticOnNhd_classicalHillDiscriminant 0 (z^2) (mem_univ _)).differentiableAt.hasDerivAt).comp z ((hasDerivAt_id z).pow 2)
  simp only [Function.comp_def, Pi.pow_apply, id_eq, Nat.cast_ofNat, show 2-1=1 by decide, pow_one, mul_one] at hd
  rw [he] at hd
  have hright := (Complex.hasDerivAt_cos z).const_mul 2
  linear_combination hd.unique hright

/-- All and only the positive free Hill energies are critical, with no slit restriction. -/
theorem classicalHill_free_critical_exhaustive (energy : ℂ) :
    deriv (classicalHillDiscriminant 0) energy = 0 ↔
      ∃ j : ℕ+, freeHillEnergy j = energy := by
  constructor
  · intro he
    have he0 : energy ≠ 0 := by
      intro h
      rw [h,deriv_classicalHillDiscriminant_zero_energy] at he
      norm_num at he
    have hz := classicalHill_free_frequency_derivative (sqrt energy)
    rw [sq_sqrt,he,mul_zero] at hz
    have hs : sin (sqrt energy) = 0 := by linear_combination hz / 2
    obtain ⟨k,hk⟩ := Complex.sin_eq_zero_iff.mp hs
    have hk0 : k ≠ 0 := by
      intro h
      rw [h,Int.cast_zero,zero_mul] at hk
      exact he0 (by rw [← sq_sqrt energy,hk]; norm_num)
    rcases lt_or_gt_of_ne hk0 with hkn | hkp
    · let j : ℕ+ := ⟨(-k).toNat,by omega⟩
      have hj : (j:ℤ) = -k := Int.toNat_of_nonneg (neg_nonneg.mpr hkn.le)
      have hjc : (j:ℂ) = -(k:ℂ) := by exact_mod_cast hj
      refine ⟨j,?_⟩
      have heq : freeHillEnergy j = ((j:ℂ)*Real.pi)^2 := by
        simp only [freeHillEnergy,ofReal_pow,ofReal_mul,ofReal_natCast]
      rw [heq,hjc,neg_mul,neg_sq,← hk,sq_sqrt]
    · let j : ℕ+ := ⟨k.toNat,by omega⟩
      have hj : (j:ℤ) = k := Int.toNat_of_nonneg hkp.le
      have hjc : (j:ℂ) = (k:ℂ) := by exact_mod_cast hj
      refine ⟨j,?_⟩
      have heq : freeHillEnergy j = ((j:ℂ)*Real.pi)^2 := by
        simp only [freeHillEnergy,ofReal_pow,ofReal_mul,ofReal_natCast]
      rw [heq,hjc,← hk,sq_sqrt]
  · rintro ⟨j,rfl⟩
    exact deriv_classicalHillDiscriminant_free_energy j

end NLS.KdV
