import NLS.SequenceSpaces.PhysicalRealMeanZeroWeighted

/-! The inverse of the exact ORIGINAL weighted Fourier differential has
its literal square-root coefficient at EVERY signed index, including zero. -/
noncomputable section
open Complex
namespace NLS

theorem physical_mean_zero_fourier_inverse_coefficient (v w : Weight)
    (L : physicalRealMeanZeroWeightedSubmodule v ≃L[ℝ] physicalRealMeanZeroWeightedSubmodule w)
    (hL : ∀ q j,(L q).val.val j=(Real.sqrt (2*(j.natAbs:ℝ)*Real.pi):ℂ)⁻¹*q.val.val j)
    (z : physicalRealMeanZeroWeightedSubmodule w) (j : ℤ) :
    (L.symm z).val.val j=(Real.sqrt (2*(j.natAbs:ℝ)*Real.pi):ℂ)*z.val.val j := by
  by_cases hj : j=0
  · subst j
    rw [show (L.symm z).val.val 0=0 from (L.symm z).property.2,
      show z.val.val 0=0 from z.property.2,mul_zero]
  have hn : (0:ℝ)<(j.natAbs:ℝ) := by exact_mod_cast Int.natAbs_pos.mpr hj
  have hp : 0<Real.sqrt (2*(j.natAbs:ℝ)*Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have hne : (Real.sqrt (2*(j.natAbs:ℝ)*Real.pi):ℂ)≠0 := Complex.ofReal_ne_zero.mpr hp.ne'
  have h := hL (L.symm z) j
  rw [L.apply_symm_apply] at h
  calc
    (L.symm z).val.val j=(Real.sqrt (2*(j.natAbs:ℝ)*Real.pi):ℂ)*
        ((Real.sqrt (2*(j.natAbs:ℝ)*Real.pi):ℂ)⁻¹*(L.symm z).val.val j) := by
      rw [←mul_assoc,mul_inv_cancel₀ hne,one_mul]
    _=_ := congrArg (fun c : ℂ => (Real.sqrt (2*(j.natAbs:ℝ)*Real.pi):ℂ)*c) h.symm

end NLS
