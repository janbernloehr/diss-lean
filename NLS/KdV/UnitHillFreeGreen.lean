import NLS.KdV.UnitHillFreeIsomorphism

/-! # The actual free endpoint Green vector

Its coefficient is the physical inverse massive symbol at EVERY frequency.
The trace is a strictly positive real Fourier sum, proving the nonzero
Schur denominator needed for the full zero-trace Dirichlet inverse.
-/
noncomputable section
open scoped ENNReal
namespace NLS.KdV
open NLS.Fourier NLS.ZakharovShabat

/-- The original unit-period trace is the absolutely convergent raw coefficient sum. -/
theorem hasSum_unitDirichletTrace (f : ScalarDomain 2) :
    HasSum (fun n : ℤ => f.val n) (unitDirichletTrace f) := by
  let a : Coeff 1 := WeightedCoeff.sobolevToL1CLM 2 (by norm_num) f
  have ha : Summable (fun n : ℤ => a n) := (lp.memℓp a).summable_of_one
  have hs : Summable (fun n : ℤ => f.val n) := by
    have he : (fun n : ℤ => f.val n) = fun n => a n := by
      funext n
      exact (WeightedCoeff.sobolevToL1CLM_apply 2 (by norm_num) f n).symm
    rw [he]
    exact ha
  have ht : unitDirichletTrace f = ∑' n : ℤ, f.val n := by
    change periodOneSobolevSynthesis f ((0:ℝ) : AddCircle (2:ℝ)) = _
    rw [periodOneSobolevSynthesis_apply, periodOneSynthesis_eq_tsum]
    simp only [wave_at_zero, mul_one, WeightedCoeff.sobolevToL1CLM_apply]
  rw [ht]
  exact hs.hasSum

/-- The actual full-dual free inverse applied to endpoint evaluation. -/
def unitHillFreeGreen : ScalarDomain 2 := unitHillFreeDualIsomorphism.symm unitDirichletTrace

theorem unitHillFreeGreen_coefficient (n : ℤ) :
    unitHillFreeGreen.val n = (((1+freeHillValue (2*n):ℝ)⁻¹):ℂ) := by
  rw [unitHillFreeGreen, unitHillFreeDualIsomorphism_symm_coefficient,
    unitDirichletTrace_scalarMode, mul_one]

/-- The trace Schur denominator is strictly positive in the actual normalization. -/
theorem unitDirichletTrace_unitHillFreeGreen_re_pos :
    0 < (unitDirichletTrace unitHillFreeGreen).re := by
  have hs := Complex.reCLM.hasSum (hasSum_unitDirichletTrace unitHillFreeGreen)
  have hnonneg (n : ℤ) : 0 ≤ (unitHillFreeGreen.val n).re := by
    rw [unitHillFreeGreen_coefficient, ← Complex.ofReal_inv, Complex.ofReal_re]
    have hv : 0 ≤ freeHillValue (2*n) := by unfold freeHillValue; positivity
    positivity
  have hzero : 0 < (unitHillFreeGreen.val 0).re := by
    rw [unitHillFreeGreen_coefficient]
    norm_num [freeHillValue]
  have hp := hs.summable.tsum_pos hnonneg 0 hzero
  rw [hs.tsum_eq] at hp
  exact hp

theorem unitDirichletTrace_unitHillFreeGreen_ne_zero :
    unitDirichletTrace unitHillFreeGreen ≠ 0 := by
  intro hz
  have hp := unitDirichletTrace_unitHillFreeGreen_re_pos
  rw [hz, Complex.zero_re] at hp
  exact lt_irrefl 0 hp

end NLS.KdV
