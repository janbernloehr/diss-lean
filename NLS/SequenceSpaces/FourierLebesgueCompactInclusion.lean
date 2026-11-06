import NLS.SequenceSpaces.PeriodOneMiuraCompactJacobian

/-! # Compact loss of one order in every finite Banach Fourier-Lebesgue norm -/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS

theorem isCompactOperator_fourierLebesgueInclusion_sub_one
    (s : ℝ) (p : ℝ≥0∞) (hp : p≠⊤) (hp1 : 1<p) [Fact (1≤p)] :
    IsCompactOperator (WeightedCoeff.sobolevInclusion (p := p) (by linarith : s≤s+1)) := by
  have hpR : 1<p.toReal := (ENNReal.toReal_lt_toReal (by simp) hp).mpr hp1
  let b : Coeff p := ⟨fun n => (Weight.sobolev 1 n : ℂ)⁻¹,
    Weight.inverse_sobolev_memlp (by linarith) (by simpa only [one_mul] using hpR)⟩
  let L := WeightedCoeff.sobolevInclusion (p := p) (by linarith : s≤s+1)
  let J := (WeightedCoeff.weightIsometry (Weight.sobolev s) p).toContinuousLinearEquiv
  let T := J.toContinuousLinearMap.comp L
  have hTc : IsCompactOperator T := by
    apply Coeff.isCompactOperator_of_rowMajorant hp T b
    intro n v
    change ‖(Weight.sobolev s n : ℂ)*(L v).val n‖≤‖(Weight.sobolev 1 n : ℂ)⁻¹‖*‖v‖
    rw [WeightedCoeff.sobolevInclusion_apply]
    have hw : (Weight.sobolev s n : ℂ)=
        (Weight.sobolev 1 n : ℂ)⁻¹*(Weight.sobolev (s+1) n : ℂ) := by
      simpa only [add_sub_cancel_right] using sobolev_sub_eq_inverse_sobolev_mul (s+1) 1 n
    rw [hw,mul_assoc,norm_mul]
    exact mul_le_mul_of_nonneg_left
      (lp.norm_apply_le_norm (ne_of_gt (zero_lt_one.trans hp1))
        (WeightedCoeff.weightEquiv (Weight.sobolev (s+1)) p v) n) (norm_nonneg _)
  have he : L=J.symm.toContinuousLinearMap.comp T := by
    ext v
    exact (J.symm_apply_apply _).symm
  change IsCompactOperator L
  rw [he]
  exact hTc.clm_comp J.symm.toContinuousLinearMap

end NLS
