import NLS.SequenceSpaces.PeriodOneMiuraSobolevJacobian
import NLS.SequenceSpaces.CompactRowMajorant

/-! # Compact native Miura Jacobian remainders at every Sobolev order

The actual tame product has an inverse-bracket row majorant in the
normalized H^(t-1) target. This proves compactness directly for every
t>=0, including the L2-to-H-minus-one endpoint and complex coefficients.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS

private theorem compact_smul_clm
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (T : E →L[ℂ] F) (hT : IsCompactOperator T) (c : ℂ) :
    IsCompactOperator (c • T) := by
  change IsCompactOperator (fun v => c • T v)
  exact hT.smul c

private theorem native_product_weighted_row_bound
    (t : ℝ) (ht : 0≤t) (a v : WeightedCoeff (Weight.sobolev t) 2) (n : ℤ) :
    ‖(Weight.sobolev t n : ℂ)*(periodOneSobolevMiuraProduct t ht a v).val n‖≤
      (2*(2 : ℝ)^t*‖a‖)*‖v‖ := by
  let u := WeightedCoeff.sobolevToL2 ht a
  let w := WeightedCoeff.sobolevToL2 ht v
  have hu : Memℓp (fun j => (Weight.sobolev t j : ℂ)*u j) 2 := by
    simpa only [u,WeightedCoeff.sobolevToL2_apply] using
      (show Memℓp (fun j => (Weight.sobolev t j : ℂ)*a.val j) 2 from a.property)
  have hw : Memℓp (fun j => (Weight.sobolev t j : ℂ)*w j) 2 := by
    simpa only [w,WeightedCoeff.sobolevToL2_apply] using
      (show Memℓp (fun j => (Weight.sobolev t j : ℂ)*v.val j) 2 from v.property)
  have hU : (⟨_,hu⟩ : Coeff 2)=WeightedCoeff.weightEquiv (Weight.sobolev t) 2 a := by
    ext j
    simp only [u,WeightedCoeff.sobolevToL2_apply,WeightedCoeff.weightEquiv_apply]
  have hW : (⟨_,hw⟩ : Coeff 2)=WeightedCoeff.weightEquiv (Weight.sobolev t) 2 v := by
    ext j
    simp only [w,WeightedCoeff.sobolevToL2_apply,WeightedCoeff.weightEquiv_apply]
  have H := weighted_miura_product_uniform_bound t ht u w hu hw n
  rw [hU,hW] at H
  change Weight.sobolev t n*‖(periodOneMiuraProduct u w).val n‖≤
    (2 : ℝ)^t*(‖a‖*‖w‖+‖u‖*‖v‖) at H
  have hau : ‖u‖≤‖a‖ := WeightedCoeff.norm_sobolevToL2_le ht a
  have hvw : ‖w‖≤‖v‖ := WeightedCoeff.norm_sobolevToL2_le ht v
  change ‖(Weight.sobolev t n : ℂ)*(periodOneMiuraProduct u w).val n‖≤_
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Weight.positive _ n)]
  exact H.trans (by nlinarith [mul_le_mul_of_nonneg_left hvw (norm_nonneg a),
    mul_le_mul_of_nonneg_right hau (norm_nonneg v),
    Real.rpow_pos_of_pos (by norm_num : (0 : ℝ)<2) t])

/-- The literal native Miura product with one fixed H^t coefficient is
compact H^t-to-H^(t-1), for EVERY t>=0 and arbitrary complex coefficient. -/
theorem isCompactOperator_periodOneSobolevMiuraProduct
    (t : ℝ) (ht : 0≤t) (a : WeightedCoeff (Weight.sobolev t) 2) :
    IsCompactOperator (periodOneSobolevMiuraProductCLM t ht a) := by
  let J := (WeightedCoeff.weightIsometry (Weight.sobolev (t-1)) 2).toContinuousLinearEquiv
  let T := J.toContinuousLinearMap.comp (periodOneSobolevMiuraProductCLM t ht a)
  let C : ℝ := 2*(2 : ℝ)^t*‖a‖
  have hC : 0≤C := by dsimp only [C];positivity
  let b : Coeff 2 := (C : ℂ) • inverseBracketCoefficients
  have hTc : IsCompactOperator T := by
    apply Coeff.isCompactOperator_of_rowMajorant (by norm_num) T b
    intro n v
    change ‖(Weight.sobolev (t-1) n : ℂ)*(periodOneSobolevMiuraProduct t ht a v).val n‖≤_
    rw [sobolev_sub_one_eq_inverseBracket_mul,mul_assoc,norm_mul]
    calc
      _ ≤ ‖inverseBracketCoefficients n‖*(C*‖v‖) :=
        mul_le_mul_of_nonneg_left (native_product_weighted_row_bound t ht a v n) (norm_nonneg _)
      _ = ‖b n‖*‖v‖ := by
        simp only [b,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,norm_mul,Complex.norm_real,
          Real.norm_eq_abs,abs_of_nonneg hC]
        ring
  have he : periodOneSobolevMiuraProductCLM t ht a=J.symm.toContinuousLinearMap.comp T := by
    ext v
    exact (J.symm_apply_apply _).symm
  rw [he]
  exact hTc.clm_comp J.symm.toContinuousLinearMap

/-- Forgetting one Sobolev order is compact in the literal native norms,
for EVERY real order, including negative orders. -/
theorem isCompactOperator_sobolevInclusion_sub_one (t : ℝ) :
    IsCompactOperator (WeightedCoeff.sobolevInclusion (p := 2) (by linarith : t-1≤t)) := by
  let L := WeightedCoeff.sobolevInclusion (p := 2) (by linarith : t-1≤t)
  let J := (WeightedCoeff.weightIsometry (Weight.sobolev (t-1)) 2).toContinuousLinearEquiv
  let T := J.toContinuousLinearMap.comp L
  have hTc : IsCompactOperator T := by
    apply Coeff.isCompactOperator_of_rowMajorant (by norm_num) T inverseBracketCoefficients
    intro n v
    change ‖(Weight.sobolev (t-1) n : ℂ)*(L v).val n‖≤_
    have hv : (L v).val n=v.val n := WeightedCoeff.sobolevInclusion_apply _ v n
    rw [hv]
    rw [sobolev_sub_one_eq_inverseBracket_mul,mul_assoc,norm_mul]
    exact mul_le_mul_of_nonneg_left
      (lp.norm_apply_le_norm (by norm_num) (WeightedCoeff.weightEquiv (Weight.sobolev t) 2 v) n)
      (norm_nonneg _)
  have he : L=J.symm.toContinuousLinearMap.comp T := by
    ext v
    exact (J.symm_apply_apply _).symm
  change IsCompactOperator L
  rw [he]
  exact hTc.clm_comp J.symm.toContinuousLinearMap

/-- The ACTUAL native shifted Jacobian differs compactly from its exact
free mass operator at every complex base and EVERY t>=0. -/
theorem isCompactOperator_periodOneSobolevMiuraJacobian_sub_mass
    (m : ℕ) (t : ℝ) (ht : 0≤t) (a : WeightedCoeff (Weight.sobolev t) 2) :
    IsCompactOperator (periodOneSobolevMiuraJacobian m t ht a-periodOneSobolevMassOperator m t) := by
  have he : periodOneSobolevMiuraJacobian m t ht a-periodOneSobolevMassOperator m t=
      (2 : ℂ) • periodOneSobolevMiuraProductCLM t ht a := by
    ext v
    apply Subtype.ext
    funext n
    simp only [_root_.sub_apply,WeightedCoeff.sub_val,
      periodOneSobolevMiuraJacobian_apply,periodOneSobolevMassOperator_apply,
      _root_.smul_apply,WeightedCoeff.smul_val,
      periodOneSobolevMiuraProductCLM_apply,periodOneSobolevMiuraProduct_apply]
    ring
  rw [he]
  exact compact_smul_clm _ (isCompactOperator_periodOneSobolevMiuraProduct t ht a) (2 : ℂ)

end NLS
