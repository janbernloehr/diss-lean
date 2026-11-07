import NLS.SequenceSpaces.PeriodOneMiuraShift
import NLS.SequenceSpaces.CompactRowMajorant

/-! The actual distributional Miura derivative is its explicit massive
first-order Fourier equivalence plus a compact operator. All products
are the original convolution in the genuine Hminus-one norm. -/
noncomputable section
open scoped ENNReal
namespace NLS

theorem isCompactOperator_boundedCoefficientsHminusOne :
    IsCompactOperator boundedCoefficientsHminusOne := by
  let T : Coeff ⊤ →L[ℂ] Coeff 2 :=
    Coeff.holderProduct (p := 2) (r := ⊤) (q := 2) inverseBracketCoefficients
  have hc : IsCompactOperator T := Coeff.isCompactOperator_of_rowMajorant (by norm_num) T
    inverseBracketCoefficients (by
      intro k b
      change ‖inverseBracketCoefficients k*b k‖ ≤ ‖inverseBracketCoefficients k‖*‖b‖
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (lp.norm_apply_le_norm (by simp) b k) (norm_nonneg _))
  exact hc.clm_comp (WeightedCoeff.weightIsometry (Weight.sobolev (-1)) 2).symm.toContinuousLinearEquiv.toContinuousLinearMap

theorem isCompactOperator_periodOneL2Inclusion : IsCompactOperator periodOneL2Inclusion :=
  isCompactOperator_boundedCoefficientsHminusOne.comp_clm (Coeff.exponentInclusion (show (2:ℝ≥0∞) ≤ ⊤ from le_top))

theorem isCompactOperator_periodOneMiuraProduct_fixed (u : Coeff 2) :
    IsCompactOperator (periodOneMiuraProduct u) :=
  isCompactOperator_boundedCoefficientsHminusOne.comp_clm
    (Coeff.youngConvolutionCLM youngRelation_two_two_top u)

def periodOneMiuraLinearization (u : Coeff 2) : Coeff 2 →L[ℂ] PeriodOneHminusOne :=
  periodOneMassOperator 0-periodOneL2Inclusion+(2:ℂ) • periodOneMiuraProduct u

theorem periodOneMiuraLinearization_apply (u h : Coeff 2) (k : ℤ) :
    (periodOneMiuraLinearization u h).val k =
      2*Complex.I*(Real.pi:ℂ)*k*h k+2*(∑' j : ℤ, u (k-j)*h j) := by
  change (periodOneMassOperator 0 h).val k-(periodOneL2Inclusion h).val k+
    (2:ℂ)*(periodOneMiuraProduct u h).val k = _
  rw [periodOneMassOperator_apply,periodOneL2Inclusion_apply,periodOneMiuraProduct_apply]
  simp only [periodOneMassSymbol,Nat.cast_zero,zero_add,Complex.ofReal_one]
  ring

theorem hasFDerivAt_periodOneMiura (u : Coeff 2) :
    HasFDerivAt periodOneMiura (periodOneMiuraLinearization u) u := by
  have hq := periodOneMiuraProduct.hasFDerivAt_of_bilinear (hasFDerivAt_id u) (hasFDerivAt_id u)
  have he : periodOneMiuraProduct.precompR (Coeff 2) u (ContinuousLinearMap.id ℂ (Coeff 2))+
      periodOneMiuraProduct.precompL (Coeff 2) (ContinuousLinearMap.id ℂ (Coeff 2)) u =
        (2:ℂ) • periodOneMiuraProduct u := by
    apply ContinuousLinearMap.ext
    intro h
    change periodOneMiuraProduct u h+periodOneMiuraProduct h u=(2:ℂ) • periodOneMiuraProduct u h
    rw [periodOneMiuraProduct_comm h u,two_smul]
  rw [show id u=u from rfl,he] at hq
  have hd := ((periodOneMassOperator 0).hasFDerivAt.add hq).sub periodOneL2Inclusion.hasFDerivAt
  change HasFDerivAt periodOneMiura
    (periodOneMassOperator 0+(2:ℂ) • periodOneMiuraProduct u-periodOneL2Inclusion) u at hd
  convert hd using 1
  unfold periodOneMiuraLinearization
  abel

theorem fderiv_periodOneMiura (u : Coeff 2) :
    fderiv ℂ periodOneMiura u=periodOneMiuraLinearization u :=
  (hasFDerivAt_periodOneMiura u).fderiv

theorem isCompactOperator_periodOneMiuraLinearization_sub_mass (u : Coeff 2) :
    IsCompactOperator (periodOneMiuraLinearization u-periodOneMassOperator 0) := by
  have he : periodOneMiuraLinearization u-periodOneMassOperator 0 =
      (2:ℂ) • periodOneMiuraProduct u-periodOneL2Inclusion := by
    unfold periodOneMiuraLinearization
    abel
  rw [he]
  exact ((isCompactOperator_periodOneMiuraProduct_fixed u).smul (2:ℂ)).sub isCompactOperator_periodOneL2Inclusion

end NLS
