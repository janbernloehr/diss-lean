import NLS.SequenceSpaces.PeriodOneFourierLebesgueMiuraProduct
import NLS.SequenceSpaces.CompactRowMajorant

/-! # Compact native Miura products at every finite Fourier-Lebesgue exponent

The full weighted Hilbert row estimate retains an inverse weight of
order 1/2+1/(2p). Its p-th power is summable, so finite output truncations
converge in operator norm. All coefficients may be complex and infinite.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS

theorem isCompactOperator_periodOneFourierLebesgueMiuraProduct
    (s p : ℝ) (hs : -1/2≤s) (hp : 2<p) [Fact (1≤ENNReal.ofReal p)]
    (a : WeightedCoeff (Weight.sobolev (s+1)) (ENNReal.ofReal p)) :
    IsCompactOperator (periodOneFourierLebesgueMiuraProduct s p hs hp a) := by
  let r : ℝ := s+1/2+1/(2*p)
  let d : ℝ := 1/2+1/(2*p)
  have hp0 : 0<p := by linarith
  have hδ : 0<1/(2*p) := by positivity
  have hr : 0≤r := by dsimp only [r];linarith
  have hd : 1/2<d := by dsimp only [d];linarith
  have hdp : 1<d*p := by
    dsimp only [d]
    have hcancel : (1/(2*p))*p=1/2 := by field_simp
    nlinarith
  let L := periodOneFourierLebesgueMiuraHilbertInclusion s p hp
  let J := (WeightedCoeff.weightIsometry (Weight.sobolev s) (ENNReal.ofReal p)).toContinuousLinearEquiv
  let T := J.toContinuousLinearMap.comp (periodOneFourierLebesgueMiuraProduct s p hs hp a)
  let C : ℝ := (2*(2 : ℝ)^r*‖L a‖)*‖L‖
  have hC : 0≤C := by dsimp only [C];positivity
  let b0 : Coeff (ENNReal.ofReal p) := ⟨fun n => (Weight.sobolev d n : ℂ)⁻¹,
    Weight.inverse_sobolev_memlp (by simpa only [ENNReal.toReal_ofReal hp0.le] using hp0)
      (by simpa only [ENNReal.toReal_ofReal hp0.le] using hdp)⟩
  let b : Coeff (ENNReal.ofReal p) := (C : ℂ) • b0
  have hTc : IsCompactOperator T := by
    apply Coeff.isCompactOperator_of_rowMajorant ENNReal.ofReal_ne_top T b
    intro n v
    have hraw : (periodOneFourierLebesgueMiuraProduct s p hs hp a v).val n=
        (periodOneFractionalMiuraProduct r hr d hd (L a) (L v)).val n := by
      rw [periodOneFourierLebesgueMiuraProduct_apply,periodOneFractionalMiuraProduct_apply]
      simp only [L,periodOneFourierLebesgueMiuraHilbertInclusion_apply]
    have hw : (Weight.sobolev s n : ℂ)=
        (Weight.sobolev d n : ℂ)⁻¹*(Weight.sobolev r n : ℂ) := by
      have hsrd : s=r-d := by dsimp only [r,d];ring
      rw [hsrd]
      exact sobolev_sub_eq_inverse_sobolev_mul r d n
    change ‖(Weight.sobolev s n : ℂ)*(periodOneFourierLebesgueMiuraProduct s p hs hp a v).val n‖≤_
    rw [hraw,hw,mul_assoc,norm_mul]
    calc
      _ ≤ ‖(Weight.sobolev d n : ℂ)⁻¹‖*((2*(2 : ℝ)^r*‖L a‖)*‖L v‖) :=
        mul_le_mul_of_nonneg_left
          (weighted_periodOneFractionalMiuraProduct_row_bound r hr d hd (L a) (L v) n) (norm_nonneg _)
      _ ≤ ‖(Weight.sobolev d n : ℂ)⁻¹‖*((2*(2 : ℝ)^r*‖L a‖)*(‖L‖*‖v‖)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (L.le_opNorm v) (by positivity)) (norm_nonneg _)
      _ = ‖b n‖*‖v‖ := by
        change _=‖(C : ℂ)*(Weight.sobolev d n : ℂ)⁻¹‖*‖v‖
        rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hC]
        dsimp only [C]
        ring
  have he : periodOneFourierLebesgueMiuraProduct s p hs hp a=J.symm.toContinuousLinearMap.comp T := by
    ext v
    exact (J.symm_apply_apply _).symm
  rw [he]
  exact hTc.clm_comp J.symm.toContinuousLinearMap

end NLS
