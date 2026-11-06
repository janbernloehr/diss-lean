import NLS.KdV.HillFreeSpectralCosineDerivative
import NLS.FunctionalAnalysis.NormPolarization
import Mathlib.Analysis.InnerProductSpace.l2Space

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open scoped ComplexConjugate
namespace NLS.KdV

variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

include h0q h0r in
/-- The real component of the ACTUAL original sequence derivative is fixed
by polarization against the physically normalized cosine directions. -/
theorem hillOriginalMeanZeroDerivativeAtZero_re (k : ℕ) (h : hillRealMeanZeroSourceSubmodule) :
    (hillOriginalMeanZeroDerivativeAtZero h k).re =
      Real.sqrt 2*(h.val.val.val (2*((k+1 : ℕ) : ℤ))).re := by
  let n : ℕ+ := ⟨k+1,by omega⟩
  have hi := NLS.FunctionalAnalysis.re_inner_map_eq_of_norm_map_eq
    hillOriginalMeanZeroDerivativeAtZero hillOriginalRawSourceCLM
    (fun x => (norm_hillOriginalMeanZeroDerivativeAtZero x).trans (norm_hillOriginalRawSourceCLM x).symm)
    h (hillOriginalFourierDirection n 1)
  rw [hillOriginalMeanZeroDerivativeAtZero_cosine h0q h0r n,
    hillOriginalRawSourceCLM_fourierDirection,inner_add_right,
    lp.inner_single_right,lp.inner_single_right,lp.inner_single_right] at hi
  have hn : (n : ℕ)-1 = k := by change (k+1)-1 = k; omega
  have hr : h.val.val.val (-(2*(n : ℤ))) = conj (h.val.val.val (2*(n : ℤ))) := by
    simpa only [SpectralWeight.toCoeff_apply] using h.val.property.2 (2*(n : ℤ))
  have hv (j : ℤ) : hillOriginalRawSourceCLM h j = h.val.val.val j := by
    change SpectralWeight.one.toCoeff h.val.val j = h.val.val.val j
    exact SpectralWeight.toCoeff_apply _ _ _
  simp only [hv] at hi
  change RCLike.re (inner ℂ (hillOriginalMeanZeroDerivativeAtZero h ((n : ℕ)-1)) (Real.sqrt 2 : ℂ)) =
    RCLike.re (inner ℂ (h.val.val.val (2*(n : ℤ))) (1 : ℂ)+
      inner ℂ (h.val.val.val (-(2*(n : ℤ)))) (conj (1 : ℂ))) at hi
  rw [hr,hn] at hi
  simp only [RCLike.inner_apply',map_one,mul_one,Complex.conj_conj,map_add] at hi
  change (conj (hillOriginalMeanZeroDerivativeAtZero h k)*(Real.sqrt 2 : ℂ)).re =
    (conj (h.val.val.val (2*(n : ℤ)))).re+(h.val.val.val (2*(n : ℤ))).re at hi
  simp only [mul_re,ofReal_re,ofReal_im,conj_re,mul_zero,sub_zero] at hi
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hp : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  change (hillOriginalMeanZeroDerivativeAtZero h k).re = Real.sqrt 2*(h.val.val.val (2*(n : ℤ))).re
  apply (mul_right_inj' hp.ne').mp
  calc
    _ = 2*(h.val.val.val (2*(n : ℤ))).re := by linarith [hi]
    _ = (Real.sqrt 2*(h.val.val.val (2*(n : ℤ))).re)*Real.sqrt 2 := by
      calc
        _ = (Real.sqrt 2 ^ 2)*(h.val.val.val (2*(n : ℤ))).re := by rw [hs]
        _ = _ := by ring
    _ = _ := by ring

include h0q h0r in
/-- The complete Fourier formula for the ACTUAL derivative of the literal
original mean-zero spectral sequence. Its frequency, sign and sqrt(2)
normalization are proved on EVERY original real mean-zero direction. -/
theorem hillOriginalMeanZeroDerivativeAtZero_fourier (k : ℕ) (h : hillRealMeanZeroSourceSubmodule) :
    hillOriginalMeanZeroDerivativeAtZero h k =
      (Real.sqrt 2 : ℂ)*h.val.val.val (2*((k+1 : ℕ) : ℤ)) := by
  apply Complex.ext
  · simpa only [mul_re,ofReal_re,ofReal_im,zero_mul,sub_zero] using
      hillOriginalMeanZeroDerivativeAtZero_re h0q h0r k h
  · simpa only [mul_im,ofReal_re,ofReal_im,zero_mul,add_zero] using
      hillOriginalMeanZeroDerivativeAtZero_im h0q h0r k h

end NLS.KdV
