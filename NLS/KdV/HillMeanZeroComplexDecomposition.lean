import NLS.KdV.HillOriginalMeanZeroSpectralDerivative
import NLS.KdV.HillRealSourceDecomposition

noncomputable section
set_option autoImplicit false
open Set Complex
open scoped ComplexConjugate
namespace NLS.KdV

/-- Every ORIGINAL even complex mean-zero direction is the complexification
of two directions in the SAME original real mean-zero Banach domain. -/
theorem exists_hillMeanZeroReal_complex_decomposition
    (h : WeightedCoeff SpectralWeight.one.toWeight 2)
    (heven : SpectralWeight.one.toCoeff h ∈ Coeff.paritySubspace 0)
    (hzero : h.val 0 = 0) :
    ∃ a b : hillRealMeanZeroSourceSubmodule, h = a.val.val+I • b.val.val := by
  obtain ⟨a,b,hae,har,hbe,hbr,hab⟩ := exists_hillRealPeriodOne_complex_decomposition h heven
  have haim : (a.val 0).im = 0 := by
    have hh := congrArg Complex.im (har 0)
    simp only [SpectralWeight.toCoeff_apply,neg_zero,conj_im] at hh
    linarith
  have hbim : (b.val 0).im = 0 := by
    have hh := congrArg Complex.im (hbr 0)
    simp only [SpectralWeight.toCoeff_apply,neg_zero,conj_im] at hh
    linarith
  have hz := congrArg (fun x : WeightedCoeff SpectralWeight.one.toWeight 2 => x.val 0) hab
  rw [hzero] at hz
  change (0 : ℂ) = a.val 0+I*b.val 0 at hz
  have hre := congrArg Complex.re hz
  have him := congrArg Complex.im hz
  simp only [add_re,mul_re,I_re,I_im,zero_mul,one_mul,zero_re] at hre
  simp only [add_im,mul_im,I_re,I_im,zero_mul,one_mul,zero_im] at him
  have ha0 : a.val 0 = 0 := by apply Complex.ext <;> simp only [zero_re,zero_im] <;> linarith
  have hb0 : b.val 0 = 0 := by apply Complex.ext <;> simp only [zero_re,zero_im] <;> linarith
  exact ⟨⟨⟨a,hae,har⟩,(mem_hillRealMeanZeroSourceSubmodule _).mpr ha0⟩,
    ⟨⟨b,hbe,hbr⟩,(mem_hillRealMeanZeroSourceSubmodule _).mpr hb0⟩,hab⟩

end NLS.KdV
