import NLS.KdV.HillFreeCartesianDifference
import NLS.KdV.HillHminusPhysicalConjugateDerivative
import NLS.KdV.HillOriginalMeanZeroSpectralDerivative

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ComplexConjugate
namespace NLS.KdV

variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

/-- The ORIGINAL Cartesian imaginary differential at zero is the literal
positive raw Fourier imaginary component, with its exact physical prefactor. -/
theorem hillOriginalCartesian_free_im_fderiv_real (n : ℕ+)
    (Z W : PeriodOneHminusOne → ℂ) (hZ : AnalyticAt ℂ Z 0) (hW : AnalyticAt ℂ W 0)
    (hZM : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨0,h0q,h0r⟩ : RealPeriodOneHillPotential),
      Z (hillOriginalHminusSource p.val) = hillSpectralCartesian p.val p.property.1 p.property.2 n n.pos)
    (hWM : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨0,h0q,h0r⟩ : RealPeriodOneHillPotential),
      W (hillOriginalHminusSource p.val) = conj (hillSpectralCartesian p.val p.property.1 p.property.2 n n.pos))
    (h : hillRealSourceSubmodule) :
    ((fderiv ℂ Z 0) (hillOriginalRealHminusInclusion h)).im =
      (hillActionGapPrefactor 0 h0q h0r n).re*(h.val.val (2*(n : ℤ))).im := by
  have hc := hillHminusPhysicalGerm_fderiv_conj_real_source (0 : hillRealSourceSubmodule) Z W
    (by simpa using hZ) (by simpa using hW)
    (by filter_upwards [hZM,hWM] with p hpZ hpW; exact hpW.trans (congrArg conj hpZ).symm) h
  have hc0 : (fderiv ℂ W 0) (hillOriginalRealHminusInclusion h) =
      conj ((fderiv ℂ Z 0) (hillOriginalRealHminusInclusion h)) := by simpa using hc
  have hd := hillOriginalCartesian_free_difference_fderiv h0q h0r n Z W hZ hW hZM hWM
    (hillOriginalRealHminusInclusion h)
  have hr : h.val.val (-(2*(n : ℤ))) = conj (h.val.val (2*(n : ℤ))) := by
    simpa only [SpectralWeight.toCoeff_apply] using h.property.2 (2*(n : ℤ))
  change (fderiv ℂ Z 0) (hillOriginalRealHminusInclusion h) -
      (fderiv ℂ W 0) (hillOriginalRealHminusInclusion h) =
      hillActionGapPrefactor 0 h0q h0r n *
        ((hillOriginalHminusSource h.val).val n-(hillOriginalHminusSource h.val).val (-(n : ℤ))) at hd
  rw [hc0,hillOriginalHminusSource_apply,hillOriginalHminusSource_apply,
    show 2*(-(n : ℤ)) = -(2*(n : ℤ)) by ring,hr] at hd
  have hi := congrArg Complex.im hd
  simp only [sub_im,conj_im,mul_im,sub_re,conj_re,sub_self,mul_zero,add_zero] at hi
  linarith

include h0q h0r in
/-- Every imaginary coordinate of the ACTUAL full original base sequence
derivative at zero is sqrt(2) times the original positive Fourier component. -/
theorem hillOriginalRealSpectralMap_free_im_fderiv (k : ℕ) (h : hillRealSourceSubmodule) :
    ((fderiv ℝ hillOriginalRealSpectralMap 0 h) k).im =
      Real.sqrt 2*(h.val.val (2*((k+1 : ℕ) : ℤ))).im := by
  let n : ℕ+ := ⟨k+1,by omega⟩
  obtain ⟨Z,W,hZ,hW,_,_,hM,_⟩ := exists_hillFree_cartesian_pair_difference h0q h0r n
  have hZM := hM.mono (fun _ hp => hp.1)
  have hWM := hM.mono (fun _ hp => hp.2)
  have hQ0 : (⟨(0 : hillRealSourceSubmodule).val,(0 : hillRealSourceSubmodule).property⟩ : RealPeriodOneHillPotential) =
      (⟨0,h0q,h0r⟩ : RealPeriodOneHillPotential) := by
    apply Subtype.ext
    rfl
  have hZM0 : ∀ᶠ p : RealPeriodOneHillPotential in
      𝓝 (⟨(0 : hillRealSourceSubmodule).val,(0 : hillRealSourceSubmodule).property⟩ : RealPeriodOneHillPotential),
      Z (hillOriginalHminusSource p.val) = hillSignedSpectralCartesian true ⟨k+1,by omega⟩ p := by
    rw [hQ0]
    simpa only [hillSignedSpectralCartesian,ite_true,n] using hZM
  have hs := hillOriginalRealSpectralMap_coordinate_fderiv (0 : hillRealSourceSubmodule) k Z
    (by simpa using hZ) hZM0
  have he := congrArg (fun L : hillRealSourceSubmodule →L[ℝ] ℂ => L h) hs
  have he0 : (fderiv ℝ hillOriginalRealSpectralMap 0 h) k =
      (Real.sqrt (2*Real.pi*(k+1 : ℕ)) : ℂ)*((fderiv ℂ Z 0) (hillOriginalRealHminusInclusion h)) := by
    calc
      _ = (lp.evalCLM (𝕜 := ℂ) (fun _ : ℕ => ℂ) 2 k) ((fderiv ℝ hillOriginalRealSpectralMap 0) h) := rfl
      _ = _ := by simpa using he
  have hi := congrArg Complex.im he0
  simp only [mul_im,ofReal_re,ofReal_im,zero_mul,add_zero] at hi
  rw [hillOriginalCartesian_free_im_fderiv_real h0q h0r n Z W hZ hW hZM hWM h] at hi
  have hc := congrArg Complex.re (hillActionGapPrefactor_free_base_normalization h0q h0r n n.pos)
  simp only [mul_re,ofReal_re,ofReal_im,zero_mul,sub_zero] at hc
  change Real.sqrt (2*Real.pi*(k+1 : ℕ))*(hillActionGapPrefactor 0 h0q h0r n).re = Real.sqrt 2 at hc
  rw [←mul_assoc,hc] at hi
  exact hi

/-- The actual mean-zero derivative is the restriction of the actual
original real derivative, without any replacement of source or map. -/
theorem hillOriginalMeanZeroDerivativeAtZero_eq_restriction :
    hillOriginalMeanZeroDerivativeAtZero =
      (fderiv ℝ hillOriginalRealSpectralMap 0).comp hillRealMeanZeroSourceSubmodule.subtypeL := by
  let L := hillRealMeanZeroSourceSubmodule.subtypeL
  have hd := ((hasFDerivAt_hillOriginalRealSpectralMap (L 0)).comp 0 L.hasFDerivAt).fderiv
  have he : hillOriginalRealSpectralMap ∘ L = hillOriginalMeanZeroRealSpectralMap := rfl
  rw [he] at hd
  simpa only [map_zero,hillOriginalMeanZeroDerivativeAtZero,L] using hd


include h0q h0r in
/-- The precise imaginary Fourier component of the ACTUAL original
mean-zero sequence derivative, on every original real mean-zero direction. -/
theorem hillOriginalMeanZeroDerivativeAtZero_im (k : ℕ) (h : hillRealMeanZeroSourceSubmodule) :
    (hillOriginalMeanZeroDerivativeAtZero h k).im =
      Real.sqrt 2*(h.val.val.val (2*((k+1 : ℕ) : ℤ))).im := by
  rw [hillOriginalMeanZeroDerivativeAtZero_eq_restriction]
  exact hillOriginalRealSpectralMap_free_im_fderiv h0q h0r k h.val

end NLS.KdV
