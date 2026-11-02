import NLS.MKdV.MiuraHillGapComplement
import NLS.ZakharovShabat.SourceCanonicalRootRealBand

/-! # The canonical physical Hill sheets on their full real H¹ gap complement

The independent nonreal-energy construction extends analytically across
every real band. Its physical trace, exact energy derivative and canonical
first-band sign hold throughout the original labeled Hill domain.
-/
noncomputable section
open Set Complex Filter Topology NLS.ComplexAnalysis NLS.KdV NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

theorem miuraHillContinuation_nonreal (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) (μ : ℂ) (hi : μ.im ≠ 0) :
    (μ,periodOneMiuraCurve a) ∈ miuraHillContinuationDomain := by
  have hs : (Complex.sqrt μ)^2 ∈ slitPlane := by
    rw [complex_sqrt_sq]
    exact mem_slitPlane_iff.mpr (Or.inr hi)
  have h := mem_miuraHillContinuationDomain_of_real (periodOneMiuraCurve a)
    (periodOneMiuraCurve_real a ha) (Complex.sqrt μ) hs (sqrt_re_pos_of_im_ne_zero μ hi).2
  simpa only [complex_sqrt_sq] using h

theorem analyticOnNhd_canonicalMiuraHillSheets (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) :
    AnalyticOnNhd ℂ (canonicalMiuraHillRoot a) (miuraHillGapComplement a ha) ∧
      AnalyticOnNhd ℂ (canonicalMiuraHillPrimitive a) (miuraHillGapComplement a ha) := by
  have h (μ : ℂ) (hμ : μ ∈ miuraHillGapComplement a ha) :=
    analyticAt_canonicalMiuraHillSheets a ha μ (miuraHillGapComplement_sqrt a ha μ hμ).1
      (miuraHillGapComplement_sqrt a ha μ hμ).2.2
  exact ⟨fun μ hμ => (h μ hμ).1,fun μ hμ => (h μ hμ).2⟩

theorem canonicalMiuraHillSheets_physical_trace (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) (μ : ℂ) (hμ : μ ∈ miuraHillGapComplement a ha) :
    2*cosh (canonicalMiuraHillPrimitive a μ) = hillL2Discriminant (sobolevMiuraHillPotential a) μ ∧
      2*sinh (canonicalMiuraHillPrimitive a μ) = canonicalMiuraHillRoot a μ := by
  have h := analyticOnNhd_canonicalMiuraHillSheets a ha
  have hF := (h.2 μ hμ).continuousAt
  have hR := (h.1 μ hμ).continuousAt
  have hD := (analyticOnNhd_hillL2Discriminant (sobolevMiuraHillPotential a) μ (mem_univ _)).continuousAt
  have he (w : ℂ) (hi : w.im ≠ 0) :
      2*cosh (canonicalMiuraHillPrimitive a w) = hillL2Discriminant (sobolevMiuraHillPotential a) w ∧
        2*sinh (canonicalMiuraHillPrimitive a w) = canonicalMiuraHillRoot a w := by
    have ht := miuraHillContinuation_nonreal a ha w hi
    rw [canonicalMiuraHillPrimitive_eq_original a w ht,canonicalMiuraHillRoot_eq_original a w ht,
      hillL2Discriminant_miura]
    exact miuraHillPrimitive_trace _ ht
  constructor
  · have hc : ContinuousAt (fun w => 2*cosh (canonicalMiuraHillPrimitive a w)) μ :=
      continuousAt_const.mul (continuous_cosh.continuousAt.comp hF)
    exact (nonrealBoundaryExtension_eq_self hc).symm.trans
      (nonrealBoundaryExtension_eq_of_continuousAt hD (fun w hi => (he w hi).1))
  · have hc : ContinuousAt (fun w => 2*sinh (canonicalMiuraHillPrimitive a w)) μ :=
      continuousAt_const.mul (continuous_sinh.continuousAt.comp hF)
    exact (nonrealBoundaryExtension_eq_self hc).symm.trans
      (nonrealBoundaryExtension_eq_of_continuousAt hR (fun w hi => (he w hi).2))

theorem canonicalMiuraHillRoot_sq (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) (μ : ℂ) (hμ : μ ∈ miuraHillGapComplement a ha) :
    (canonicalMiuraHillRoot a μ)^2 = hillL2Radicand (sobolevMiuraHillPotential a) μ := by
  have hs := miuraHillGapComplement_sqrt a ha μ hμ
  have he := (canonicalMiuraHillSheets_eq_NLS a ha (Complex.sqrt μ) hs.2.1 hs.2.2).1
  simp only [complex_sqrt_sq] at he
  rw [he,sourceCanonicalRoot_sq_eq_discriminant_sq_sub_four _ _ _ _ hs.2.2]
  change canonicalDiscriminant (by simp) (periodOnePotential (sobolevSourceInclusion (a,a)))
    (Complex.sqrt μ)^2-4 = _
  rw [← hillL2Discriminant_miura_eq_canonical a (Complex.sqrt μ),complex_sqrt_sq]
  rfl

theorem canonicalMiuraHillRoot_ne_zero (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) (μ : ℂ) (hμ : μ ∈ miuraHillGapComplement a ha) :
    canonicalMiuraHillRoot a μ ≠ 0 := by
  have hs := miuraHillGapComplement_sqrt a ha μ hμ
  have he := (canonicalMiuraHillSheets_eq_NLS a ha (Complex.sqrt μ) hs.2.1 hs.2.2).1
  simp only [complex_sqrt_sq] at he
  rw [he]
  exact sourceCanonicalRoot_ne_zero_off_gaps _ _ _ _ hs.2.2

theorem hasDerivAt_canonicalMiuraHillPrimitive (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) (μ : ℂ) (hμ : μ ∈ miuraHillGapComplement a ha) :
    HasDerivAt (canonicalMiuraHillPrimitive a)
      (deriv (hillL2Discriminant (sobolevMiuraHillPotential a)) μ / canonicalMiuraHillRoot a μ) μ := by
  have hf := ((analyticOnNhd_canonicalMiuraHillSheets a ha).2 μ hμ).differentiableAt.hasDerivAt
  have he : (hillL2Discriminant (sobolevMiuraHillPotential a)) =ᶠ[𝓝 μ]
      (fun w => 2*cosh (canonicalMiuraHillPrimitive a w)) := by
    filter_upwards [(isOpen_miuraHillGapComplement a ha).mem_nhds hμ] with w hw
    exact (canonicalMiuraHillSheets_physical_trace a ha w hw).1.symm
  have hd := ((hf.ccosh).const_mul 2).congr_of_eventuallyEq he
  have hD := (analyticOnNhd_hillL2Discriminant (sobolevMiuraHillPotential a) μ
    (mem_univ _)).differentiableAt.hasDerivAt
  have heq := hd.unique hD
  rw [← mul_assoc,(canonicalMiuraHillSheets_physical_trace a ha μ hμ).2] at heq
  apply hf.congr_deriv
  apply (eq_div_iff (canonicalMiuraHillRoot_ne_zero a ha μ hμ)).mpr
  simpa only [mul_comm] using heq

/-- The source's first-band branch condition, with positive real
value after multiplication by i, on every full real H¹ profile. -/
theorem canonicalMiuraHillRoot_firstBand_sign (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) (x : ℝ)
    (hx : x ∈ Ioo (miuraNLSRight a 0).re (miuraNLSLeft a 1).re) :
    (I*canonicalMiuraHillRoot a ((x : ℂ)^2)).im = 0 ∧
      0 < (I*canonicalMiuraHillRoot a ((x : ℂ)^2)).re := by
  have hp : 0 < x := (miuraNLSRight_zero_nonnegative a).trans_lt hx.1
  have hband : x ∈ sourceRealBand (by simp) (by norm_num) (realDiagonalH1Source a ha).val 0 := hx
  have hz := sourceRealBand_subset_rootDomain _ _ _ (realDiagonalH1Source a ha).property 0 x hband
  rw [(canonicalMiuraHillSheets_eq_NLS a ha x hp hz).1]
  have hs := sourceCanonicalRoot_realBand_sign (by simp) (by norm_num)
    (realDiagonalH1Source a ha).val (realDiagonalH1Source a ha).property 0 x hband
  simp only [Int.natAbs_zero,pow_zero,one_mul] at hs
  simp only [mul_im,mul_re,I_re,I_im,zero_mul,one_mul,zero_add,zero_sub]
  exact ⟨hs.1,neg_pos.mpr hs.2⟩

end NLS.MKdV
