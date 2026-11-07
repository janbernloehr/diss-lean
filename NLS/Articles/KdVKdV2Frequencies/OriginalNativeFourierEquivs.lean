import NLS.Articles.KdVKdV2Frequencies.OriginalNativeBirkhoffIdentifications
import NLS.ComplexAnalysis.AnalyticHomeomorphDerivativeEquiv

/-! Actual native original Birkhoff homeomorphisms and their TRUE
canonical Fourier derivative equivalences, retaining original raw norms. -/
noncomputable section
open Set Complex NLS.KdV NLS.ComplexAnalysis
namespace NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData

def originalNativeBirkhoff (D : GlobalRoughAbelianForwardData) (s : ℝ) (hs : -1≤s) :
    physicalRealMeanZeroWeightedSubmodule (Weight.sobolev s) ≃ₜ
      physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (s+1/2)) :=
  Classical.choose (D.exists_originalMeanZeroMap_native_diffeomorphism s hs)

theorem originalNativeBirkhoff_analytic (D : GlobalRoughAbelianForwardData) (s : ℝ) (hs : -1≤s) :
    AnalyticOnNhd ℝ (fun q => D.originalNativeBirkhoff s hs q) univ :=
  (Classical.choose_spec (D.exists_originalMeanZeroMap_native_diffeomorphism s hs)).1

theorem originalNativeBirkhoff_symm_analytic (D : GlobalRoughAbelianForwardData) (s : ℝ) (hs : -1≤s) :
    AnalyticOnNhd ℝ (fun z => (D.originalNativeBirkhoff s hs).symm z) univ :=
  (Classical.choose_spec (D.exists_originalMeanZeroMap_native_diffeomorphism s hs)).2.1

theorem originalNativeBirkhoff_mem_domain (D : GlobalRoughAbelianForwardData) (s : ℝ) (hs : -1≤s)
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev s)) :
    physicalRealMeanZeroSobolevToComplex hs q∈D.originalMeanZeroDomain :=
  (Classical.choose_spec (D.exists_originalMeanZeroMap_native_diffeomorphism s hs)).2.2.1 q

theorem originalNativeBirkhoff_restriction (D : GlobalRoughAbelianForwardData) (s : ℝ) (hs : -1≤s)
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev s)) :
    D.originalMeanZeroMap (physicalRealMeanZeroSobolevToComplex hs q)=
      physicalRealMeanZeroSobolevToComplex (by linarith : (-1/2:ℝ)≤s+1/2) (D.originalNativeBirkhoff s hs q) :=
  (Classical.choose_spec (D.exists_originalMeanZeroMap_native_diffeomorphism s hs)).2.2.2 q

theorem originalNativeBirkhoff_zero (D : GlobalRoughAbelianForwardData) (s : ℝ) (hs : -1≤s) :
    D.originalNativeBirkhoff s hs 0=0 := by
  have h := D.originalNativeBirkhoff_restriction s hs 0
  rw [map_zero,D.originalMeanZeroMap_zero] at h
  apply Subtype.ext
  apply Subtype.ext
  funext j
  have hc := congrArg (fun z : OriginalComplexBirkhoffTarget => z.val.val j) h
  simpa only [physicalRealMeanZeroSobolevToComplex_val,WeightedCoeff.sobolevInclusion_apply,Submodule.coe_zero,WeightedCoeff.zero_val]
    using! hc.symm

theorem exists_original_native_fourier_equiv (D : GlobalRoughAbelianForwardData) (s : ℝ) (hs : -1≤s) :
    ∃ L : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev s) ≃L[ℝ]
        physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (s+1/2)),
      (L : _ →L[ℝ] _) = fderiv ℝ (fun q => D.originalNativeBirkhoff s hs q) 0 ∧
      (L.symm : _ →L[ℝ] _) = fderiv ℝ (fun z => (D.originalNativeBirkhoff s hs).symm z) 0 ∧
      ∀ q j,(L q).val.val j=(Real.sqrt (2*(j.natAbs:ℝ)*Real.pi):ℂ)⁻¹*q.val.val j := by
  obtain ⟨L,hL,hLi⟩ := exists_analytic_homeomorph_zero_derivative_equiv (D.originalNativeBirkhoff s hs)
    (D.originalNativeBirkhoff_analytic s hs) (D.originalNativeBirkhoff_symm_analytic s hs) (D.originalNativeBirkhoff_zero s hs)
  refine ⟨L,hL,hLi,?_⟩
  intro q j
  rw [show L q=(fderiv ℝ (fun p => D.originalNativeBirkhoff s hs p) 0) q from congrArg (fun T => T q) hL]
  exact D.originalMeanZeroMap_native_fourier_differential s hs (D.originalNativeBirkhoff s hs)
    (D.originalNativeBirkhoff_analytic s hs) (D.originalNativeBirkhoff_restriction s hs) q j

end NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
