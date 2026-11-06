import NLS.Articles.KdVKdV2Frequencies.OriginalComplexMeanZeroBirkhoffMap
import NLS.Articles.KdVKdV2Frequencies.GlobalKdVHierarchyActionFactors

/-! # Exact native differential and inverse identifications for one original map -/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.KdV
namespace NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData

/-- Any native restriction identified with the same mean-zero map has
exactly the printed Fourier differential in its native norms. -/
theorem originalMeanZeroMap_native_fourier_differential
    (D : GlobalRoughAbelianForwardData) (s : ℝ) (hs : -1 ≤ s)
    (e : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev s) ≃ₜ
      physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (s+1/2)))
    (hea : AnalyticOnNhd ℝ (fun q => e q) univ)
    (hrec : ∀ q, D.originalMeanZeroMap (physicalRealMeanZeroSobolevToComplex hs q) =
      physicalRealMeanZeroSobolevToComplex (by linarith : (-1/2 : ℝ) ≤ s+1/2) (e q))
    (h : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev s)) (j : ℤ) :
    (((fderiv ℝ (fun q => e q) 0) h).val).val j =
      (Real.sqrt (2*(j.natAbs : ℝ)*Real.pi) : ℂ)⁻¹*h.val.val j := by
  let J := physicalRealMeanZeroSobolevToComplex hs
  let L := ((WeightedCoeff.evalCLM (Weight.sobolev (s+1/2)) 2 j).restrictScalars ℝ).comp
    (physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (s+1/2))).subtypeL
  let C := ((WeightedCoeff.evalCLM (Weight.sobolev (-1/2)) 2 j).comp
    (complexMeanZeroWeightedSubmodule (Weight.sobolev (-1/2))).subtypeL).restrictScalars ℝ
  have heq : (fun q => L (e q)) = fun q => C (D.originalMeanZeroMap (J q)) := by
    funext q
    rw [hrec q]
    simp [L,C,physicalRealMeanZeroSobolevToComplex_val,WeightedCoeff.sobolevInclusion_apply]
  have hzero : (0 : OriginalComplexBirkhoffSource) ∈ D.originalMeanZeroDomain :=
    D.real_meanZero_mem_canonicalDomain 0 (by intro k; simp) (by rfl)
  have hPhi := (D.originalMeanZeroMap_analytic 0 hzero).differentiableAt.hasFDerivAt.restrictScalars ℝ
  have hPhiJ : HasFDerivAt D.originalMeanZeroMap ((fderiv ℂ D.originalMeanZeroMap 0).restrictScalars ℝ) (J 0) := by
    simpa only [map_zero] using! hPhi
  have hdL := L.hasFDerivAt.comp 0 ((hea 0 (mem_univ _)).differentiableAt.hasFDerivAt)
  have hdR := C.hasFDerivAt.comp 0 (hPhiJ.comp 0 J.hasFDerivAt)
  have hd : L.comp (fderiv ℝ (fun q => e q) 0) =
      C.comp (((fderiv ℂ D.originalMeanZeroMap 0).restrictScalars ℝ).comp J) := by
    apply hdL.unique
    simpa only [Function.comp_def,heq] using! hdR
  have hh := congrArg (fun K => K h) hd
  have hFourier := D.originalMeanZeroMap_fourier_differential (J h) j
  apply hh.trans
  simpa only [C,J,ContinuousLinearMap.comp_apply,
    physicalRealMeanZeroSobolevToComplex_val,WeightedCoeff.sobolevInclusion_apply] using! hFourier

/-- Any integer native inverse of this same map equals the fixed weak
inverse with its proved sharp native regularity. -/
theorem originalMeanZeroMap_native_inverse_eq
    (D : GlobalRoughAbelianForwardData) (m : ℕ)
    (e : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (m : ℝ)) ≃ₜ
      physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((m : ℝ)+1/2)))
    (hmem : ∀ q, physicalRealMeanZeroSobolevToComplex
      (by have := Nat.cast_nonneg (α := ℝ) m; linarith : (-1 : ℝ) ≤ m) q ∈ D.originalMeanZeroDomain)
    (hrec : ∀ q, D.originalMeanZeroMap (physicalRealMeanZeroSobolevToComplex
      (by have := Nat.cast_nonneg (α := ℝ) m; linarith : (-1 : ℝ) ≤ m) q) =
        physicalRealMeanZeroSobolevToComplex
          (by have := Nat.cast_nonneg (α := ℝ) m; linarith : (-1/2 : ℝ) ≤ (m : ℝ)+1/2) (e q))
    (z : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((m : ℝ)+1/2))) :
    D.rawIntegerInverseSource m z = (e.symm z).val := by
  apply D.rawIntegerInverseSource_eq_of_signed_eq m _ (e.symm z).property.1 (e.symm z).property.2
  have he := congrArg Subtype.val (hrec (e.symm z))
  rw [D.originalMeanZeroMap_val _ (hmem _),e.apply_symm_apply] at he
  exact he

/-- Consequently the hierarchy factors recover the physical Hamiltonian
composed with ANY native inverse of the SAME original mean-zero map. -/
theorem exists_originalMeanZeroMap_native_hierarchy_action_factor
    (D : GlobalRoughAbelianForwardData) (m : ℕ)
    (e : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (m : ℝ)) ≃ₜ
      physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((m : ℝ)+1/2)))
    (hmem : ∀ q, physicalRealMeanZeroSobolevToComplex
      (by have := Nat.cast_nonneg (α := ℝ) m; linarith : (-1 : ℝ) ≤ m) q ∈ D.originalMeanZeroDomain)
    (hrec : ∀ q, D.originalMeanZeroMap (physicalRealMeanZeroSobolevToComplex
      (by have := Nat.cast_nonneg (α := ℝ) m; linarith : (-1 : ℝ) ≤ m) q) =
        physicalRealMeanZeroSobolevToComplex
          (by have := Nat.cast_nonneg (α := ℝ) m; linarith : (-1/2 : ℝ) ≤ (m : ℝ)+1/2) (e q)) :
    ∃ U : Set (WeightedCoeff (Weight.sobolev (2*(m : ℝ)+1)) 1),
      ∃ g : WeightedCoeff (Weight.sobolev (2*(m : ℝ)+1)) 1 → ℂ,
      IsOpen U ∧ WeightedCoeff.nonnegativeLocus (Weight.sobolev (2*(m : ℝ)+1)) 1 ⊆ U ∧
      AnalyticOnNhd ℂ g U ∧
      (∀ z, g (hierarchyNativeActionSequence m z) = nativeHillHierarchyHamiltonian m (e.symm z).val) ∧
      ∀ I : WeightedCoeff (Weight.sobolev (2*(m : ℝ)+1)) 1,
        I ∈ WeightedCoeff.nonnegativeLocus (Weight.sobolev (2*(m : ℝ)+1)) 1 →
        (∀ n : ℤ, n ≤ 0 → I.val n = 0) → (g I).im = 0 := by
  obtain ⟨U,g,hU,hpos,hg,hrecover,hreal⟩ := D.exists_originalKdVHierarchy_real_analytic_action_factor m
  refine ⟨U,g,hU,hpos,hg,?_,hreal⟩
  intro z
  rw [hrecover z,D.birkhoffHillHierarchyHamiltonian_complex_value,
    D.originalMeanZeroMap_native_inverse_eq m e hmem hrec z]

end NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
