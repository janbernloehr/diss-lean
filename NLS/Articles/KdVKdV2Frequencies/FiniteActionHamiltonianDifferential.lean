import NLS.Articles.KdVKdV2Frequencies.OriginalHierarchyActionFrequencies
import NLS.SequenceSpaces.SobolevSignedFiniteActionDifferential

/-! # The actual native Hamiltonian differential at finite-action sources

At a target with finitely many open actions, every native variation of the
independently defined physical Hamiltonian is an exact finite sum of its
intrinsic frequencies times the actual action differentials.
-/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.KdV
open scoped ENNReal ComplexConjugate
namespace NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData

/-- Full complex value of the physical H_m through the SAME native inverse. -/
def complexBirkhoffHierarchyHamiltonian (D : GlobalRoughAbelianForwardData) (m : ℕ)
    (z : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((m : ℝ)+1/2))) : ℂ :=
  nativeHillHierarchyHamiltonian m (D.rawIntegerInverseSource m z)

theorem complexBirkhoffHierarchyHamiltonian_eq_real (D : GlobalRoughAbelianForwardData) (m : ℕ)
    (z : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((m : ℝ)+1/2))) :
    D.complexBirkhoffHierarchyHamiltonian m z = (D.birkhoffHillHierarchyHamiltonian m z : ℂ) :=
  (D.birkhoffHillHierarchyHamiltonian_complex_value m z).symm

/-- The actual physical pullback has the full Banach chain-rule differential
through ANY genuine analytic factor, on the ENTIRE native target domain. -/
theorem hasFDerivAt_complexBirkhoffHierarchyHamiltonian_actions
    (D : GlobalRoughAbelianForwardData) (m : ℕ) (r : ℝ) (hrs : r=2*((m : ℝ)+1/2))
    (F : OriginalHierarchyActionFactor D m r hrs)
    (z : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((m : ℝ)+1/2))) :
    HasFDerivAt (D.complexBirkhoffHierarchyHamiltonian m)
      (((fderiv ℂ F.value (sobolevSignedActionSequence r ((m : ℝ)+1/2) hrs z)).restrictScalars ℝ).comp
        (sobolevRealSignedActionJacobian r ((m : ℝ)+1/2) hrs z)) z := by
  have hF := (F.analytic _ (F.nonnegative_subset_domain
    (originalPositiveActions m r hrs z).property.1)).differentiableAt.hasFDerivAt.restrictScalars ℝ
  have hd := hF.comp z (hasFDerivAt_sobolevSignedActionSequence r ((m : ℝ)+1/2) hrs z)
  have he : F.value ∘ sobolevSignedActionSequence r ((m : ℝ)+1/2) hrs =
      D.complexBirkhoffHierarchyHamiltonian m := funext F.target_recovery
  rw [he] at hd
  exact hd

/-- Finitely many actual open actions give an exact finite frequency
expansion of EVERY physical native Frechet variation, including directions
opening previously closed gaps. -/
theorem fderiv_complexBirkhoffHierarchyHamiltonian_finite_actions
    (D : GlobalRoughAbelianForwardData) (m : ℕ) (r : ℝ) (hrs : r=2*((m : ℝ)+1/2))
    (z : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((m : ℝ)+1/2))) (S : Finset ℕ+)
    (hz : ∀ n : ℕ+, n ∉ S → (sobolevSignedActionSequence r ((m : ℝ)+1/2) hrs z).val (n : ℤ) = 0)
    (h : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((m : ℝ)+1/2))) :
    (fderiv ℝ (D.complexBirkhoffHierarchyHamiltonian m) z) h = ∑ n ∈ S,
      (z.val.val n*h.val.val (-n)+h.val.val n*z.val.val (-n))*
        (D.originalHierarchyFrequency m r hrs (originalPositiveActions m r hrs z) n : ℂ) := by
  obtain ⟨F⟩ := nonempty_originalHierarchyActionFactor D m r hrs
  have hd := D.hasFDerivAt_complexBirkhoffHierarchyHamiltonian_actions m r hrs F z
  have he : (fderiv ℝ (D.complexBirkhoffHierarchyHamiltonian m) z) h =
      (fderiv ℂ F.value (sobolevSignedActionSequence r ((m : ℝ)+1/2) hrs z))
        (sobolevRealSignedActionJacobian r ((m : ℝ)+1/2) hrs z h) := by
    simpa only [ContinuousLinearMap.comp_apply] using!
      congrArg (fun L => L h) hd.fderiv
  rw [he,sobolevRealSignedActionJacobian_finite_sum_of_actions r ((m : ℝ)+1/2) hrs z S hz h,map_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [map_smul,smul_eq_mul]
  congr 1
  exact (D.originalHierarchyFrequency_eq_factor_derivative m r hrs F (originalPositiveActions m r hrs z) n).symm

/-- The real physical native Hamiltonian differential retains the exact
original signed-mode normalization, with no infinite gradient sum. -/
theorem fderiv_birkhoffHierarchyHamiltonian_finite_actions
    (D : GlobalRoughAbelianForwardData) (m : ℕ) (r : ℝ) (hrs : r=2*((m : ℝ)+1/2))
    (z : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((m : ℝ)+1/2))) (S : Finset ℕ+)
    (hz : ∀ n : ℕ+, n ∉ S → (sobolevSignedActionSequence r ((m : ℝ)+1/2) hrs z).val (n : ℤ) = 0)
    (h : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((m : ℝ)+1/2))) :
    (fderiv ℝ (D.birkhoffHillHierarchyHamiltonian m) z) h = ∑ n ∈ S,
      2*(z.val.val n*conj (h.val.val n)).re*
        D.originalHierarchyFrequency m r hrs (originalPositiveActions m r hrs z) n := by
  obtain ⟨F⟩ := nonempty_originalHierarchyActionFactor D m r hrs
  have hdC := D.hasFDerivAt_complexBirkhoffHierarchyHamiltonian_actions m r hrs F z
  have hdR := Complex.reCLM.hasFDerivAt.comp z hdC
  have hdR' : HasFDerivAt (D.birkhoffHillHierarchyHamiltonian m)
      (Complex.reCLM.comp (((fderiv ℂ F.value (sobolevSignedActionSequence r ((m : ℝ)+1/2) hrs z)).restrictScalars ℝ).comp
        (sobolevRealSignedActionJacobian r ((m : ℝ)+1/2) hrs z))) z := by
    simpa only [Function.comp_def,birkhoffHillHierarchyHamiltonian,complexBirkhoffHierarchyHamiltonian] using! hdR
  have he : (fderiv ℝ (D.birkhoffHillHierarchyHamiltonian m) z) h =
      ((fderiv ℝ (D.complexBirkhoffHierarchyHamiltonian m) z) h).re := by
    rw [hdC.fderiv]
    simpa only [ContinuousLinearMap.comp_apply] using! congrArg (fun L => L h) hdR'.fderiv
  rw [he,D.fderiv_complexBirkhoffHierarchyHamiltonian_finite_actions m r hrs z S hz h]
  change Complex.reCLM (∑ n ∈ S, _ ) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro n _
  change ((_ : ℂ)*(D.originalHierarchyFrequency m r hrs (originalPositiveActions m r hrs z) n : ℂ)).re = _
  rw [Complex.mul_re]
  simp only [Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
  congr 1
  rw [h.property.1 (n : ℤ),z.property.1 (n : ℤ)]
  simp only [Complex.add_re,Complex.mul_re,Complex.conj_re,Complex.conj_im]
  ring

/-- At the origin the ACTUAL native Hamiltonian differential vanishes. -/
theorem fderiv_birkhoffHierarchyHamiltonian_zero (D : GlobalRoughAbelianForwardData) (m : ℕ) :
    fderiv ℝ (D.birkhoffHillHierarchyHamiltonian m) 0 = 0 := by
  ext h
  have he := D.fderiv_birkhoffHierarchyHamiltonian_finite_actions m (2*(m : ℝ)+1) (by ring)
    0 ∅ (by intro n _; rw [sobolevSignedActionSequence_apply]; simp) h
  simpa only [Finset.sum_empty,zero_apply] using he

end NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
