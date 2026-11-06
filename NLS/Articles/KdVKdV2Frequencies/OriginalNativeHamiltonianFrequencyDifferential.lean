import NLS.Articles.KdVKdV2Frequencies.OriginalHierarchyActionFrequencies
import NLS.SequenceSpaces.SobolevSignedActionModeCurve

/-! # Physical native Hamiltonian differentials in the original signed modes

The intrinsic action frequencies are the actual coefficients of the native
Hamiltonian differential through the SAME global inverse. All formulas use
real signed mode variations in their original native norms.
-/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.KdV
open scoped ENNReal ComplexConjugate
namespace NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData

/-- The complex value of the actual physical native H_m has this derivative
in every real signed Birkhoff mode on the entire native target. -/
theorem hasDerivAt_nativeHierarchyHamiltonian_signed_mode
    (D : GlobalRoughAbelianForwardData) (m : ℕ) (r : ℝ) (hrs : r=2*((m : ℝ)+1/2))
    (z : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((m : ℝ)+1/2)))
    (n : ℕ+) (c : ℂ) :
    HasDerivAt (fun t : ℝ => nativeHillHierarchyHamiltonian m (D.rawIntegerInverseSource m
      (z+t • physicalRealMeanZeroWeightedMode (Weight.sobolev ((m : ℝ)+1/2)) n c)))
      ((z.val.val n*conj c+c*z.val.val (-n))*
        (D.originalHierarchyFrequency m r hrs (originalPositiveActions m r hrs z) n : ℂ)) 0 := by
  obtain ⟨F⟩ := nonempty_originalHierarchyActionFactor D m r hrs
  let A := sobolevSignedActionSequence r ((m : ℝ)+1/2) hrs
  let v := physicalRealMeanZeroWeightedMode (Weight.sobolev ((m : ℝ)+1/2)) n c
  have hdA := hasDerivAt_sobolevSignedActionSequence_mode_curve r ((m : ℝ)+1/2) hrs z n c
  have hdF : HasFDerivAt F.value ((fderiv ℂ F.value (A z)).restrictScalars ℝ) (A (z+(0 : ℝ) • v)) := by
    simpa only [zero_smul,add_zero] using!
      (F.analytic (A z) (F.nonnegative_subset_domain (originalPositiveActions m r hrs z).property.1)).differentiableAt.hasFDerivAt.restrictScalars ℝ
  have hd : HasDerivAt (fun t : ℝ => F.value (A (z+t • v)))
      ((fderiv ℂ F.value (A z)) ((z.val.val n*conj c+c*z.val.val (-n)) •
        WeightedCoeff.single (Weight.sobolev r) (n : ℤ) 1)) 0 := by
    simpa only [Function.comp_def] using! hdF.comp_hasDerivAt 0 hdA
  have hfreq : (D.originalHierarchyFrequency m r hrs (originalPositiveActions m r hrs z) n : ℂ) =
      (fderiv ℂ F.value (A z)) (WeightedCoeff.single (Weight.sobolev r) (n : ℤ) 1) := by
    simpa only [A,originalPositiveActions_val] using!
      D.originalHierarchyFrequency_eq_factor_derivative m r hrs F (originalPositiveActions m r hrs z) n
  rw [map_smul,smul_eq_mul,←hfreq] at hd
  have he : (fun t : ℝ => F.value (A (z+t • v))) = fun t : ℝ =>
      nativeHillHierarchyHamiltonian m (D.rawIntegerInverseSource m (z+t • v)) := by
    funext t
    exact F.target_recovery _
  rw [he] at hd
  exact hd

/-- The actual real native Hamiltonian derivative, with both physical
signed coefficients combined and the exact original action normalization. -/
theorem hasDerivAt_birkhoffHierarchyHamiltonian_signed_mode
    (D : GlobalRoughAbelianForwardData) (m : ℕ) (r : ℝ) (hrs : r=2*((m : ℝ)+1/2))
    (z : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((m : ℝ)+1/2)))
    (n : ℕ+) (c : ℂ) :
    HasDerivAt (fun t : ℝ => D.birkhoffHillHierarchyHamiltonian m
      (z+t • physicalRealMeanZeroWeightedMode (Weight.sobolev ((m : ℝ)+1/2)) n c))
      (2*(z.val.val n*conj c).re*
        D.originalHierarchyFrequency m r hrs (originalPositiveActions m r hrs z) n) 0 := by
  have hd := D.hasDerivAt_nativeHierarchyHamiltonian_signed_mode m r hrs z n c
  have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 hd
  have hδ : (z.val.val n*conj c+c*z.val.val (-n)).re = 2*(z.val.val n*conj c).re := by
    rw [z.property.1 (n : ℤ)]
    simp only [Complex.add_re,Complex.mul_re,Complex.conj_re,Complex.conj_im]
    ring
  have hder : ((z.val.val n*conj c+c*z.val.val (-n))*
      (D.originalHierarchyFrequency m r hrs (originalPositiveActions m r hrs z) n : ℂ)).re =
      2*(z.val.val n*conj c).re*
        D.originalHierarchyFrequency m r hrs (originalPositiveActions m r hrs z) n := by
    rw [Complex.mul_re]
    simp only [Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
    rw [hδ]
  have hr' : HasDerivAt (fun t : ℝ => (nativeHillHierarchyHamiltonian m (D.rawIntegerInverseSource m
      (z+t • physicalRealMeanZeroWeightedMode (Weight.sobolev ((m : ℝ)+1/2)) n c))).re)
      (((z.val.val n*conj c+c*z.val.val (-n))*
        (D.originalHierarchyFrequency m r hrs (originalPositiveActions m r hrs z) n : ℂ)).re) 0 := by
    simpa only [Function.comp_def] using! hr
  rw [hder] at hr'
  exact hr'

/-- These frequencies are coefficients of the actual Frechet differential
in the original raw native target norm, rather than only curve derivatives. -/
theorem fderiv_birkhoffHierarchyHamiltonian_signed_mode
    (D : GlobalRoughAbelianForwardData) (m : ℕ) (r : ℝ) (hrs : r=2*((m : ℝ)+1/2))
    (z : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((m : ℝ)+1/2)))
    (n : ℕ+) (c : ℂ) :
    (fderiv ℝ (D.birkhoffHillHierarchyHamiltonian m) z)
      (physicalRealMeanZeroWeightedMode (Weight.sobolev ((m : ℝ)+1/2)) n c) =
      2*(z.val.val n*conj c).re*
        D.originalHierarchyFrequency m r hrs (originalPositiveActions m r hrs z) n := by
  let v := physicalRealMeanZeroWeightedMode (Weight.sobolev ((m : ℝ)+1/2)) n c
  have hline : HasDerivAt (fun t : ℝ => z+t • v) v 0 := by
    simpa using! ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add z
  have hdH : HasFDerivAt (D.birkhoffHillHierarchyHamiltonian m)
      (fderiv ℝ (D.birkhoffHillHierarchyHamiltonian m) z) (z+(0 : ℝ) • v) := by
    simpa only [zero_smul,add_zero] using!
      (D.birkhoffHillHierarchyHamiltonian_analytic m z (mem_univ _)).differentiableAt.hasFDerivAt
  have hd : HasDerivAt (fun t : ℝ => D.birkhoffHillHierarchyHamiltonian m (z+t • v))
      ((fderiv ℝ (D.birkhoffHillHierarchyHamiltonian m) z) v) 0 := by
    simpa only [Function.comp_def] using! hdH.comp_hasDerivAt 0 hline
  exact hd.unique (D.hasDerivAt_birkhoffHierarchyHamiltonian_signed_mode m r hrs z n c)

/-- A real coordinate direction gives exactly 2*Re(z_n)*omega_n. -/
theorem fderiv_birkhoffHierarchyHamiltonian_real_mode
    (D : GlobalRoughAbelianForwardData) (m : ℕ) (r : ℝ) (hrs : r=2*((m : ℝ)+1/2))
    (z : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((m : ℝ)+1/2))) (n : ℕ+) :
    (fderiv ℝ (D.birkhoffHillHierarchyHamiltonian m) z)
      (physicalRealMeanZeroWeightedMode (Weight.sobolev ((m : ℝ)+1/2)) n 1) =
      2*(z.val.val n).re*D.originalHierarchyFrequency m r hrs (originalPositiveActions m r hrs z) n := by
  simpa only [map_one,mul_one] using D.fderiv_birkhoffHierarchyHamiltonian_signed_mode m r hrs z n 1

/-- An imaginary coordinate direction gives exactly 2*Im(z_n)*omega_n. -/
theorem fderiv_birkhoffHierarchyHamiltonian_imaginary_mode
    (D : GlobalRoughAbelianForwardData) (m : ℕ) (r : ℝ) (hrs : r=2*((m : ℝ)+1/2))
    (z : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((m : ℝ)+1/2))) (n : ℕ+) :
    (fderiv ℝ (D.birkhoffHillHierarchyHamiltonian m) z)
      (physicalRealMeanZeroWeightedMode (Weight.sobolev ((m : ℝ)+1/2)) n I) =
      2*(z.val.val n).im*D.originalHierarchyFrequency m r hrs (originalPositiveActions m r hrs z) n := by
  simpa only [Complex.conj_I,Complex.mul_re,Complex.neg_re,Complex.I_re,
    Complex.neg_im,Complex.I_im,neg_zero,mul_zero,mul_neg_one,zero_sub,neg_neg] using
    D.fderiv_birkhoffHierarchyHamiltonian_signed_mode m r hrs z n I

/-- At a closed gap the first physical Hamiltonian differential vanishes
in every signed direction of that mode, without excluding its frequency. -/
theorem fderiv_birkhoffHierarchyHamiltonian_closed_mode
    (D : GlobalRoughAbelianForwardData) (m : ℕ) (r : ℝ) (hrs : r=2*((m : ℝ)+1/2))
    (z : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((m : ℝ)+1/2)))
    (n : ℕ+) (c : ℂ) (hz : z.val.val n = 0) :
    (fderiv ℝ (D.birkhoffHillHierarchyHamiltonian m) z)
      (physicalRealMeanZeroWeightedMode (Weight.sobolev ((m : ℝ)+1/2)) n c) = 0 := by
  rw [D.fderiv_birkhoffHierarchyHamiltonian_signed_mode m r hrs z n c]
  simp only [hz,zero_mul,Complex.zero_re,mul_zero]

/-- Exact frequency coefficient for the printed physical KdV Hamiltonian
composed with the SAME native inverse, in the literal order-three action norm. -/
theorem fderiv_birkhoffKdVHamiltonian_signed_mode (D : GlobalRoughAbelianForwardData)
    (z : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (((1 : ℕ) : ℝ)+1/2)))
    (n : ℕ+) (c : ℂ) :
    (fderiv ℝ D.birkhoffKdVHamiltonian z)
      (physicalRealMeanZeroWeightedMode (Weight.sobolev (((1 : ℕ) : ℝ)+1/2)) n c) =
      2*(z.val.val n*conj c).re*D.originalKdVFrequency (originalPositiveActions 1 3 (by norm_num) z) n := by
  have he : D.birkhoffHillHierarchyHamiltonian 1 = D.birkhoffKdVHamiltonian :=
    funext D.birkhoffHillHierarchyHamiltonian_one
  simpa only [he,originalKdVFrequency] using
    D.fderiv_birkhoffHierarchyHamiltonian_signed_mode 1 3 (by norm_num) z n c

/-- The corresponding exact printed physical KdV2 coefficient, without a
mass or dispersion correction hidden in the definition of the frequency. -/
theorem fderiv_birkhoffKdV2Hamiltonian_signed_mode (D : GlobalRoughAbelianForwardData)
    (z : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (((2 : ℕ) : ℝ)+1/2)))
    (n : ℕ+) (c : ℂ) :
    (fderiv ℝ D.birkhoffKdV2Hamiltonian z)
      (physicalRealMeanZeroWeightedMode (Weight.sobolev (((2 : ℕ) : ℝ)+1/2)) n c) =
      2*(z.val.val n*conj c).re*D.originalKdV2Frequency (originalPositiveActions 2 5 (by norm_num) z) n := by
  have he : D.birkhoffHillHierarchyHamiltonian 2 = D.birkhoffKdV2Hamiltonian :=
    funext D.birkhoffHillHierarchyHamiltonian_two
  simpa only [he,originalKdV2Frequency] using
    D.fderiv_birkhoffHierarchyHamiltonian_signed_mode 2 5 (by norm_num) z n c

end NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
