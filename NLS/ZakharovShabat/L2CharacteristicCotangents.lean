import NLS.ZakharovShabat.L2SourceCharacteristics

/-! # Full source cotangents of the physical L2 endpoint functions

Differentiate the exact identities on the entire source space. Every
Hilbert base point and direction is included, without continuity or
finite-Fourier-support assumptions.
-/
noncomputable section
open Set Complex
namespace NLS.ZakharovShabat

/-- Potential analyticity of each actual L2 separated characteristic. -/
theorem analyticOnNhd_l2SeparatedCharacteristic_potential (b : BoundaryCondition) (z : ℂ) :
    AnalyticOnNhd ℂ (fun u : IntervalPairL2 => l2SeparatedCharacteristic b u z) univ := by
  intro u _
  exact (analyticOnNhd_l2SeparatedCharacteristic_joint b (z,u) (mem_univ _)).comp
    (f := fun v : IntervalPairL2 => (z,v)) (analyticAt_const.prod analyticAt_id)

theorem analyticOnNhd_l2AntiDiscriminant_potential (z : ℂ) :
    AnalyticOnNhd ℂ (fun u : IntervalPairL2 => l2AntiDiscriminant u z) univ := by
  intro u _
  exact (analyticOnNhd_l2AntiDiscriminant_joint (z,u) (mem_univ _)).comp
    (f := fun v : IntervalPairL2 => (z,v)) (analyticAt_const.prod analyticAt_id)

/-- The entire source boundary cotangent is the actual L2 differential composed with physical realization. -/
theorem sourceBoundaryCharacteristicCotangent_eq_l2 (b : BoundaryCondition) (φ : CoeffPair 2) (z : ℂ) :
    sourceBoundaryCharacteristicCotangent (by simp) (by norm_num) b z φ =
      (fderiv ℂ (fun u : IntervalPairL2 => l2SeparatedCharacteristic b u z) (sourcePhysicalL2 φ)).comp sourcePhysicalL2 := by
  have he : (fun ψ : CoeffPair 2 => periodOneBoundaryCharacteristic (by simp) (by norm_num) b ψ z) =
      (fun u : IntervalPairL2 => l2SeparatedCharacteristic b u z) ∘ sourcePhysicalL2 :=
    funext (fun ψ => periodOneBoundaryCharacteristic_eq_l2 b ψ z)
  unfold sourceBoundaryCharacteristicCotangent
  rw [he,fderiv_comp φ ((analyticOnNhd_l2SeparatedCharacteristic_potential b z _ (mem_univ _)).differentiableAt)
    sourcePhysicalL2.differentiableAt,ContinuousLinearMap.fderiv]

/-- Every Hilbert source variation of the separated characteristic is included. -/
theorem sourceBoundaryCharacteristicCotangent_apply_eq_l2 (b : BoundaryCondition) (φ h : CoeffPair 2) (z : ℂ) :
    sourceBoundaryCharacteristicCotangent (by simp) (by norm_num) b z φ h =
      (fderiv ℂ (fun u : IntervalPairL2 => l2SeparatedCharacteristic b u z) (sourcePhysicalL2 φ)) (sourcePhysicalL2 h) := by
  rw [sourceBoundaryCharacteristicCotangent_eq_l2,ContinuousLinearMap.comp_apply]

/-- The entire source anti-discriminant cotangent is the actual L2 differential. -/
theorem sourceAntiDiscriminantCotangent_eq_l2 (φ : CoeffPair 2) (z : ℂ) :
    sourceAntiDiscriminantCotangent (by simp) (by norm_num) z φ =
      (fderiv ℂ (fun u : IntervalPairL2 => l2AntiDiscriminant u z) (sourcePhysicalL2 φ)).comp sourcePhysicalL2 := by
  have he : (fun ψ : CoeffPair 2 => sourceAntiDiscriminantCandidate (by simp) (by norm_num) ψ z) =
      (fun u : IntervalPairL2 => l2AntiDiscriminant u z) ∘ sourcePhysicalL2 :=
    funext (fun ψ => sourceAntiDiscriminantCandidate_eq_l2 ψ z)
  unfold sourceAntiDiscriminantCotangent
  rw [he,fderiv_comp φ ((analyticOnNhd_l2AntiDiscriminant_potential z _ (mem_univ _)).differentiableAt)
    sourcePhysicalL2.differentiableAt,ContinuousLinearMap.fderiv]

/-- Every Hilbert source variation of the anti-discriminant is included. -/
theorem sourceAntiDiscriminantCotangent_apply_eq_l2 (φ h : CoeffPair 2) (z : ℂ) :
    sourceAntiDiscriminantCotangent (by simp) (by norm_num) z φ h =
      (fderiv ℂ (fun u : IntervalPairL2 => l2AntiDiscriminant u z) (sourcePhysicalL2 φ)) (sourcePhysicalL2 h) := by
  rw [sourceAntiDiscriminantCotangent_eq_l2,ContinuousLinearMap.comp_apply]

/-- Spectral derivatives preserve the exact separated-characteristic identity. -/
theorem deriv_periodOneBoundaryCharacteristic_eq_l2 (b : BoundaryCondition) (φ : CoeffPair 2) (z : ℂ) :
    deriv (periodOneBoundaryCharacteristic (by simp) (by norm_num) b φ) z =
      deriv (l2SeparatedCharacteristic b (sourcePhysicalL2 φ)) z := by
  rw [funext (periodOneBoundaryCharacteristic_eq_l2 b φ)]

theorem deriv_sourceAntiDiscriminantCandidate_eq_l2 (φ : CoeffPair 2) (z : ℂ) :
    deriv (sourceAntiDiscriminantCandidate (by simp) (by norm_num) φ) z =
      deriv (l2AntiDiscriminant (sourcePhysicalL2 φ)) z := by
  rw [funext (sourceAntiDiscriminantCandidate_eq_l2 φ)]

end NLS.ZakharovShabat
