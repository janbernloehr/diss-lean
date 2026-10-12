import NLS.ZakharovShabat.L2Discriminant
import NLS.ZakharovShabat.SourceDiscriminantCotangent

/-! # The actual L2 discriminant differential on every Hilbert source direction

The canonical and physical discriminants agree on the entire source space.
The chain rule therefore identifies their full continuous cotangents, not
only variations along finite Fourier polynomials.
-/
noncomputable section
open Set Complex
namespace NLS.ZakharovShabat

/-- Analyticity in the physical potential for every fixed spectral parameter. -/
theorem analyticOnNhd_l2Discriminant_potential (z : ℂ) :
    AnalyticOnNhd ℂ (fun u : IntervalPairL2 => l2Discriminant u z) univ := by
  intro u _
  exact (analyticOnNhd_l2Discriminant_joint (z,u) (mem_univ _)).comp
    (f := fun v : IntervalPairL2 => (z,v)) (analyticAt_const.prod analyticAt_id)

/-- Equality of the entire source cotangent with the differential of the physical L2 trace. -/
theorem sourceDiscriminantCotangent_eq_l2 (φ : CoeffPair 2) (z : ℂ) :
    sourceDiscriminantCotangent (by simp) z φ =
      (fderiv ℂ (fun u : IntervalPairL2 => l2Discriminant u z) (sourcePhysicalL2 φ)).comp sourcePhysicalL2 := by
  have he : (fun ψ : CoeffPair 2 => canonicalDiscriminant (by simp) (periodOnePotential ψ) z) =
      (fun u : IntervalPairL2 => l2Discriminant u z) ∘ sourcePhysicalL2 := by
    funext ψ
    exact canonicalDiscriminant_eq_l2_source ψ z
  unfold sourceDiscriminantCotangent
  rw [he,fderiv_comp φ ((analyticOnNhd_l2Discriminant_potential z _ (mem_univ _)).differentiableAt)
    sourcePhysicalL2.differentiableAt,ContinuousLinearMap.fderiv]

/-- Every original Hilbert source direction is admitted; no finite-support or continuity hypothesis is needed. -/
theorem sourceDiscriminantCotangent_apply_eq_l2 (φ h : CoeffPair 2) (z : ℂ) :
    sourceDiscriminantCotangent (by simp) z φ h =
      (fderiv ℂ (fun u : IntervalPairL2 => l2Discriminant u z) (sourcePhysicalL2 φ)) (sourcePhysicalL2 h) := by
  rw [sourceDiscriminantCotangent_eq_l2,ContinuousLinearMap.comp_apply]

/-- Spectral differentiation also retains the exact physical discriminant. -/
theorem deriv_canonicalDiscriminant_eq_l2 (φ : CoeffPair 2) (z : ℂ) :
    deriv (canonicalDiscriminant (by simp) (periodOnePotential φ)) z =
      deriv (l2Discriminant (sourcePhysicalL2 φ)) z := by
  have he : canonicalDiscriminant (by simp) (periodOnePotential φ) = l2Discriminant (sourcePhysicalL2 φ) :=
    funext (canonicalDiscriminant_eq_l2_source φ)
  rw [he]

end NLS.ZakharovShabat
