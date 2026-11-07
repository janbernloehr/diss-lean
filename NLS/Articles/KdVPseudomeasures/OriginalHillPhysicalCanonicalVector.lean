import NLS.Articles.KdVPseudomeasures.OriginalHillEnergyCotangentNativeVelocity
import NLS.Articles.KdVPseudomeasures.OriginalHillCanonicalRoughTangent
import NLS.KdV.PeriodOneSmoothEnergyCotangent

/-! The genuine canonical source tangent is the ACTUAL physical KdV
vector at every smooth original H4 source. The bounded rough energy
cotangent is CONSTRUCTED, and all signed native velocities identify the
source vectors by the verified full actual rough Jacobian injectivity. -/
noncomputable section
open Set Complex NLS.KdV NLS.Poisson NLS.WeightedCoeff NLS.ZakharovShabat NLS.Fourier
open scoped ContDiff
namespace NLS.Articles.KdVPseudomeasures

theorem periodOneH1RoughInclusion_signedOne (h : RealSignedHilbert (signedStepOrder 0 1)) :
    periodOneH1RoughInclusion (signedOneRealToScalarDomain h)=
      hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 h) := by
  apply Subtype.ext
  funext k
  rw [periodOneH1RoughInclusion_apply,signedOneRealToScalarDomain_apply]
  exact (hillIntegerSourceInclusion_apply 1 h k).symm

theorem hillIntegerCanonicalKdVVector_eq_energy_cotangent
    (q : RealSignedHilbert (signedStepOrder 0 4)) (L : PeriodOneHminusOne →L[ℂ] ℂ)
    (hL : ∀ h : RealSignedHilbert (signedStepOrder 0 1),
      L (hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 h))=
        (fderiv ℂ periodOneKdVHamiltonian
          (signedOneRealToScalarDomain (hillIntegerSourceOrderInclusion 1 4 (by decide) q))) (signedOneRealToScalarDomain h)) :
    hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 (hillIntegerCanonicalKdVVector 1 q))=
      gardnerHamiltonianDirection L := by
  let r := hillIntegerSourceInclusion 4 q
  let p := hillIntegerSourceOrderInclusion 1 4 (by decide) q
  have hp : hillIntegerSourceInclusion 1 p=r := hillIntegerSourceOrderInclusion_rough 1 4 (by decide) q
  let v : HillMeanZeroSource := (hillIntegerSourceInclusion 1 (hillIntegerCanonicalKdVVector 1 q)).val
  let g : HillMeanZeroSource := ⟨gardnerHamiltonianDirection L,gardnerHamiltonianDirection_zero_mode L⟩
  have hdomain := real_mem_hillMeanZeroComplexDomain r.val r.property
  have hv : (fderiv ℂ hillMeanZeroComplexMap r.val) v=(fderiv ℂ hillMeanZeroComplexMap r.val) g := by
    apply Subtype.ext
    apply Subtype.ext
    funext k
    rw [fderiv_hillMeanZeroComplexMap_coordinate r.val hdomain v k,
      fderiv_hillMeanZeroComplexMap_coordinate r.val hdomain g k]
    have hG := energy_cotangent_native_signed_velocity p L hL k
    rw [hp] at hG
    exact (hillIntegerCanonicalKdVVector_rough_native_velocity 1 q k).trans hG.symm
  have he : v=g := (hillRealNativeJacobian_bijective r).1 hv
  exact congrArg (fun h : HillMeanZeroSource => h.val) he

theorem hillIntegerCanonicalKdVVector_physical_KdV_coefficients
    (q : RealSignedHilbert (signedStepOrder 0 4))
    (hq : ContDiff ℝ ∞ (fun x : ℝ => periodOneSobolevSynthesis
      (signedOneRealToScalarDomain (hillIntegerSourceOrderInclusion 1 4 (by decide) q)) (x : AddCircle (2:ℝ))))
    (k : ℤ) :
    (hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 (hillIntegerCanonicalKdVVector 1 q))).val k=
      periodOneCoefficient (classicalKdVVectorField (fun x : ℝ => periodOneSobolevSynthesis
        (signedOneRealToScalarDomain (hillIntegerSourceOrderInclusion 1 4 (by decide) q)) (x : AddCircle (2:ℝ)))) k := by
  let a := signedOneRealToScalarDomain (hillIntegerSourceOrderInclusion 1 4 (by decide) q)
  let L := periodOneSmoothKdVEnergyCotangent a hq
  have hL (h : RealSignedHilbert (signedStepOrder 0 1)) :
      L (hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 h))=
        (fderiv ℂ periodOneKdVHamiltonian a) (signedOneRealToScalarDomain h) := by
    have he := congrArg (fun A : ScalarDomain 2 →L[ℂ] ℂ => A (signedOneRealToScalarDomain h))
      (periodOneSmoothKdVEnergyCotangent_restrict a hq)
    change L (periodOneH1RoughInclusion (signedOneRealToScalarDomain h))=_ at he
    rw [periodOneH1RoughInclusion_signedOne] at he
    exact he
  have he := hillIntegerCanonicalKdVVector_eq_energy_cotangent q L hL
  rw [he]
  exact periodOneSmoothKdVEnergyCotangent_physical_vector a hq k

end NLS.Articles.KdVPseudomeasures
