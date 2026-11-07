import NLS.Articles.KdVPseudomeasures.OriginalHillIntegerCanonicalDerivative

/-! The exact canonical source tangent at EVERY time, and its actual
native Jacobian image. These are strong Banach-space derivatives, with
three additional source Sobolev orders and the SAME actual native map. -/
noncomputable section
open Set Filter Topology NLS.KdV NLS.WeightedCoeff
namespace NLS.Articles.KdVPseudomeasures

theorem hasDerivAt_hillIntegerCanonicalKdVFlow (N : ℕ)
    (q : RealSignedHilbert (signedStepOrder 0 (N+3))) (time : ℝ) :
    HasDerivAt (fun r : ℝ => hillIntegerSourceOrderInclusion N (N+3) (by omega)
      (hillIntegerCanonicalKdVFlow (N+3) q r))
      (hillIntegerCanonicalKdVVector N (hillIntegerCanonicalKdVFlow (N+3) q time)) time := by
  have hshift : HasDerivAt (fun r : ℝ => r-time) 1 time := (hasDerivAt_id time).sub_const time
  have hd := HasDerivAt.scomp_of_eq (𝕜 := ℝ) (𝕜' := ℝ)
    (F := RealSignedHilbert (signedStepOrder 0 N)) time
    (hasDerivAt_hillIntegerCanonicalKdVFlow_zero N (hillIntegerCanonicalKdVFlow (N+3) q time)) hshift (by simp)
  have he : (fun r : ℝ => hillIntegerSourceOrderInclusion N (N+3) (by omega)
      (hillIntegerCanonicalKdVFlow (N+3) (hillIntegerCanonicalKdVFlow (N+3) q time) (r-time)))=
      (fun r => hillIntegerSourceOrderInclusion N (N+3) (by omega) (hillIntegerCanonicalKdVFlow (N+3) q r)) := by
    funext r
    rw [hillIntegerCanonicalKdVFlow_add,sub_add_cancel]
  dsimp only [Function.comp_def] at hd
  rw [he,one_smul] at hd
  exact hd

theorem hillIntegerCanonicalKdVVector_nativeJacobian (N : ℕ)
    (q : RealSignedHilbert (signedStepOrder 0 (N+3))) :
    (fderiv ℝ (hillIntegerSobolevEquiv N).equiv
      (hillIntegerSourceOrderInclusion N (N+3) (by omega) q)) (hillIntegerCanonicalKdVVector N q)=
        hillIntegerCanonicalNativeVelocity N q := by
  let r := hillIntegerSourceOrderInclusion N (N+3) (by omega) q
  have hi : HasFDerivAt (hillIntegerSobolevEquiv N).equiv
      (fderiv ℝ (hillIntegerSobolevEquiv N).equiv r) r :=
    ((hillIntegerSobolevEquiv N).analytic r).differentiableAt.hasFDerivAt
  have hd := @HasFDerivAt.comp_hasDerivAt_of_eq ℝ inferInstance
    (RealSignedHilbert (signedStepOrder 0 N)) inferInstance inferInstance
    (RealSignedHilbert (signedStepOrder (1/2) N)) inferInstance inferInstance
    (fun time : ℝ => hillIntegerSourceOrderInclusion N (N+3) (by omega) (hillIntegerCanonicalKdVFlow (N+3) q time))
    (hillIntegerCanonicalKdVVector N q) 0 (hillIntegerSobolevEquiv N).equiv
    (fderiv ℝ (hillIntegerSobolevEquiv N).equiv r) r hi
    (hasDerivAt_hillIntegerCanonicalKdVFlow_zero N q) (by rw [hillIntegerCanonicalKdVFlow_zero])
  exact HasDerivAt.unique (𝕜 := ℝ) (F := RealSignedHilbert (signedStepOrder (1/2) N))
    hd (hasDerivAt_hillIntegerCanonicalFlow_native_zero N q)

end NLS.Articles.KdVPseudomeasures
