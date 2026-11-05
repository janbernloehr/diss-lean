import NLS.Articles.KdVPseudomeasures.OriginalHillIntegerOrderInclusion
import NLS.Articles.KdVPseudomeasures.OriginalHillCanonicalFrequencyGenerator
import NLS.SequenceSpaces.FourierRealPhaseDerivative

/-! Genuine strong differentiation of the canonical KdV source flow.
Three more actual Sobolev orders put the cubic canonical velocity in the
lower native space. The SAME actual inverse differential gives the source
tangent; physical PDE identification remains a further obligation. -/
noncomputable section
open Set Complex Filter Topology NLS.KdV NLS.WeightedCoeff NLS.LpSequence
namespace NLS.Articles.KdVPseudomeasures

theorem exists_actual_frequency_generator_at_orders (s t : ℝ) (hst : s+3=t)
    (q : HillRealMeanZeroSource) (z : RealSignedHilbert t) :
    ∃ v : RealSignedHilbert s, ∀ k,
      v.val.val.val k=I*(oddPositiveFrequency (fun n => hillRoughKdVFrequency n q) k:ℂ)*z.val.val.val k := by
  subst t
  exact ⟨hillRoughKdVFrequencyGenerator s q 2 z,fun k => hillRoughKdVFrequencyGenerator_apply s q z k⟩

def hillIntegerCanonicalNativeVelocity (N : ℕ)
    (q : RealSignedHilbert (signedStepOrder 0 (N+3))) :
    RealSignedHilbert (signedStepOrder (1/2) N) :=
  Classical.choose (exists_actual_frequency_generator_at_orders
    (signedStepOrder (1/2) N) (signedStepOrder (1/2) (N+3))
    (by rw [hillIntegerSobolev_target_order,hillIntegerSobolev_target_order]; push_cast; ring)
    (hillIntegerSourceInclusion (N+3) q) ((hillIntegerSobolevEquiv (N+3)).equiv q))

theorem hillIntegerCanonicalNativeVelocity_apply (N : ℕ)
    (q : RealSignedHilbert (signedStepOrder 0 (N+3))) (k : ℤ) :
    (hillIntegerCanonicalNativeVelocity N q).val.val.val k=
      I*(oddPositiveFrequency (fun n => hillRoughKdVFrequency n (hillIntegerSourceInclusion (N+3) q)) k:ℂ)*
        ((hillIntegerSobolevEquiv (N+3)).equiv q).val.val.val k :=
  Classical.choose_spec (exists_actual_frequency_generator_at_orders
    (signedStepOrder (1/2) N) (signedStepOrder (1/2) (N+3))
    (by rw [hillIntegerSobolev_target_order,hillIntegerSobolev_target_order]; push_cast; ring)
    (hillIntegerSourceInclusion (N+3) q) ((hillIntegerSobolevEquiv (N+3)).equiv q)) k

theorem hasDerivAt_hillIntegerCanonicalFlow_native_zero (N : ℕ)
    (q : RealSignedHilbert (signedStepOrder 0 (N+3))) :
    HasDerivAt (fun time : ℝ => (hillIntegerSobolevEquiv N).equiv
      (hillIntegerSourceOrderInclusion N (N+3) (by omega) (hillIntegerCanonicalKdVFlow (N+3) q time)))
      (hillIntegerCanonicalNativeVelocity N q) 0 := by
  let r := hillIntegerSourceOrderInclusion N (N+3) (by omega) q
  let Q := hillIntegerSourceInclusion (N+3) q
  let freq := oddPositiveFrequency (fun n => hillRoughKdVFrequency n Q)
  have hr : hillIntegerSourceInclusion N r=Q := hillIntegerSourceOrderInclusion_rough N (N+3) (by omega) q
  have hv (k : ℤ) : (hillIntegerCanonicalNativeVelocity N q).val.val.val k=
      I*(freq k:ℂ)*((hillIntegerSobolevEquiv N).equiv r).val.val.val k := by
    rw [hillIntegerCanonicalNativeVelocity_apply]
    change _=I*(freq k:ℂ)*((hillIntegerSobolevEquiv N).equiv
      (hillIntegerSourceOrderInclusion N (N+3) (by omega) q)).val.val.val k
    rw [hillIntegerSobolevEquiv_order_compatibility,hillIntegerTargetOrderInclusion_apply]
  have hd := hasDerivAt_fourierRealZeroPhaseFlow
    (Weight.signedSobolev (signedStepOrder (1/2) N)) (Weight.signedSobolev_neg _) (by simp)
    freq (oddPositiveFrequency_neg _) ((hillIntegerSobolevEquiv N).equiv r)
    (hillIntegerCanonicalNativeVelocity N q) hv 0
  simp only [fourierRealZeroPhaseFlow_zero] at hd
  have he : (fun time : ℝ => (hillIntegerSobolevEquiv N).equiv
      (hillIntegerSourceOrderInclusion N (N+3) (by omega) (hillIntegerCanonicalKdVFlow (N+3) q time)))=
      (fun time => fourierRealZeroPhaseFlow (Weight.signedSobolev (signedStepOrder (1/2) N))
        freq (oddPositiveFrequency_neg _) time ((hillIntegerSobolevEquiv N).equiv r)) := by
    funext time
    rw [← hillIntegerCanonicalKdVFlow_order_compatibility,hillIntegerCanonicalKdVFlow_native]
    change fourierRealZeroPhaseFlow _ (oddPositiveFrequency (fun n => hillRoughKdVFrequency n (hillIntegerSourceInclusion N r))) _ _ _=_
    rw [hr]
  rw [he]
  exact hd

def hillIntegerCanonicalKdVVector (N : ℕ)
    (q : RealSignedHilbert (signedStepOrder 0 (N+3))) : RealSignedHilbert (signedStepOrder 0 N) :=
  (fderiv ℝ (hillIntegerSobolevEquiv N).equiv.symm
    ((hillIntegerSobolevEquiv N).equiv (hillIntegerSourceOrderInclusion N (N+3) (by omega) q)))
      (hillIntegerCanonicalNativeVelocity N q)

theorem hasDerivAt_hillIntegerCanonicalKdVFlow_zero (N : ℕ)
    (q : RealSignedHilbert (signedStepOrder 0 (N+3))) :
    HasDerivAt (fun time : ℝ => hillIntegerSourceOrderInclusion N (N+3) (by omega)
      (hillIntegerCanonicalKdVFlow (N+3) q time)) (hillIntegerCanonicalKdVVector N q) 0 := by
  let z := (hillIntegerSobolevEquiv N).equiv (hillIntegerSourceOrderInclusion N (N+3) (by omega) q)
  have hi : HasFDerivAt (hillIntegerSobolevEquiv N).equiv.symm
      (fderiv ℝ (hillIntegerSobolevEquiv N).equiv.symm z) z :=
    ((hillIntegerSobolevEquiv N).analytic_symm z).differentiableAt.hasFDerivAt
  have hd := @HasFDerivAt.comp_hasDerivAt_of_eq ℝ inferInstance
    (RealSignedHilbert (signedStepOrder (1/2) N)) inferInstance inferInstance
    (RealSignedHilbert (signedStepOrder 0 N)) inferInstance inferInstance
    (fun time : ℝ => (hillIntegerSobolevEquiv N).equiv
      (hillIntegerSourceOrderInclusion N (N+3) (by omega) (hillIntegerCanonicalKdVFlow (N+3) q time)))
    (hillIntegerCanonicalNativeVelocity N q) 0 (hillIntegerSobolevEquiv N).equiv.symm
    (fderiv ℝ (hillIntegerSobolevEquiv N).equiv.symm z) z hi
    (hasDerivAt_hillIntegerCanonicalFlow_native_zero N q) (by rw [hillIntegerCanonicalKdVFlow_zero])
  have he : (fun time : ℝ => (hillIntegerSobolevEquiv N).equiv.symm
      ((hillIntegerSobolevEquiv N).equiv (hillIntegerSourceOrderInclusion N (N+3) (by omega)
        (hillIntegerCanonicalKdVFlow (N+3) q time))))=
      (fun time => hillIntegerSourceOrderInclusion N (N+3) (by omega) (hillIntegerCanonicalKdVFlow (N+3) q time)) := by
    funext time
    exact (hillIntegerSobolevEquiv N).equiv.symm_apply_apply _
  dsimp only [Function.comp_def] at hd
  rw [he] at hd
  exact hd

end NLS.Articles.KdVPseudomeasures
