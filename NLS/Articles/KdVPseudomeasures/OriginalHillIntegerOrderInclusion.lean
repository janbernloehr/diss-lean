import NLS.Articles.KdVPseudomeasures.OriginalHillIntegerCanonicalFlow
import NLS.SequenceSpaces.SignedSobolevOrderInclusion

/-! Actual compatibility of the SAME native maps and canonical flows
between arbitrary ordered integer Sobolev scales. Every original Fourier
coefficient is retained; these are genuine source and target inclusions. -/
noncomputable section
open NLS.KdV NLS.WeightedCoeff
namespace NLS.Articles.KdVPseudomeasures

def hillIntegerSourceOrderInclusion (N M : ℕ) (h : N≤M) :
    RealSignedHilbert (signedStepOrder 0 M) →L[ℝ] RealSignedHilbert (signedStepOrder 0 N) :=
  signedRealOrderInclusion _ _ (by rw [hillIntegerSobolev_source_order,hillIntegerSobolev_source_order]; exact_mod_cast h)

def hillIntegerTargetOrderInclusion (N M : ℕ) (h : N≤M) :
    RealSignedHilbert (signedStepOrder (1/2) M) →L[ℝ] RealSignedHilbert (signedStepOrder (1/2) N) :=
  signedRealOrderInclusion _ _ (by
    rw [hillIntegerSobolev_target_order,hillIntegerSobolev_target_order]
    have hx : (N:ℝ)≤(M:ℝ) := by exact_mod_cast h
    linarith)

theorem hillIntegerSourceOrderInclusion_apply (N M : ℕ) (h : N≤M)
    (q : RealSignedHilbert (signedStepOrder 0 M)) (k : ℤ) :
    (hillIntegerSourceOrderInclusion N M h q).val.val.val k=q.val.val.val k :=
  signedRealOrderInclusion_apply _ _ _ q k

theorem hillIntegerTargetOrderInclusion_apply (N M : ℕ) (h : N≤M)
    (z : RealSignedHilbert (signedStepOrder (1/2) M)) (k : ℤ) :
    (hillIntegerTargetOrderInclusion N M h z).val.val.val k=z.val.val.val k :=
  signedRealOrderInclusion_apply _ _ _ z k

theorem hillIntegerSourceOrderInclusion_rough (N M : ℕ) (h : N≤M)
    (q : RealSignedHilbert (signedStepOrder 0 M)) :
    hillIntegerSourceInclusion N (hillIntegerSourceOrderInclusion N M h q)=hillIntegerSourceInclusion M q := by
  apply hillRealMeanZeroInclusion_injective
  apply Subtype.ext
  funext k
  change (hillIntegerSourceInclusion N (hillIntegerSourceOrderInclusion N M h q)).val.val.val k=
    (hillIntegerSourceInclusion M q).val.val.val k
  rw [hillIntegerSourceInclusion_apply,hillIntegerSourceOrderInclusion_apply,hillIntegerSourceInclusion_apply]

theorem hillIntegerTargetOrderInclusion_rough (N M : ℕ) (h : N≤M)
    (z : RealSignedHilbert (signedStepOrder (1/2) M)) :
    hillIntegerTargetInclusion N (hillIntegerTargetOrderInclusion N M h z)=hillIntegerTargetInclusion M z := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext k
  rw [hillIntegerTargetInclusion_apply,hillIntegerTargetOrderInclusion_apply,hillIntegerTargetInclusion_apply]

theorem hillIntegerSobolevEquiv_order_compatibility (N M : ℕ) (h : N≤M)
    (q : RealSignedHilbert (signedStepOrder 0 M)) :
    (hillIntegerSobolevEquiv N).equiv (hillIntegerSourceOrderInclusion N M h q)=
      hillIntegerTargetOrderInclusion N M h ((hillIntegerSobolevEquiv M).equiv q) := by
  apply hillIntegerTargetInclusion_injective N
  rw [hillIntegerSobolevEquiv_inclusion,hillIntegerSourceOrderInclusion_rough,
    hillIntegerTargetOrderInclusion_rough,hillIntegerSobolevEquiv_inclusion]

theorem hillIntegerCanonicalKdVFlow_order_compatibility (N M : ℕ) (h : N≤M)
    (q : RealSignedHilbert (signedStepOrder 0 M)) (time : ℝ) :
    hillIntegerCanonicalKdVFlow N (hillIntegerSourceOrderInclusion N M h q) time=
      hillIntegerSourceOrderInclusion N M h (hillIntegerCanonicalKdVFlow M q time) := by
  apply hillIntegerSourceInclusion_injective N
  rw [hillIntegerCanonicalKdVFlow_inclusion,hillIntegerSourceOrderInclusion_rough,
    hillIntegerSourceOrderInclusion_rough,hillIntegerCanonicalKdVFlow_inclusion]

end NLS.Articles.KdVPseudomeasures
