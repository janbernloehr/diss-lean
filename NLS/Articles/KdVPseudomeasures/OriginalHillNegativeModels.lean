import NLS.KdV.HillFractionalDerivativeCompact
import NLS.Articles.KdVPseudomeasures.OriginalHillPhysicalRealInverse
import NLS.SequenceSpaces.SignedSobolevOrderInclusion
import NLS.SequenceSpaces.FourierRealWeightRegularity

/-! The physical mean-zero negative Hilbert models, coefficient-preserving
rough inclusions, and the exact free half-Fourier equivalence. -/
noncomputable section
open NLS.KdV NLS.WeightedCoeff
namespace NLS.Articles.KdVPseudomeasures

abbrev HillRealNegativeSource (r : ℝ) := fourierRealZeroSubmodule (Weight.sobolev (-r)) 2
abbrev HillRealFractionalTarget (r : ℝ) := fourierRealZeroSubmodule (Weight.signedSobolev (1/2-r)) 2

def hillNegativeSourceCoefficients (r : ℝ) :
    HillRealNegativeSource r →L[ℝ] WeightedCoeff (Weight.sobolev (-r)) 2 :=
  ((zeroModeSubmodule (Weight.sobolev (-r)) 2).subtypeL.restrictScalars ℝ).comp
    (fourierRealZeroSubmodule (Weight.sobolev (-r)) 2).subtypeL

theorem hillNegativeSourceCoefficients_apply (r : ℝ) (q : HillRealNegativeSource r) (k : ℤ) :
    (hillNegativeSourceCoefficients r q).val k = q.val.val.val k := rfl

def hillNegativeSourceInclusion (r : ℝ) (hr1 : r < 1) :
    HillRealNegativeSource r →L[ℝ] HillRealMeanZeroSource :=
  fourierRealZeroMultiplier _ _ (Weight.sobolev_neg (-1)) (fun _ => 1) 1 zero_le_one
    (by intro k; simp only [norm_one, mul_one, one_mul];
        exact Weight.sobolev_mono (show (-1:ℝ) ≤ -r by linarith) k)
    (by intro k; simp)

theorem hillNegativeSourceInclusion_apply (r : ℝ) (hr1 : r < 1)
    (q : HillRealNegativeSource r) (k : ℤ) :
    (hillNegativeSourceInclusion r hr1 q).val.val.val k = q.val.val.val k := by
  rw [hillNegativeSourceInclusion, fourierRealZeroMultiplier_apply, one_mul]

theorem hillNegativeSourceInclusion_injective (r : ℝ) (hr1 : r < 1) :
    Function.Injective (hillNegativeSourceInclusion r hr1) := by
  intro q a he
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext k
  simpa only [hillNegativeSourceInclusion_apply] using
    congrArg (fun b : HillRealMeanZeroSource => b.val.val.val k) he

theorem exists_hillNegativeSource_of_memlp (r : ℝ) (hr1 : r < 1) (q : HillRealMeanZeroSource)
    (hq : Memℓp (fun k => (Weight.sobolev (-r) k:ℂ)*q.val.val.val k) 2) :
    ∃ u : HillRealNegativeSource r, hillNegativeSourceInclusion r hr1 u = q :=
  exists_physicalWeightRealization _ _ (Weight.sobolev_neg (-r)) (hillNegativeSourceInclusion r hr1)
    (hillNegativeSourceInclusion_apply r hr1) q hq

theorem hillNegativeSourceCoefficients_rough (r : ℝ) (hr1 : r < 1) (q : HillRealNegativeSource r) :
    sobolevInclusion (show (-1:ℝ) ≤ -r by linarith) (hillNegativeSourceCoefficients r q) =
      (hillNegativeSourceInclusion r hr1 q).val.val := by
  apply Subtype.ext
  funext k
  rw [sobolevInclusion_apply, hillNegativeSourceCoefficients_apply, hillNegativeSourceInclusion_apply]

theorem hillNegativeSourceCoefficients_real (r : ℝ) (hr1 : r < 1) (q : HillRealNegativeSource r) :
    IsRealPeriodOneHminusOne
      (sobolevInclusion (show (-1:ℝ) ≤ -r by linarith) (hillNegativeSourceCoefficients r q)) := by
  rw [hillNegativeSourceCoefficients_rough]
  exact (hillNegativeSourceInclusion r hr1 q).property

def hillNegativeTargetInclusion (r : ℝ) (hr1 : r < 1) :
    HillRealFractionalTarget r →L[ℝ] HillRealSignedTarget :=
  signedRealOrderInclusion (-1/2) (1/2-r) (by linarith)

theorem hillNegativeTargetInclusion_apply (r : ℝ) (hr1 : r < 1)
    (z : HillRealFractionalTarget r) (k : ℤ) :
    (hillNegativeTargetInclusion r hr1 z).val.val.val k = z.val.val.val k :=
  signedRealOrderInclusion_apply _ _ _ z k

theorem hillNegativeTargetInclusion_injective (r : ℝ) (hr1 : r < 1) :
    Function.Injective (hillNegativeTargetInclusion r hr1) :=
  signedRealOrderInclusion_injective _ _ _

def hillNegativeFreeFourierEquiv (r : ℝ) (hr : 0 ≤ r) :
    HillRealNegativeSource r ≃L[ℝ] HillRealFractionalTarget r :=
  (physicalSignedSobolevNegativeEquiv r hr).symm.trans
    (signedRealOrderHalfFourierEquivOfEq (-r) (1/2-r) (by ring) 2)

theorem hillNegativeFreeFourierEquiv_apply (r : ℝ) (hr : 0 ≤ r)
    (q : HillRealNegativeSource r) (k : ℤ) :
    (hillNegativeFreeFourierEquiv r hr q).val.val.val k = halfFourierSymbol k*q.val.val.val k := by
  rw [hillNegativeFreeFourierEquiv, ContinuousLinearEquiv.trans_apply,
    signedRealOrderHalfFourierEquivOfEq_apply, physicalSignedSobolevNegativeEquiv_symm_apply]

end NLS.Articles.KdVPseudomeasures
