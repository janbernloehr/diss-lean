import NLS.SequenceSpaces.MeanZeroWeightedCoordinates
import NLS.SequenceSpaces.SobolevDerivative

/-! # Literal inclusions in normalized mean-zero Sobolev charts

The deleted Hilbert coordinates normalize each native Sobolev norm by its
actual weight. Inclusion preserves raw coefficients, including the central
zero, and is injective. These maps compare actual inverse branches.
-/
noncomputable section
set_option autoImplicit false
namespace NLS.WeightedCoeff

@[simp] theorem meanZeroWeightedLift_apply (w : Weight) (a : DeletedCoeff 2 0) (j : ℤ) :
    (meanZeroWeightedLiftCLM w a).val j=a.val j/(w j : ℂ) := rfl

@[simp] theorem meanZeroWeightedLift_zero (w : Weight) (a : DeletedCoeff 2 0) :
    (meanZeroWeightedLiftCLM w a).val 0=0 := by
  have h0 : a.val 0=0 := a.property
  rw [meanZeroWeightedLift_apply,h0,zero_div]

theorem meanZeroWeightedProjection_apply_other (w : Weight) (z : WeightedCoeff w 2)
    (j : ℤ) (hj : j≠0) :
    (meanZeroWeightedProjectionCLM w z).val j=(w j : ℂ)*z.val j := by
  change Coeff.deleteCoordinate 0 (weightEquiv w 2 z) j=_
  rw [Coeff.deleteCoordinate_apply_other 0 j hj,weightEquiv_apply]

/-- Native Sobolev inclusion written in the exact mean-zero weight charts. -/
def meanZeroSobolevInclusion {s t : ℝ} (h : t≤s) : DeletedCoeff 2 0 →L[ℂ] DeletedCoeff 2 0 :=
  (meanZeroWeightedProjectionCLM (Weight.sobolev t)).comp
    ((sobolevInclusion h).comp (meanZeroWeightedLiftCLM (Weight.sobolev s)))

theorem meanZeroSobolevInclusion_lift {s t : ℝ} (h : t≤s) (a : DeletedCoeff 2 0) :
    meanZeroWeightedLiftCLM (Weight.sobolev t) (meanZeroSobolevInclusion h a)=
      sobolevInclusion h (meanZeroWeightedLiftCLM (Weight.sobolev s) a) :=
  meanZeroWeightedLift_projection _ _ (by
    change (sobolevInclusion h (meanZeroWeightedLiftCLM (Weight.sobolev s) a)).val 0=0
    rw [sobolevInclusion_apply,meanZeroWeightedLift_zero])

theorem meanZeroSobolevInclusion_injective {s t : ℝ} (h : t≤s) :
    Function.Injective (meanZeroSobolevInclusion h) := by
  intro a b hab
  have H := congrArg (meanZeroWeightedLiftCLM (Weight.sobolev t)) hab
  rw [meanZeroSobolevInclusion_lift,meanZeroSobolevInclusion_lift] at H
  have H' := sobolevInclusion_injective h H
  have H'' := congrArg (meanZeroWeightedProjectionCLM (Weight.sobolev s)) H'
  simpa only [meanZeroWeightedProjection_lift] using H''

/-- Inclusion commutes with the normalized central-coordinate projection,
even when the original complex sequence has a nonzero central slot. -/
theorem meanZeroSobolevInclusion_projection {s t : ℝ} (h : t≤s)
    (z : WeightedCoeff (Weight.sobolev s) 2) :
    meanZeroSobolevInclusion h (meanZeroWeightedProjectionCLM (Weight.sobolev s) z)=
      meanZeroWeightedProjectionCLM (Weight.sobolev t) (sobolevInclusion h z) := by
  ext j
  by_cases hj : j=0
  · subst j
    have hz (a : DeletedCoeff 2 0) : a.val 0=0 := a.property
    exact (hz _).trans (hz _).symm
  · change (meanZeroWeightedProjectionCLM (Weight.sobolev t)
      (sobolevInclusion h (meanZeroWeightedLiftCLM (Weight.sobolev s)
        (meanZeroWeightedProjectionCLM (Weight.sobolev s) z)))).val j=_
    rw [meanZeroWeightedProjection_apply_other _ _ j hj,
      meanZeroWeightedProjection_apply_other _ _ j hj,sobolevInclusion_apply,
      sobolevInclusion_apply,meanZeroWeightedLift_apply,
      meanZeroWeightedProjection_apply_other _ _ j hj,
      mul_div_cancel_left₀ _ (Weight.complex_ne_zero _ _)]

/-- The actual half-order target/source ratio is independent of the order. -/
theorem sobolev_half_ratio (s : ℝ) (j : ℤ) :
    (Weight.sobolev (s+1/2) j : ℂ)/(Weight.sobolev s j : ℂ)=
      (Weight.sobolev (1/2) j : ℂ) := by
  rw [Weight.sobolev_add,Complex.ofReal_mul,mul_div_cancel_left₀ _ (Weight.complex_ne_zero _ _)]

end NLS.WeightedCoeff
