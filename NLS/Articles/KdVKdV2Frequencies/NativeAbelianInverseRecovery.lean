import NLS.Articles.KdVKdV2Frequencies.ActualNativeJacobianUnit

/-! # Exact native coefficient recovery, including both central zero slots -/
noncomputable section
set_option autoImplicit false
open Set Complex
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies

/-- The exact normalized commuting diagram at ANY genuine native point. -/
theorem nativeMeanZeroAbelianMap_commuting
    (t : ℝ) (ht : 0≤t)
    (Z : PeriodOneHminusOne → WeightedCoeff (Weight.sobolev (-1/2)) 2)
    (g : WeightedCoeff (Weight.sobolev (t-1)) 2 → WeightedCoeff (Weight.sobolev (t-1/2)) 2)
    (a : DeletedCoeff 2 0)
    (hcomm : WeightedCoeff.sobolevInclusion (by linarith : (-1/2 : ℝ)≤t-1/2)
      (g (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (t-1)) a))=
      Z (periodOneSobolevImageInclusion t ht (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (t-1)) a))) :
    WeightedCoeff.meanZeroSobolevInclusion (by linarith : (-1/2 : ℝ)≤t-1/2) (nativeMeanZeroAbelianMap t g a)=
      weakMeanZeroAbelianMap Z (WeightedCoeff.meanZeroSobolevInclusion (by linarith : (-1 : ℝ)≤t-1) a) := by
  change WeightedCoeff.meanZeroSobolevInclusion _ (WeightedCoeff.meanZeroWeightedProjectionCLM _ (g _))=
    WeightedCoeff.meanZeroWeightedProjectionCLM (Weight.sobolev (-1/2))
      (Z (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1)) (WeightedCoeff.meanZeroSobolevInclusion _ a)))
  rw [WeightedCoeff.meanZeroSobolevInclusion_projection,hcomm,WeightedCoeff.meanZeroSobolevInclusion_lift]
  rfl

/-- Normalized matching recovers the FULL actual source, including zero. -/
theorem native_source_lift_recovery
    (t : ℝ) (ht : 0≤t) (a b : DeletedCoeff 2 0)
    (R : DeletedCoeff 2 0 → PeriodOneHminusOne) (hmean : (R b).val 0=0)
    (he : WeightedCoeff.meanZeroSobolevInclusion (by linarith : (-1 : ℝ)≤t-1) a=
      WeightedCoeff.meanZeroWeightedProjectionCLM (Weight.sobolev (-1)) (R b)) :
    periodOneSobolevImageInclusion t ht (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (t-1)) a)=R b := by
  have h := congrArg (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1))) he
  rw [WeightedCoeff.meanZeroSobolevInclusion_lift,WeightedCoeff.meanZeroWeightedLift_projection _ _ hmean] at h
  exact h

/-- Matching the SAME actual rough inverse recovers the FULL stronger
forward identity, rather than only its projected mean-zero coordinates. -/
theorem native_inverse_full_target_recovery
    (t : ℝ) (ht : 0≤t)
    (Z : PeriodOneHminusOne → WeightedCoeff (Weight.sobolev (-1/2)) 2)
    (g : WeightedCoeff (Weight.sobolev (t-1)) 2 → WeightedCoeff (Weight.sobolev (t-1/2)) 2)
    (R : DeletedCoeff 2 0 → PeriodOneHminusOne) (a b : DeletedCoeff 2 0)
    (hcomm : WeightedCoeff.sobolevInclusion (by linarith : (-1/2 : ℝ)≤t-1/2)
      (g (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (t-1)) a))=
      Z (periodOneSobolevImageInclusion t ht (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (t-1)) a)))
    (hmatch : periodOneSobolevImageInclusion t ht (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (t-1)) a)=
      R (WeightedCoeff.meanZeroSobolevInclusion (by linarith : (-1/2 : ℝ)≤t-1/2) b))
    (hRsolve : Z (R (WeightedCoeff.meanZeroSobolevInclusion (by linarith : (-1/2 : ℝ)≤t-1/2) b))=
      WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1/2))
        (WeightedCoeff.meanZeroSobolevInclusion (by linarith : (-1/2 : ℝ)≤t-1/2) b))
    (hsolve : nativeMeanZeroAbelianMap t g a=b) :
    g (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (t-1)) a)=
      WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (t-1/2)) b := by
  have hc := hcomm
  rw [hmatch,hRsolve] at hc
  have hz : (g (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (t-1)) a)).val 0=0 := by
    have h := congrArg (fun z : WeightedCoeff (Weight.sobolev (-1/2)) 2 => z.val 0) hc
    simpa only [WeightedCoeff.sobolevInclusion_apply,WeightedCoeff.meanZeroWeightedLift_zero] using h
  calc
    _ = WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (t-1/2))
      (nativeMeanZeroAbelianMap t g a) := (WeightedCoeff.meanZeroWeightedLift_projection _ _ hz).symm
    _ = _ := by rw [hsolve]

end NLS.Articles.KdVKdV2Frequencies
