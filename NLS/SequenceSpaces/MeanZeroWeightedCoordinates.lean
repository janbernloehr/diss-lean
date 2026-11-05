import NLS.SequenceSpaces.DeletedCoordinate
import NLS.SequenceSpaces.Weighted
import Mathlib.Analysis.Analytic.Linear
import Mathlib.Analysis.Analytic.Composition
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-! # Exact linear charts for mean-zero weighted Hilbert targets -/
noncomputable section
open Set Metric
namespace NLS.WeightedCoeff

def meanZeroWeightedLiftCLM (w : Weight) : DeletedCoeff 2 0 →L[ℂ] WeightedCoeff w 2 :=
  ((weightIsometry w 2).symm.toContinuousLinearEquiv.toContinuousLinearMap).comp
    (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 0).ker.subtypeL

def meanZeroWeightedProjectionCLM (w : Weight) : WeightedCoeff w 2 →L[ℂ] DeletedCoeff 2 0 :=
  (Coeff.deleteCoordinateTo 0).comp (weightIsometry w 2).toContinuousLinearEquiv.toContinuousLinearMap

theorem meanZeroWeightedProjection_lift (w : Weight) (b : DeletedCoeff 2 0) :
    meanZeroWeightedProjectionCLM w (meanZeroWeightedLiftCLM w b) = b := by
  apply Subtype.ext
  change Coeff.deleteCoordinate 0 ((weightEquiv w 2) ((weightEquiv w 2).symm b.val)) = b.val
  rw [LinearEquiv.apply_symm_apply]
  exact (Coeff.deleteCoordinate_eq_self_iff 0 b.val).mpr b.property

theorem meanZeroWeightedLift_projection (w : Weight) (z : WeightedCoeff w 2) (hz : z.val 0 = 0) :
    meanZeroWeightedLiftCLM w (meanZeroWeightedProjectionCLM w z) = z := by
  change (weightEquiv w 2).symm (Coeff.deleteCoordinate 0 ((weightEquiv w 2) z)) = z
  rw [(Coeff.deleteCoordinate_eq_self_iff 0 ((weightEquiv w 2) z)).mpr
    (by rw [weightEquiv_apply,hz,mul_zero]),LinearEquiv.symm_apply_apply]

theorem meanZeroWeightedLift_norm (w : Weight) (b : DeletedCoeff 2 0) : ‖meanZeroWeightedLiftCLM w b‖ = ‖b‖ :=
  (weightIsometry w 2).symm.norm_map b.val

def meanZeroWeightedMap (w : Weight) (Z : Coeff 2 → WeightedCoeff w 2) (a : DeletedCoeff 2 0) : DeletedCoeff 2 0 :=
  meanZeroWeightedProjectionCLM w (Z a.val)

theorem meanZeroWeightedMap_apply_other (w : Weight) (Z : Coeff 2 → WeightedCoeff w 2)
    (a : DeletedCoeff 2 0) (j : ℤ) (hj : j ≠ 0) :
    (meanZeroWeightedMap w Z a).val j = (w j : ℂ)*(Z a.val).val j := by
  change Coeff.deleteCoordinate 0 ((weightEquiv w 2) (Z a.val)) j = _
  rw [Coeff.deleteCoordinate_apply_other 0 j hj,weightEquiv_apply]

theorem analyticOnNhd_meanZeroWeightedMap (w : Weight) (Z : Coeff 2 → WeightedCoeff w 2) (η : ℝ)
    (hZ : AnalyticOnNhd ℂ Z (ball (0 : Coeff 2) η)) :
    AnalyticOnNhd ℂ (meanZeroWeightedMap w Z) (ball (0 : DeletedCoeff 2 0) η) := by
  intro a ha
  have hmem : a.val ∈ ball (0 : Coeff 2) η := by
    simpa only [mem_ball_zero_iff,Submodule.norm_coe] using ha
  have hI := ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 0).ker.subtypeL).analyticAt a
  exact ((meanZeroWeightedProjectionCLM w).analyticAt _).comp ((hZ a.val hmem).comp hI)

theorem hasFDerivAt_meanZeroWeightedMap (w : Weight) (Z : Coeff 2 → WeightedCoeff w 2)
    (D : Coeff 2 →L[ℂ] WeightedCoeff w 2) (hZ : HasFDerivAt Z D 0) :
    HasFDerivAt (meanZeroWeightedMap w Z)
      ((meanZeroWeightedProjectionCLM w).comp (D.comp (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 0).ker.subtypeL)) 0 := by
  let I := (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 0).ker.subtypeL
  have hZi : HasFDerivAt Z D (I 0) := by simpa only [map_zero] using hZ
  exact (meanZeroWeightedProjectionCLM w).hasFDerivAt.comp 0 (hZi.comp 0 I.hasFDerivAt)

end NLS.WeightedCoeff
