import NLS.KdV.HillUnitRealSourceCoordinates
import NLS.KdV.HillNativePositiveAbelianCoordinates
import NLS.SequenceSpaces.MeanZeroWeightedCoordinates
import NLS.SequenceSpaces.DeletedRealConjugation

/-! # Physical conjugation equivariance of the actual native Abelian germ -/
noncomputable section
open Set Metric Complex
open scoped ComplexConjugate
namespace NLS.KdV

private theorem weighted_physical_fixed (p : RealHillWeightedPotential SpectralWeight.one) :
    periodOneL2Conjugation ((WeightedCoeff.weightIsometry (hillAbelianTargetWeight SpectralWeight.one) 2)
      (hillPhysicalAbelianMap SpectralWeight.one p)) =
      (WeightedCoeff.weightIsometry (hillAbelianTargetWeight SpectralWeight.one) 2)
        (hillPhysicalAbelianMap SpectralWeight.one p) := by
  apply (periodOneL2Conjugation_fixed_iff _).mpr
  intro j
  change (WeightedCoeff.weightEquiv (hillAbelianTargetWeight SpectralWeight.one) 2
    (hillPhysicalAbelianMap SpectralWeight.one p)) (-j) = conj
    ((WeightedCoeff.weightEquiv (hillAbelianTargetWeight SpectralWeight.one) 2
      (hillPhysicalAbelianMap SpectralWeight.one p)) j)
  rw [WeightedCoeff.weightEquiv_apply,WeightedCoeff.weightEquiv_apply,
    (hillPhysicalAbelianMap_real SpectralWeight.one p).2 j,map_mul,conj_ofReal,
    hillAbelianTargetWeight_one_sqrt,hillAbelianTargetWeight_one_sqrt,Int.cast_neg,abs_neg]

theorem hillNativeAbelian_weighted_conjugation
    (η : ℝ) (hη : 0 < η)
    (Z : Coeff 2 → WeightedCoeff (hillAbelianTargetWeight SpectralWeight.one) 2)
    (hZa : AnalyticOnNhd ℂ Z (ball (0 : Coeff 2) η))
    (hphysical : ∀ p : RealHillWeightedPotential SpectralWeight.one,
      SpectralWeight.one.doubleIndex.toCoeff p.val ∈ ball (0 : Coeff 2) η →
      Z (SpectralWeight.one.doubleIndex.toCoeff p.val) = hillPhysicalAbelianMap SpectralWeight.one p) :
    ∀ u ∈ ball (0 : Coeff 2) η,
      (WeightedCoeff.weightIsometry (hillAbelianTargetWeight SpectralWeight.one) 2) (Z (periodOneL2Conjugation u)) =
      periodOneL2Conjugation ((WeightedCoeff.weightIsometry (hillAbelianTargetWeight SpectralWeight.one) 2) (Z u)) := by
  let L := (WeightedCoeff.weightIsometry (hillAbelianTargetWeight SpectralWeight.one) 2).toContinuousLinearEquiv.toContinuousLinearMap
  let T := fun u => L (Z u)
  have hTa : AnalyticOnNhd ℂ T (ball (0 : Coeff 2) η) := fun u hu => (L.analyticAt _).comp (hZa u hu)
  have he := periodOneL2_real_form_identity isOpen_ball (convex_ball (0 : Coeff 2) η).isPreconnected
    (mem_ball_self hη) T (fun u => periodOneL2Conjugation (T (periodOneL2Conjugation u)))
    hTa (analyticOnNhd_periodOneL2_conjugate T η hTa) (by
      intro u hu hJu
      rw [hJu]
      let p := hillUnitRealSourceLift u hJu
      have hp : SpectralWeight.one.doubleIndex.toCoeff p.val = u := hillUnitRealSourceLift_toCoeff u hJu
      have hz : Z u = hillPhysicalAbelianMap SpectralWeight.one p := by
        simpa only [hp] using hphysical p (by simpa only [hp] using hu)
      change L (Z u) = periodOneL2Conjugation (L (Z u))
      rw [hz]
      exact (weighted_physical_fixed p).symm)
  intro u hu
  have h := congrArg periodOneL2Conjugation (he hu)
  change T (periodOneL2Conjugation u) = periodOneL2Conjugation (T u)
  simpa only [periodOneL2Conjugation_involutive] using h.symm

theorem hillNativeAbelian_meanZero_conjugation
    (η : ℝ) (hη : 0 < η)
    (Z : Coeff 2 → WeightedCoeff (hillAbelianTargetWeight SpectralWeight.one) 2)
    (hZa : AnalyticOnNhd ℂ Z (ball (0 : Coeff 2) η))
    (hphysical : ∀ p : RealHillWeightedPotential SpectralWeight.one,
      SpectralWeight.one.doubleIndex.toCoeff p.val ∈ ball (0 : Coeff 2) η →
      Z (SpectralWeight.one.doubleIndex.toCoeff p.val) = hillPhysicalAbelianMap SpectralWeight.one p) :
    ∀ a ∈ ball (0 : DeletedCoeff 2 0) η,
      WeightedCoeff.meanZeroWeightedMap (hillAbelianTargetWeight SpectralWeight.one) Z (deletedL2Conjugation a) =
      deletedL2Conjugation (WeightedCoeff.meanZeroWeightedMap (hillAbelianTargetWeight SpectralWeight.one) Z a) := by
  intro a ha
  have hmem : a.val ∈ ball (0 : Coeff 2) η := by
    simpa only [mem_ball_zero_iff,Submodule.norm_coe] using ha
  have he := hillNativeAbelian_weighted_conjugation η hη Z hZa hphysical a.val hmem
  change Coeff.deleteCoordinateTo 0
    ((WeightedCoeff.weightIsometry (hillAbelianTargetWeight SpectralWeight.one) 2) (Z (periodOneL2Conjugation a.val))) = _
  rw [he]
  exact deleteCoordinateTo_conjugation _

end NLS.KdV
