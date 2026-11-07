import NLS.Articles.KdVConvexity.FourierLebesgueFinitePhaseStrongKdV
import NLS.Dynamics.ContinuousEvolutionDerivativeLimit

/-! # Every H4 physical phase orbit solves KdV in H1

The actual finite-gap solutions converge in C(R,H4). Continuity of the
literal conservative KdV vector H4 -> H1 gives locally uniform H1
convergence of their derivatives, so the differential equation passes
to every H4 initial potential. No finite-support hypothesis remains.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology NLS.KdV
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
open NLS.Articles.KdVConvexity

theorem hasDerivAt_fourierLebesguePhaseEvolution_nativeKdV
    (D : GlobalRoughAbelianForwardData) (B : BasePhysicalFrequencyExtension)
    (q : physicalRealMeanZeroWeightedExponent (Weight.sobolev 4) 2) (t : ℝ) :
    HasDerivAt (fun u : ℝ => WeightedCoeff.sobolevInclusion (by norm_num : (1 : ℝ)≤4)
      (D.fourierLebesguePhaseEvolution B 4 (by norm_num) 2 (by simp) (by norm_num) u q).val)
      (periodOneKdVNativeVector
        (D.fourierLebesguePhaseEvolution B 4 (by norm_num) 2 (by simp) (by norm_num) t q).val) t := by
  let L : physicalRealMeanZeroWeightedExponent (Weight.sobolev 4) 2 →L[ℝ]
      WeightedCoeff (Weight.sobolev 1) 2 :=
    ((WeightedCoeff.sobolevInclusion (by norm_num : (1 : ℝ)≤4)).restrictScalars ℝ).comp
      (physicalRealMeanZeroWeightedExponent (Weight.sobolev 4) 2).subtypeL
  let V : C(physicalRealMeanZeroWeightedExponent (Weight.sobolev 4) 2,
      WeightedCoeff (Weight.sobolev 1) 2) :=
    ⟨fun a => periodOneKdVNativeVector a.val,
      (continuous_iff_continuousAt.mpr (fun a =>
        (analyticAt_periodOneKdVNativeVector a).continuousAt)).comp continuous_subtype_val⟩
  have hfin (N : ℕ) : (Function.support
      (D.fourierLebesgueForward 4 (by norm_num) 2 (by simp) (by norm_num)
        (D.fourierLebesgueFiniteGapApproximation 4 (by norm_num) 2 (by simp) (by norm_num) q N)).val.val).Finite := by
    rw [D.fourierLebesgueFiniteGapApproximation_coordinates]
    exact physicalRealMeanZeroWeightedTruncateExponent_finiteSupport N _
  apply NLS.Dynamics.hasDerivAt_of_continuous_evolution_approximation
    (D.fourierLebesgueTrajectoryMap B 4 (by norm_num) 2 (by simp) (by norm_num)) L V q
    (D.fourierLebesgueFiniteGapApproximation 4 (by norm_num) 2 (by simp) (by norm_num) q)
    (D.tendsto_fourierLebesgueFiniteGapApproximation 4 (by norm_num) 2 (by simp) (by norm_num) q)
  intro N u
  exact D.hasDerivAt_finitePhaseEvolution_nativeKdV B _ (hfin N) u

end NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
