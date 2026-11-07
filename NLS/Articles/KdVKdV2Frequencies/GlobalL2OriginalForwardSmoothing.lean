import NLS.Articles.KdVKdV2Frequencies.GlobalL2MeanZeroFourierSmoothing
import NLS.Articles.KdVKdV2Frequencies.ActualL2MeanZeroDomain
import NLS.ComplexAnalysis.RestrictAnalyticRealNeighborhood

/-! The ORIGINAL map Phi minus its TRUE d_0 Phi has an analytic
h0^(3/2) realization on ONE complex neighborhood of the ENTIRE real L2_0
space inside the SAME true Birkhoff domain, with original local bounds. -/
noncomputable section
open Set Complex NLS.KdV NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData

theorem exists_global_l2_original_forward_smoothing (D : GlobalRoughAbelianForwardData) :
    ∃ U : Set (complexMeanZeroWeightedSubmodule (Weight.sobolev 0)),IsOpen U ∧
      (∀ q,IsRealPeriodOneHminusOne (originalL2MeanZeroSource q) → q∈U) ∧
      U⊆D.originalL2MeanZeroDomain ∧
      ∃ R : complexMeanZeroWeightedSubmodule (Weight.sobolev 0) → complexMeanZeroWeightedSubmodule (Weight.sobolev (3/2)),
        AnalyticOnNhd ℂ R U ∧
        (∀ q∈U,D.originalMeanZeroMap (complexMeanZeroSobolevInclusion (by norm_num : (-1:ℝ)≤0) q)-
            (fderiv ℂ D.originalMeanZeroMap 0) (complexMeanZeroSobolevInclusion (by norm_num : (-1:ℝ)≤0) q)=
            complexMeanZeroSobolevInclusion (by norm_num : (-1/2:ℝ)≤3/2) (R q) ∧
          ∀ j : ℤ,(R q).val.val j=(D.signed (originalL2MeanZeroSource q)).val j-
            (Real.sqrt (2*(j.natAbs:ℝ)*Real.pi):ℂ)⁻¹*q.val.val j) ∧
        ∀ q,IsRealPeriodOneHminusOne (originalL2MeanZeroSource q) →
          ∃ V : Set (complexMeanZeroWeightedSubmodule (Weight.sobolev 0)),IsOpen V ∧ q∈V ∧ V⊆U ∧
            ∃ C : ℝ,0<C ∧ ∀ p∈V,‖R p‖≤C := by
  obtain ⟨U,hU,hreal,R,hRa,hd,hb⟩ := D.exists_global_l2_mean_zero_fourier_smoothing
  obtain ⟨V,hV,hVreal,hVU,hVD⟩ := D.exists_original_l2_domain_refinement U hU hreal
  refine ⟨V,hV,hVreal,hVD,R,hRa.mono hVU,(fun q hq => hd q (hVU hq)),?_⟩
  intro q hq
  obtain ⟨W,hW,hqW,hWU,C,hC,hCb⟩ := hb q hq
  exact ⟨W∩V,hW.inter hV,⟨hqW,hVreal q hq⟩,inter_subset_right,C,hC,(fun p hp => hCb p hp.1)⟩

end NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
