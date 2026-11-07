import NLS.Articles.KdVKdV2Frequencies.GlobalL2CanonicalFourierRemainder
import NLS.Articles.KdVKdV2Frequencies.OriginalComplexMeanZeroBirkhoffMap

/-! The article's ORIGINAL intrinsic mean-zero Birkhoff map minus its
TRUE weighted Fourier differential is analytic into ORIGINAL h0^(3/2),
on ONE complex neighborhood of the ENTIRE real mean-zero L2 source. -/
noncomputable section
open Set Complex NLS.KdV NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData

def originalL2MeanZeroFourier (D : GlobalRoughAbelianForwardData) :
    complexMeanZeroWeightedSubmodule (Weight.sobolev 0) →L[ℂ] OriginalComplexBirkhoffTarget :=
  (complexMeanZeroWeightedProjection (Weight.sobolev (-1/2))).comp D.originalL2Fourier

theorem originalL2MeanZeroFourier_apply (D : GlobalRoughAbelianForwardData)
    (q : complexMeanZeroWeightedSubmodule (Weight.sobolev 0)) (j : ℤ) :
    (D.originalL2MeanZeroFourier q).val.val j=
      (Real.sqrt (2*(j.natAbs:ℝ)*Real.pi):ℂ)⁻¹*q.val.val j := by
  by_cases hj : j=0
  · subst j
    rw [show (D.originalL2MeanZeroFourier q).val.val 0=0 from (D.originalL2MeanZeroFourier q).property,
      show q.val.val 0=0 from q.property,mul_zero]
  · change (complexMeanZeroWeightedProjection _ (D.originalL2Fourier q)).val.val j=_
    rw [complexMeanZeroWeightedProjection_apply_other _ _ j hj,D.originalL2Fourier_apply]

theorem originalL2MeanZeroFourier_eq_actual_differential (D : GlobalRoughAbelianForwardData) :
    D.originalL2MeanZeroFourier=(fderiv ℂ D.originalMeanZeroMap 0).comp
      (complexMeanZeroSobolevInclusion (by norm_num : (-1:ℝ)≤0)) := by
  apply ContinuousLinearMap.ext
  intro q
  change D.originalL2MeanZeroFourier q=(fderiv ℂ D.originalMeanZeroMap 0)
    (complexMeanZeroSobolevInclusion (by norm_num : (-1:ℝ)≤0) q)
  apply Subtype.ext
  apply Subtype.ext
  funext j
  rw [D.originalL2MeanZeroFourier_apply,D.originalMeanZeroMap_fourier_differential]
  simp only [complexMeanZeroSobolevInclusion_val,WeightedCoeff.sobolevInclusion_apply]

theorem exists_global_l2_mean_zero_fourier_smoothing (D : GlobalRoughAbelianForwardData) :
    ∃ U : Set (complexMeanZeroWeightedSubmodule (Weight.sobolev 0)),IsOpen U ∧
      (∀ q,IsRealPeriodOneHminusOne (originalL2MeanZeroSource q) → q∈U) ∧
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
  obtain ⟨U,hU,hreal,R,hRa,hd,_hloc⟩ := D.exists_global_l2_canonical_fourier_remainder
  have hz (q) (hq : q∈U) : (R q).val 0=0 := by
    rw [(hd q hq).2.2 0,D.signed_zero _ (hd q hq).1,
      show q.val.val 0=0 from q.property,mul_zero,sub_zero]
  let P := complexMeanZeroWeightedProjection (Weight.sobolev (3/2))
  let S := fun q => P (R q)
  have hSa : AnalyticOnNhd ℂ S U := fun q hq => (P.analyticAt _).comp (hRa q hq)
  have hS (q) (hq : q∈U) : (S q).val=R q :=
    WeightedCoeff.meanZeroWeightedLift_projection _ _ (hz q hq)
  have hsource (q) : originalL2MeanZeroSource q=
      (complexMeanZeroSobolevInclusion (by norm_num : (-1:ℝ)≤0) q).val := by
    apply Subtype.ext
    funext j
    rw [originalL2MeanZeroSource_apply,complexMeanZeroSobolevInclusion_val,WeightedCoeff.sobolevInclusion_apply]
  refine ⟨U,hU,hreal,S,hSa,?_,?_⟩
  · intro q hq
    constructor
    · have hF : (fderiv ℂ D.originalMeanZeroMap 0)
          (complexMeanZeroSobolevInclusion (by norm_num : (-1:ℝ)≤0) q)=D.originalL2MeanZeroFourier q := by
        exact (congrArg (fun T => T q) D.originalL2MeanZeroFourier_eq_actual_differential).symm
      apply sub_eq_iff_eq_add.mpr
      rw [hF,add_comm]
      change complexMeanZeroWeightedProjection _
        (D.signed (complexMeanZeroSobolevInclusion (by norm_num : (-1:ℝ)≤0) q).val)=
          D.originalL2MeanZeroFourier q+complexMeanZeroSobolevInclusion _ (S q)
      rw [←hsource q,(hd q hq).2.1,map_add]
      rw [←hS q hq]
      congr 1
      exact complexMeanZeroWeightedProjection_eq_self _ (complexMeanZeroSobolevInclusion _ (S q))
    · intro j
      rw [hS q hq]
      exact (hd q hq).2.2 j
  intro q hq
  obtain ⟨V,hV,hqV,hVU,C,hC,_hSVa,hSb⟩ := exists_bounded_analytic_germ U hU q (hreal q hq) S hSa
  exact ⟨V,hV,hqV,hVU,C+1,by positivity,(fun p hp => (hSb p hp).trans (by linarith))⟩

end NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
