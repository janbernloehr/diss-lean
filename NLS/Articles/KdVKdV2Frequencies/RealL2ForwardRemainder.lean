import NLS.Articles.KdVKdV2Frequencies.CanonicalL2ForwardReality
import NLS.Articles.KdVKdV2Frequencies.OriginalNativeFourierEquivs
import NLS.SequenceSpaces.PhysicalRealMeanZeroProjection
import NLS.ComplexAnalysis.AnalyticRealLinearTransport

/-! The actual canonical stronger forward remainder, in ORIGINAL real
mean-zero L2 and h^(1+1/2) Banach spaces, is globally real analytic. -/
noncomputable section
open Set Complex NLS.KdV NLS.ComplexAnalysis
open scoped ENNReal ComplexConjugate
namespace NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData

theorem original_l2_physical_source_real
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev 0)) :
    IsRealPeriodOneHminusOne (originalL2MeanZeroSource (physicalRealToComplexMeanZeroWeighted (Weight.sobolev 0) q)) := by
  intro j
  simpa only [originalL2MeanZeroSource_apply,physicalRealToComplexMeanZeroWeighted_val] using q.property.1 j

theorem originalNativeBirkhoff_l2_coefficient (D : GlobalRoughAbelianForwardData)
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev 0)) (j : ℤ) :
    (D.originalNativeBirkhoff 0 (by norm_num) q).val.val j=
      (D.signed (originalL2MeanZeroSource (physicalRealToComplexMeanZeroWeighted (Weight.sobolev 0) q))).val j := by
  let a := physicalRealMeanZeroSobolevToComplex (by norm_num : (-1:ℝ)≤0) q
  have ha : a=complexMeanZeroSobolevInclusion (by norm_num : (-1:ℝ)≤0)
      (physicalRealToComplexMeanZeroWeighted (Weight.sobolev 0) q) := rfl
  have h := D.originalNativeBirkhoff_restriction 0 (by norm_num) q
  have hval := D.originalMeanZeroMap_val a (D.originalNativeBirkhoff_mem_domain 0 (by norm_num) q)
  have hsrc : a.val=originalL2MeanZeroSource (physicalRealToComplexMeanZeroWeighted (Weight.sobolev 0) q) := by
    rw [ha,←originalL2MeanZeroSource_eq_intrinsic]
  have hc := congrArg (fun z : OriginalComplexBirkhoffTarget => z.val.val j) h
  rw [hval,hsrc] at hc
  simpa only [physicalRealMeanZeroSobolevToComplex_val,WeightedCoeff.sobolevInclusion_apply] using hc.symm

theorem exists_real_l2_forward_remainder (D : GlobalRoughAbelianForwardData) :
    ∃ R : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev 0) →
        physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (1+1/2)),
      AnalyticOnNhd ℝ R univ ∧ ∀ q j,(R q).val.val j=
        (D.originalNativeBirkhoff 0 (by norm_num) q).val.val j-
          (Real.sqrt (2*(j.natAbs:ℝ)*Real.pi):ℂ)⁻¹*q.val.val j := by
  obtain ⟨U,_hU,hreal,_hdom,S,hSa,hd,hsreal,_hb⟩ := D.exists_global_l2_original_forward_smoothing_real
  let J := physicalRealToComplexMeanZeroWeighted (Weight.sobolev 0)
  let Q : complexMeanZeroWeightedSubmodule (Weight.sobolev (3/2)) →L[ℝ]
      WeightedCoeff (Weight.sobolev (1+1/2)) 2 :=
    ((WeightedCoeff.sobolevInclusion (by norm_num : (1+1/2:ℝ)≤3/2)).restrictScalars ℝ).comp
      ((complexMeanZeroWeightedSubmodule (Weight.sobolev (3/2))).subtypeL.restrictScalars ℝ)
  let P := (physicalRealMeanZeroProjection (Weight.sobolev (1+1/2)) (Weight.sobolev_neg _)).comp Q
  let R := fun q => P (S (J q))
  have hRa : AnalyticOnNhd ℝ R univ := fun q _ =>
    analyticAt_real_linear_transport J P S q
      (hSa (J q) (hreal (J q) (original_l2_physical_source_real q)))
  have hrec (q) : (R q).val=Q (S (J q)) := by
    have hQr : Q (S (J q))∈physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (1+1/2)) := by
      constructor
      · intro j
        change (WeightedCoeff.sobolevInclusion (by norm_num : (1+1/2:ℝ)≤3/2) (S (J q)).val).val (-j)=
          conj ((WeightedCoeff.sobolevInclusion (by norm_num : (1+1/2:ℝ)≤3/2) (S (J q)).val).val j)
        simp only [WeightedCoeff.sobolevInclusion_apply]
        exact hsreal (J q) (original_l2_physical_source_real q) j
      · change (WeightedCoeff.sobolevInclusion (by norm_num : (1+1/2:ℝ)≤3/2) (S (J q)).val).val 0=0
        rw [WeightedCoeff.sobolevInclusion_apply]
        exact (S (J q)).property
    have h := physicalRealMeanZeroProjection_coe (Weight.sobolev (1+1/2)) (Weight.sobolev_neg _)
      (⟨Q (S (J q)),hQr⟩ : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (1+1/2)))
    exact congrArg Subtype.val h
  refine ⟨R,hRa,?_⟩
  intro q j
  rw [hrec]
  change (WeightedCoeff.sobolevInclusion (by norm_num : (1+1/2:ℝ)≤3/2) (S (J q)).val).val j=_
  rw [WeightedCoeff.sobolevInclusion_apply,D.originalNativeBirkhoff_l2_coefficient]
  simpa only [J,physicalRealToComplexMeanZeroWeighted_val] using
    (hd (J q) (hreal (J q) (original_l2_physical_source_real q))).2 j

end NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
