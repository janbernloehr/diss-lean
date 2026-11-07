import NLS.Articles.KdVKdV2Frequencies.GlobalL2OriginalForwardSmoothing

/-! The canonical stronger remainder retains the ACTUAL physical real
form. The real mean-zero source maps into real mean-zero h^(3/2), in the
inherited original norms, rather than just its complexification. -/
noncomputable section
open Set Complex NLS.KdV
open scoped ENNReal ComplexConjugate
namespace NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData

theorem original_l2_forward_remainder_real (D : GlobalRoughAbelianForwardData)
    (q : complexMeanZeroWeightedSubmodule (Weight.sobolev 0))
    (hr : IsRealPeriodOneHminusOne (originalL2MeanZeroSource q))
    (r : complexMeanZeroWeightedSubmodule (Weight.sobolev (3/2)))
    (hc : ∀ j : ℤ,r.val.val j=(D.signed (originalL2MeanZeroSource q)).val j-
      (Real.sqrt (2*(j.natAbs:ℝ)*Real.pi):ℂ)⁻¹*q.val.val j) :
    ∀ j : ℤ,r.val.val (-j)=conj (r.val.val j) := by
  intro j
  have hq : q.val.val (-j)=conj (q.val.val j) := by
    simpa only [originalL2MeanZeroSource_apply] using hr j
  rw [hc (-j),hc j,D.signed_real _ hr j]
  simp only [Int.natAbs_neg,hq,map_sub,map_mul,map_inv₀,conj_ofReal]

theorem exists_global_l2_original_forward_smoothing_real (D : GlobalRoughAbelianForwardData) :
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
        (∀ q,IsRealPeriodOneHminusOne (originalL2MeanZeroSource q) →
          ∀ j : ℤ,(R q).val.val (-j)=conj ((R q).val.val j)) ∧
        ∀ q,IsRealPeriodOneHminusOne (originalL2MeanZeroSource q) →
          ∃ V : Set (complexMeanZeroWeightedSubmodule (Weight.sobolev 0)),IsOpen V ∧ q∈V ∧ V⊆U ∧
            ∃ C : ℝ,0<C ∧ ∀ p∈V,‖R p‖≤C := by
  obtain ⟨U,hU,hreal,hdom,R,hRa,hd,hb⟩ := D.exists_global_l2_original_forward_smoothing
  exact ⟨U,hU,hreal,hdom,R,hRa,hd,(fun q hq => D.original_l2_forward_remainder_real q hq _ (hd q (hreal q hq)).2),hb⟩

end NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
