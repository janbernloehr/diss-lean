import NLS.Articles.KdVKdV2Frequencies.RealL2ForwardRemainder
import NLS.SequenceSpaces.PhysicalMeanZeroFourierInverse
import NLS.SequenceSpaces.PhysicalRealMeanZeroSobolevInclusion
import NLS.ComplexAnalysis.AnalyticInverseSmoothing
import NLS.ComplexAnalysis.BoundedAnalyticGerm

/-! The SAME actual original native inverse minus its TRUE canonical
Fourier inverse has an ORIGINAL real mean-zero H1 analytic realization
on the ENTIRE real h0^(1/2) target, with positive locally uniform bounds. -/
noncomputable section
open Set Complex NLS.KdV NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData

theorem exists_original_l2_inverse_smoothing (D : GlobalRoughAbelianForwardData) :
    ∃ F : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev 0) ≃L[ℝ]
        physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (0+1/2)),
      (F : _ →L[ℝ] _) = fderiv ℝ (fun q => D.originalNativeBirkhoff 0 (by norm_num) q) 0 ∧
      (F.symm : _ →L[ℝ] _) = fderiv ℝ (fun z => (D.originalNativeBirkhoff 0 (by norm_num)).symm z) 0 ∧
      (∀ q j,(F q).val.val j=(Real.sqrt (2*(j.natAbs:ℝ)*Real.pi):ℂ)⁻¹*q.val.val j) ∧
      (∀ z j,(F.symm z).val.val j=(Real.sqrt (2*(j.natAbs:ℝ)*Real.pi):ℂ)*z.val.val j) ∧
      ∃ R : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (0+1/2)) →
          physicalRealMeanZeroWeightedSubmodule (Weight.sobolev 1),
        AnalyticOnNhd ℝ R univ ∧
        (∀ z,(D.originalNativeBirkhoff 0 (by norm_num)).symm z-F.symm z=
          physicalRealMeanZeroSobolevInclusion (by norm_num : (0:ℝ)≤1) (R z)) ∧
        (∀ z j,(R z).val.val j=((D.originalNativeBirkhoff 0 (by norm_num)).symm z).val.val j-
          (Real.sqrt (2*(j.natAbs:ℝ)*Real.pi):ℂ)*z.val.val j) ∧
        ∀ z,∃ V : Set (physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (0+1/2))),
          IsOpen V ∧ z∈V ∧ ∃ C : ℝ,0<C ∧ ∀ w∈V,‖R w‖≤C := by
  obtain ⟨F,hF,hFi,hFc⟩ := D.exists_original_native_fourier_equiv 0 (by norm_num)
  obtain ⟨L,hL,_hLi,hLc⟩ := D.exists_original_native_fourier_equiv 1 (by norm_num)
  let I := physicalRealMeanZeroSobolevInclusion (by norm_num : (0:ℝ)≤1)
  let J := physicalRealMeanZeroSobolevInclusion (by norm_num : (0+1/2:ℝ)≤1+1/2)
  have hc (q) : J (L q)=F (I q) := by
    apply Subtype.ext
    apply Subtype.ext
    funext j
    simp only [I,J,physicalRealMeanZeroSobolevInclusion_coefficient,hFc,hLc]
  obtain ⟨R,hRa,hRc⟩ := D.exists_real_l2_forward_remainder
  have hf (q) : D.originalNativeBirkhoff 0 (by norm_num) q=F q+J (R q) := by
    apply Subtype.ext
    apply Subtype.ext
    funext j
    change (D.originalNativeBirkhoff 0 (by norm_num) q).val.val j=
      (F q).val.val j+(J (R q)).val.val j
    simp only [J,physicalRealMeanZeroSobolevInclusion_coefficient,hFc]
    linear_combination -(hRc q j)
  obtain ⟨S,hSa,hs⟩ := exists_analytic_inverse_smoothing I J F L hc
    (D.originalNativeBirkhoff 0 (by norm_num)) (D.originalNativeBirkhoff_symm_analytic 0 (by norm_num)) R hRa hf
  have hFic (z) (j) : (F.symm z).val.val j=(Real.sqrt (2*(j.natAbs:ℝ)*Real.pi):ℂ)*z.val.val j :=
    physical_mean_zero_fourier_inverse_coefficient _ _ F hFc z j
  refine ⟨F,hF,hFi,hFc,hFic,S,hSa,hs,?_,?_⟩
  · intro z j
    have h := congrArg (fun q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev 0) => q.val.val j) (hs z)
    simp only [I,Submodule.coe_sub,WeightedCoeff.sub_val,physicalRealMeanZeroSobolevInclusion_coefficient,hFic] at h
    exact h.symm
  intro z
  obtain ⟨V,hV,hzV,_hVU,C,hC,_hSVa,hSb⟩ := exists_bounded_analytic_germ univ isOpen_univ z (mem_univ _) S hSa
  exact ⟨V,hV,hzV,C+1,by positivity,(fun w hw => (hSb w hw).trans (by linarith))⟩

end NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
