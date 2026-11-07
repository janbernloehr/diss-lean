import NLS.Articles.KdVKdV2Frequencies.GlobalL2FixedFourierRemainder
import NLS.Articles.KdVKdV2Frequencies.ActualL2FourierLinearization
import NLS.SequenceSpaces.SignedFourierCoreDerivative
import NLS.ComplexAnalysis.AnalyticRemainderLinearization
import NLS.ComplexAnalysis.AnalyticDomainPullback
import NLS.ComplexAnalysis.BoundedAnalyticGerm

/-! The SAME actual forward map minus its TRUE canonical weighted
Fourier linearization has ONE analytic raw h^(3/2) realization around the
ENTIRE real ORIGINAL mean-zero L2 space, with locally uniform bounds. -/
noncomputable section
open Set Complex NLS.KdV NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData

theorem exists_global_l2_canonical_fourier_remainder (D : GlobalRoughAbelianForwardData) :
    ∃ U : Set (complexMeanZeroWeightedSubmodule (Weight.sobolev 0)),IsOpen U ∧
      (∀ q,IsRealPeriodOneHminusOne (originalL2MeanZeroSource q) → q∈U) ∧
      ∃ R : complexMeanZeroWeightedSubmodule (Weight.sobolev 0) → WeightedCoeff (Weight.sobolev (3/2)) 2,
        AnalyticOnNhd ℂ R U ∧
        (∀ q∈U,originalL2MeanZeroSource q∈D.domain ∧
          D.signed (originalL2MeanZeroSource q)=D.originalL2Fourier q+
            WeightedCoeff.sobolevInclusion (by norm_num : (-1/2:ℝ)≤3/2) (R q) ∧
          ∀ j : ℤ,(R q).val j=(D.signed (originalL2MeanZeroSource q)).val j-
            (Real.sqrt (2*(j.natAbs:ℝ)*Real.pi):ℂ)⁻¹*q.val.val j) ∧
        ∀ q,IsRealPeriodOneHminusOne (originalL2MeanZeroSource q) →
          ∃ V : Set (complexMeanZeroWeightedSubmodule (Weight.sobolev 0)),IsOpen V ∧ q∈V ∧ V⊆U ∧
            ∃ C : ℝ,0<C ∧ ∀ p∈V,‖R p‖≤C := by
  obtain ⟨W,hW,hreal,A0,R0,hA0a,hR0a,hd,_hloc⟩ := D.exists_global_l2_fixed_fourier_remainder
  let L := originalL2MeanZeroNativeInclusion
  let U := L ⁻¹' W
  have hU : IsOpen U := hW.preimage L.continuous
  have hmem (q) (hq : IsRealPeriodOneHminusOne (originalL2MeanZeroSource q)) : q∈U := hreal (L q) hq
  have h0 : (0 : complexMeanZeroWeightedSubmodule (Weight.sobolev 0))∈U := hmem 0 (by
    rw [map_zero]
    intro j;simp)
  let A := fun q => A0 (L q)
  let R := fun q => R0 (L q)
  have hAa : AnalyticOnNhd ℂ A U := analyticOnNhd_clm_preimage L A0 W hA0a
  have hRa : AnalyticOnNhd ℂ R U := analyticOnNhd_clm_preimage L R0 W hR0a
  let DA := fderiv ℂ A 0
  let DR := fderiv ℂ R 0
  have hAd : HasFDerivAt A DA 0 := (hAa 0 h0).differentiableAt.hasFDerivAt
  have hRd : HasFDerivAt R DR 0 := (hRa 0 h0).differentiableAt.hasFDerivAt
  have hAe : ∀ q∈U,A q=DA q := by
    apply WeightedCoeff.signed_fourier_core_eq_derivative (Weight.sobolev 0) (Weight.sobolev (1-1/2))
      (complexMeanZeroWeightedSubmodule (Weight.sobolev 0)).subtypeL U hU h0 A DA hAd D.fixedFourierSigns
      (fun n => (Real.sqrt (2*Real.pi*(n:ℝ)):ℂ)⁻¹)
    intro q hq
    simpa only [A,L,originalL2MeanZeroNativeInclusion_apply,Submodule.subtypeL_apply] using (hd (L q) hq).2.2
  let I : WeightedCoeff (Weight.sobolev (1-1/2)) 2 →L[ℂ] WeightedCoeff (Weight.sobolev (-1/2)) 2 :=
    WeightedCoeff.sobolevInclusion (by norm_num)
  let J : WeightedCoeff (Weight.sobolev (2-1/2)) 2 →L[ℂ] WeightedCoeff (Weight.sobolev (-1/2)) 2 :=
    WeightedCoeff.sobolevInclusion (by norm_num)
  have hY : ∀ q∈U,D.signed (originalL2MeanZeroSource q)=I (A q)+J (R q) := by
    intro q hq
    exact (hd (L q) hq).2.1
  obtain ⟨S,hSa,hs⟩ := exists_analytic_remainder_at_true_linearization U hU h0 A R
    (fun q => D.signed (originalL2MeanZeroSource q)) I J DA DR D.originalL2Fourier hAd hRd
    D.hasFDerivAt_original_l2_signed_at_zero hRa hAe hY
  let Q : WeightedCoeff (Weight.sobolev (2-1/2)) 2 →L[ℂ] WeightedCoeff (Weight.sobolev (3/2)) 2 :=
    WeightedCoeff.sobolevInclusion (by norm_num)
  let T := fun q => Q (S q)
  have hTa : AnalyticOnNhd ℂ T U := fun q hq => (Q.analyticAt _).comp (hSa q hq)
  have hT (q) (hq : q∈U) : D.signed (originalL2MeanZeroSource q)=D.originalL2Fourier q+
      WeightedCoeff.sobolevInclusion (by norm_num : (-1/2:ℝ)≤3/2) (T q) := by
    rw [hs q hq]
    congr 1
    apply Subtype.ext
    funext j
    simp only [J,T,Q,WeightedCoeff.sobolevInclusion_apply]
  refine ⟨U,hU,hmem,T,hTa,?_,?_⟩
  · intro q hq
    refine ⟨(hd (L q) hq).1,hT q hq,?_⟩
    intro j
    have h := congrArg (fun z : WeightedCoeff (Weight.sobolev (-1/2)) 2 => z.val j) (hT q hq)
    simp only [WeightedCoeff.add_val,WeightedCoeff.sobolevInclusion_apply,D.originalL2Fourier_apply] at h
    linear_combination -h
  intro q hq
  obtain ⟨V,hV,hqV,hVU,C,hC,_hTVa,hTb⟩ := exists_bounded_analytic_germ U hU q (hmem q hq) T hTa
  exact ⟨V,hV,hqV,hVU,C+1,by positivity,(fun p hp => (hTb p hp).trans (by linarith))⟩

end NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
