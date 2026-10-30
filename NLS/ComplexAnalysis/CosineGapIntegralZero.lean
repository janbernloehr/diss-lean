import NLS.ComplexAnalysis.CosinePrimitiveEndpointAgreement
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# A vanishing cosine integral from a single-valued gap primitive

Opposite angle sheets have the same spectral point and opposite root
coefficients. Continuity at angle zero therefore identifies the two
endpoint values of the regular angle primitive. Real FTC gives the
full cosine integral, without a reality assumption on either endpoint.
-/

noncomputable section
open Set Metric Complex Filter Topology MeasureTheory
namespace NLS.ComplexAnalysis

/-- A single-valued gap primitive forces its regular cosine numerator to
have zero full integral, without a reality hypothesis on the gap. -/
theorem integral_cosineGapPoint_eq_zero_of_primitive
    (g Q F : ℂ → ℂ) (Ω : Set ℂ) (τ δ A : ℂ)
    (hΩ : IsOpen Ω) (hδ : δ ≠ 0)
    (hgap : segment ℝ (τ-δ) (τ+δ) ⊆ Ω)
    (hg : AnalyticOnNhd ℂ g Ω)
    (hQ : ContinuousOn Q (Ω \ segment ℝ (τ-δ) (τ+δ)))
    (hsq : ∀ z ∈ Ω \ segment ℝ (τ-δ) (τ+δ),
      Q z^2 = (τ-δ-z)*(τ+δ-z))
    (hF : ∀ z ∈ Ω \ segment ℝ (τ-δ) (τ+δ), HasDerivAt F (g z/Q z) z)
    (hA : Tendsto F (𝓝[Ω \ segment ℝ (τ-δ) (τ+δ)] (τ-δ)) (𝓝 A)) :
    (∫ θ in (0:ℝ)..Real.pi, g (cosineGapPoint τ δ (θ:ℂ))) = 0 := by
  obtain ⟨U,H,hU,_,hsegU,hUT,hH,hchart⟩ := exists_cosine_gap_primitive_chart
    g Q F Ω τ δ A hΩ hδ hgap hg hQ hsq hF hA
  have h0 : (0:ℂ) ∈ U := hsegU (left_mem_segment ℝ _ _)
  have hlim : Tendsto (fun y : ℝ => (y:ℂ)*I) (𝓝[>] (0:ℝ)) (𝓝 (0:ℂ)) := by
    simpa using (continuous_ofReal.mul_const I).continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[>] (0:ℝ) ≤ 𝓝 0)
  have hnlim : Tendsto (fun y : ℝ => -((y:ℂ)*I)) (𝓝[>] (0:ℝ)) (𝓝 (0:ℂ)) := by
    simpa using hlim.neg
  have hevent : ∀ᶠ y : ℝ in 𝓝[>] (0:ℝ),
      H ((y:ℂ)*I)+H (-((y:ℂ)*I)) = 2*H (Real.pi:ℂ) := by
    filter_upwards [hlim.eventually (hU.mem_nhds h0),hnlim.eventually (hU.mem_nhds h0),
      self_mem_nhdsWithin] with y hy hny hpos
    have hi : ((y:ℂ)*I).im ≠ 0 := by simpa using (ne_of_gt hpos)
    have hni : (-((y:ℂ)*I)).im ≠ 0 := by simpa using hi
    have hp := hchart _ hy hi
    have hn := hchart _ hny hni
    rw [cosineRootCoefficient_neg] at hn
    have ht : cosineGapPoint τ δ (-((y:ℂ)*I)) = cosineGapPoint τ δ ((y:ℂ)*I) := by
      simp only [cosineGapPoint,Complex.cos_neg]
    rw [ht] at hn
    have hcoefsq := cosineRootCoefficient_sq Q τ δ ((y:ℂ)*I) hδ hi
      (hsq _ ⟨hUT hy,cosineGapPoint_not_mem_segment τ δ _ hδ hi⟩)
    have hcoef : cosineRootCoefficient Q τ δ ((y:ℂ)*I) ≠ 0 := by
      intro hz
      rw [hz] at hcoefsq
      norm_num at hcoefsq
    have heq : cosineRootCoefficient Q τ δ ((y:ℂ)*I) *
        (H ((y:ℂ)*I)+H (-((y:ℂ)*I))-2*H (Real.pi:ℂ)) = 0 := by
      linear_combination hn-hp
    exact sub_eq_zero.mp ((mul_eq_zero.mp heq).resolve_left hcoef)
  have hleft : Tendsto (fun y : ℝ => H ((y:ℂ)*I)+H (-((y:ℂ)*I)))
      (𝓝[>] (0:ℝ)) (𝓝 (H 0+H 0)) :=
    ((hH 0 h0).continuousAt.tendsto.comp hlim).add
      ((hH 0 h0).continuousAt.tendsto.comp hnlim)
  have hright : Tendsto (fun y : ℝ => H ((y:ℂ)*I)+H (-((y:ℂ)*I)))
      (𝓝[>] (0:ℝ)) (𝓝 (2*H (Real.pi:ℂ))) :=
    tendsto_const_nhds.congr' (hevent.mono fun _ h => h.symm)
  have hend : H 0 = H (Real.pi:ℂ) := by
    have he := tendsto_nhds_unique hleft hright
    linear_combination he/2
  have hangle (θ : ℝ) (hθ : θ ∈ Icc 0 Real.pi) : (θ:ℂ) ∈ U := by
    apply hsegU
    have ht : θ/Real.pi ∈ Icc (0:ℝ) 1 :=
      ⟨div_nonneg hθ.1 Real.pi_pos.le,(div_le_one Real.pi_pos).mpr hθ.2⟩
    convert lineMap_mem_segment ℝ (0:ℂ) (Real.pi:ℂ) ht using 1
    simp only [AffineMap.lineMap_apply_module,Complex.real_smul,mul_zero,zero_add,Complex.ofReal_div]
    field_simp
  have hcont : ContinuousOn (fun θ : ℝ => H (θ:ℂ)) (Icc 0 Real.pi) :=
    (show ContinuousOn H U from fun θ hθ => (hH θ hθ).continuousAt.continuousWithinAt).comp
      continuous_ofReal.continuousOn hangle
  have hgcont : ContinuousOn (fun θ : ℝ => g (cosineGapPoint τ δ (θ:ℂ))) (Icc 0 Real.pi) := by
    apply hg.continuousOn.comp (by unfold cosineGapPoint; fun_prop)
    intro θ hθ
    exact hUT (hangle θ hθ)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le Real.pi_pos.le hcont
    (fun θ hθ => (hH _ (hangle θ (Ioo_subset_Icc_self hθ))).comp_ofReal)
    (hgcont.intervalIntegrable_of_Icc Real.pi_pos.le)
  simpa only [ofReal_zero,hend,sub_self] using hi

end NLS.ComplexAnalysis
