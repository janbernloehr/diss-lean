import NLS.ComplexAnalysis.CosinePrimitiveEndpointAgreement
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic

/-!
# Continuing a normalized gap primitive onto a regular sheet

The cosine primitive extends across real angles. At a noncritical angle
the analytic inverse of the cosine coordinate transfers it to a spectral
neighborhood. A prescribed regular square root fixes the coefficient
there. The resulting primitive matches the exterior normalized primitive
with the exact ratio of the two square-root sheets.
-/

noncomputable section
open Set Metric Complex Filter Topology
namespace NLS.ComplexAnalysis

/-- At a regular angle on the real gap interval, the normalized exterior
primitive continues analytically onto any analytic sheet of the endpoint
polynomial. Its exterior value is multiplied by the ratio of the original
and prescribed roots, so the statement includes either terminal sign. -/
theorem exists_cosine_gap_regular_sheet_primitive
    (g Q F R : ℂ → ℂ) (Ω Λ : Set ℂ) (τ δ A e : ℂ)
    (hΩ : IsOpen Ω) (hδ : δ ≠ 0)
    (hgap : segment ℝ (τ-δ) (τ+δ) ⊆ Ω)
    (hg : AnalyticOnNhd ℂ g Ω)
    (hQ : ContinuousOn Q (Ω \ segment ℝ (τ-δ) (τ+δ)))
    (hsq : ∀ z ∈ Ω \ segment ℝ (τ-δ) (τ+δ),
      Q z^2 = (τ-δ-z)*(τ+δ-z))
    (hF : ∀ z ∈ Ω \ segment ℝ (τ-δ) (τ+δ), HasDerivAt F (g z/Q z) z)
    (hA : Tendsto F (𝓝[Ω \ segment ℝ (τ-δ) (τ+δ)] (τ-δ)) (𝓝 A))
    (he : e ∈ segment ℝ (0:ℂ) (Real.pi:ℂ)) (hsin : Complex.sin e ≠ 0)
    (hΛ : IsOpen Λ) (heΛ : cosineGapPoint τ δ e ∈ Λ)
    (hR : AnalyticOnNhd ℂ R Λ)
    (hRsq : ∀ z ∈ Λ, R z^2 = (τ-δ-z)*(τ+δ-z)) :
    ∃ B : Set ℂ, ∃ P : ℂ → ℂ,
      IsOpen B ∧ cosineGapPoint τ δ e ∈ B ∧ B ⊆ Ω ∩ Λ ∧
      AnalyticOnNhd ℂ P B ∧ (∀ z ∈ B, HasDerivAt P (g z/R z) z) ∧
      ∀ z ∈ B, z ∉ segment ℝ (τ-δ) (τ+δ) →
        P z = (Q z/R z)*(F z-A) := by
  obtain ⟨U,H,hU,_hconv,hsegU,hUT,hH,hchart⟩ := exists_cosine_gap_primitive_chart
    g Q F Ω τ δ A hΩ hδ hgap hg hQ hsq hF hA
  let T := cosineGapPoint τ δ
  have heU : e ∈ U := hsegU he
  have hTcont : Continuous T := by
    change Continuous (fun θ : ℂ => τ+δ*Complex.cos θ)
    fun_prop
  have hTa : AnalyticAt ℂ T e :=
    analyticAt_const.add (analyticAt_const.mul Complex.analyticAt_cos)
  have hTne : deriv T e ≠ 0 := by
    rw [(hasDerivAt_cosineGapPoint τ δ e).deriv]
    exact mul_ne_zero (neg_ne_zero.mpr hδ) hsin
  let inv := hTa.hasStrictDerivAt.localInverse T (deriv T e) e hTne
  have hinva : AnalyticAt ℂ inv (T e) := hTa.analyticAt_localInverse hTne
  have hinve : inv (T e) = e := HasStrictFDerivAt.localInverse_apply_image ..
  have hinvid : ∀ᶠ z in 𝓝 (T e), T (inv z) = z :=
    HasStrictDerivAt.eventually_right_inverse ..
  have hallowed : U ∩ (T ⁻¹' Λ) ∩ {θ : ℂ | Complex.sin θ ≠ 0} ∈ 𝓝 e :=
    inter_mem (inter_mem (hU.mem_nhds heU) ((hΛ.preimage hTcont).mem_nhds heΛ))
      ((isOpen_ne.preimage Complex.continuous_sin).mem_nhds hsin)
  obtain ⟨ρ,hρ,hSsub⟩ := Metric.mem_nhds_iff.mp hallowed
  let S := ball e ρ
  have heS : e ∈ S := mem_ball_self hρ
  have hcoef : ∀ θ ∈ S, cosineRootCoefficient R τ δ θ = cosineRootCoefficient R τ δ e :=
    cosineRootCoefficient_eq_on_connected_of_sin_ne_zero R τ δ S hδ
      (convex_ball e ρ).isPreconnected (fun θ hθ => (hSsub hθ).2)
      (hR.continuousOn.comp hTcont.continuousOn (fun θ hθ => (hSsub hθ).1.2))
      (fun θ hθ => hRsq _ (hSsub hθ).1.2) e heS
  have hHanalytic : AnalyticOnNhd ℂ H U :=
    (show DifferentiableOn ℂ H U from fun θ hθ =>
      (hH θ hθ).differentiableAt.differentiableWithinAt).analyticOnNhd hU
  have hinvS : ∀ᶠ z in 𝓝 (T e), inv z ∈ S := by
    have ht := hinva.continuousAt.tendsto
    rw [hinve] at ht
    exact ht.eventually (ball_mem_nhds e hρ)
  have hgood : ∀ᶠ z in 𝓝 (T e),
      AnalyticAt ℂ inv z ∧ inv z ∈ S ∧ T (inv z) = z ∧ z ∈ Ω ∩ Λ :=
    hinva.eventually_analyticAt.and (hinvS.and (hinvid.and
      (inter_mem (hΩ.mem_nhds (hUT heU)) (hΛ.mem_nhds heΛ))))
  obtain ⟨B,hBsub,hB,hbase⟩ := _root_.mem_nhds_iff.mp hgood
  let C := cosineRootCoefficient R τ δ e
  let P : ℂ → ℂ := fun z => C*(H (inv z)-H (Real.pi:ℂ))
  have hRne (z : ℂ) (hz : z ∈ B) : R z ≠ 0 := by
    have hs : R z^2 = -(δ^2*Complex.sin (inv z)^2) :=
      (hRsq z (hBsub hz).2.2.2.2).trans (by
        have hzT : cosineGapPoint τ δ (inv z) = z := (hBsub hz).2.2.1
        simpa only [hzT] using cosineGapPoint_endpoint_factor τ δ (inv z))
    intro h
    rw [h,zero_pow (by norm_num : 2 ≠ 0)] at hs
    exact (neg_ne_zero.mpr (mul_ne_zero (pow_ne_zero 2 hδ)
      (pow_ne_zero 2 (hSsub (hBsub hz).2.1).2))) hs.symm
  refine ⟨B,P,hB,hbase,fun z hz => (hBsub hz).2.2.2,?_,?_,?_⟩
  · intro z hz
    exact analyticAt_const.mul (((hHanalytic _ (hSsub (hBsub hz).2.1).1.1).comp
      (x := z) (hBsub hz).1).sub analyticAt_const)
  · intro z hz
    have hi := (hBsub hz).1.differentiableAt.hasDerivAt
    have ht := (hasDerivAt_cosineGapPoint τ δ (inv z)).comp z hi
    have heq : (fun w => T (inv w)) =ᶠ[𝓝 z] id := by
      filter_upwards [hB.mem_nhds hz] with w hw
      exact (hBsub hw).2.2.1
    have hmul : (-δ*Complex.sin (inv z))*deriv inv z = 1 :=
      (ht.congr_of_eventuallyEq heq.symm).unique (hasDerivAt_id z)
    have hP := (((hH _ (hSsub (hBsub hz).2.1).1.1).comp z hi).sub_const
      (H (Real.pi:ℂ))).const_mul C
    convert hP using 1 <;> try rfl
    dsimp only [C]
    rw [← hcoef _ (hBsub hz).2.1]
    dsimp only [cosineRootCoefficient]
    have hzT : cosineGapPoint τ δ (inv z) = z := (hBsub hz).2.2.1
    rw [hzT]
    field_simp [hRne z hz]
    linear_combination -g z*hmul
  · intro z hz hcut
    have him : (inv z).im ≠ 0 := by
      intro h
      have hi : inv z = ((inv z).re:ℂ) := by
        apply Complex.ext <;> simp [h]
      apply hcut
      rw [← (hBsub hz).2.2.1,hi]
      exact cosineGapPoint_real_mem_segment τ δ _
    have hQne : Q z ≠ 0 := by
      have hs : Q z^2 = -(δ^2*Complex.sin (inv z)^2) :=
        (hsq z ⟨(hBsub hz).2.2.2.1,hcut⟩).trans (by
          have hzT : cosineGapPoint τ δ (inv z) = z := (hBsub hz).2.2.1
          simpa only [hzT] using cosineGapPoint_endpoint_factor τ δ (inv z))
      intro h
      rw [h,zero_pow (by norm_num : 2 ≠ 0)] at hs
      exact (neg_ne_zero.mpr (mul_ne_zero (pow_ne_zero 2 hδ)
        (pow_ne_zero 2 (hSsub (hBsub hz).2.1).2))) hs.symm
    have hzT : cosineGapPoint τ δ (inv z) = z := (hBsub hz).2.2.1
    have hfz : F z-A = cosineRootCoefficient Q τ δ (inv z)*(H (inv z)-H (Real.pi:ℂ)) := by
      simpa only [hzT] using hchart _ (hSsub (hBsub hz).2.1).1.1 him
    dsimp only [P,C]
    rw [← hcoef _ (hBsub hz).2.1,hfz]
    dsimp only [cosineRootCoefficient]
    rw [hzT]
    field_simp [hQne,hRne z hz]

/-- The spectral-point version needs no supplied cosine coordinate.
Every point of the cut except its endpoints admits the continuation. -/
theorem exists_gap_interior_regular_sheet_primitive
    (g Q F R : ℂ → ℂ) (Ω Λ : Set ℂ) (τ δ A b : ℂ)
    (hΩ : IsOpen Ω) (hδ : δ ≠ 0)
    (hgap : segment ℝ (τ-δ) (τ+δ) ⊆ Ω)
    (hg : AnalyticOnNhd ℂ g Ω)
    (hQ : ContinuousOn Q (Ω \ segment ℝ (τ-δ) (τ+δ)))
    (hsq : ∀ z ∈ Ω \ segment ℝ (τ-δ) (τ+δ),
      Q z^2 = (τ-δ-z)*(τ+δ-z))
    (hF : ∀ z ∈ Ω \ segment ℝ (τ-δ) (τ+δ), HasDerivAt F (g z/Q z) z)
    (hA : Tendsto F (𝓝[Ω \ segment ℝ (τ-δ) (τ+δ)] (τ-δ)) (𝓝 A))
    (hb : b ∈ segment ℝ (τ-δ) (τ+δ)) (hl : b ≠ τ-δ) (hr : b ≠ τ+δ)
    (hΛ : IsOpen Λ) (hbΛ : b ∈ Λ)
    (hR : AnalyticOnNhd ℂ R Λ)
    (hRsq : ∀ z ∈ Λ, R z^2 = (τ-δ-z)*(τ+δ-z)) :
    ∃ B : Set ℂ, ∃ P : ℂ → ℂ,
      IsOpen B ∧ b ∈ B ∧ B ⊆ Ω ∩ Λ ∧
      AnalyticOnNhd ℂ P B ∧ (∀ z ∈ B, HasDerivAt P (g z/R z) z) ∧
      ∀ z ∈ B, z ∉ segment ℝ (τ-δ) (τ+δ) →
        P z = (Q z/R z)*(F z-A) := by
  obtain ⟨e,he,hsin,hpoint⟩ := exists_cosineGapPoint_regular_angle τ δ b hb hl hr
  simpa only [hpoint] using exists_cosine_gap_regular_sheet_primitive
    g Q F R Ω Λ τ δ A e hΩ hδ hgap hg hQ hsq hF hA he hsin hΛ
    (hpoint.symm ▸ hbΛ) hR hRsq

end NLS.ComplexAnalysis
