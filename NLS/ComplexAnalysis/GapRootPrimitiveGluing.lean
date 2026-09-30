import NLS.ComplexAnalysis.CosinePrimitiveSheetContinuation
import NLS.ComplexAnalysis.DensePrimitiveGluing

/-!
# Gluing an endpoint-normalized gap primitive onto any regular root sheet

An analytic numerator divided by the canonical endpoint root has a
single-valued exterior primitive. Its left endpoint limit normalizes
the cosine continuations across the cut. These glue onto the whole
regular domain of any analytic root of the same endpoint polynomial.
-/

noncomputable section
open Set Filter Topology Complex
namespace NLS.ComplexAnalysis

theorem exists_glued_gap_regular_sheet_primitive
    (g Q F R : ℂ → ℂ) (Ω Λ : Set ℂ) (τ δ A : ℂ)
    (hΩ : IsOpen Ω) (hΛ : IsOpen Λ) (hδ : δ ≠ 0)
    (hgap : segment ℝ (τ-δ) (τ+δ) ⊆ Ω)
    (hg : AnalyticOnNhd ℂ g Ω)
    (hQ : ContinuousOn Q (Ω \ segment ℝ (τ-δ) (τ+δ)))
    (hsq : ∀ z ∈ Ω \ segment ℝ (τ-δ) (τ+δ), Q z^2 = (τ-δ-z)*(τ+δ-z))
    (hF : ∀ z ∈ Ω \ segment ℝ (τ-δ) (τ+δ), HasDerivAt F (g z/Q z) z)
    (hA : Tendsto F (𝓝[Ω \ segment ℝ (τ-δ) (τ+δ)] (τ-δ)) (𝓝 A))
    (hR : AnalyticOnNhd ℂ R Λ) (hRne : ∀ z ∈ Λ, R z ≠ 0)
    (hRsq : ∀ z ∈ Λ, R z^2 = (τ-δ-z)*(τ+δ-z)) :
    ∃ E : ℂ → ℂ, AnalyticOnNhd ℂ E (Ω ∩ Λ) ∧
      (∀ z ∈ Ω ∩ Λ, HasDerivAt E (g z/R z) z) ∧
      EqOn E (rootRatioPrimitive Q R F A) ((Ω ∩ Λ) \ segment ℝ (τ-δ) (τ+δ)) ∧
      ∀ B : Set ℂ, ∀ P : ℂ → ℂ, IsOpen B → B ⊆ Ω ∩ Λ →
        ContinuousOn P B →
        EqOn P (rootRatioPrimitive Q R F A) (B \ segment ℝ (τ-δ) (τ+δ)) → EqOn E P B := by
  apply exists_glued_normalized_root_primitive g Q R F Ω Λ
    (segment ℝ (τ-δ) (τ+δ)) A hΩ hΛ
    (by
      apply IsCompact.isClosed
      rw [segment_eq_image_lineMap]
      exact isCompact_Icc.image AffineMap.lineMap_continuous)
    (dense_complex_segment_complement _ _) hQ hR.continuousOn
    (fun z hz => (hsq z ⟨hz.1.1,hz.2⟩).trans (hRsq z hz.1.2).symm) hRne hF
  intro b hb hbK
  have hleft : b ≠ τ-δ := by
    intro he
    have h := hRsq b hb.2
    rw [he,sub_self,zero_mul] at h
    exact pow_ne_zero 2 (hRne b hb.2) (by simpa only [he] using h)
  have hright : b ≠ τ+δ := by
    intro he
    have h := hRsq b hb.2
    rw [he,sub_self,mul_zero] at h
    exact pow_ne_zero 2 (hRne b hb.2) (by simpa only [he] using h)
  obtain ⟨B,P,hB,hbB,hBsub,hP,hPd,hmatch⟩ := exists_gap_interior_regular_sheet_primitive
    g Q F R Ω Λ τ δ A b hΩ hδ hgap hg hQ hsq hF hA hbK hleft hright hΛ hb.2 hR hRsq
  exact ⟨B,P,hB,hbB,hBsub,hP,hPd,fun z hz => hmatch z hz.1 hz.2⟩

end NLS.ComplexAnalysis
