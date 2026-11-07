import NLS.SequenceSpaces.AnalyticUniformAmplitudeError
import NLS.ComplexAnalysis.AnalyticDomainPullback

/-! Keep original source inclusion, amplitude domain and local weighted
error symbol in one opaque Banach-space pullback. -/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.Coeff

theorem exists_analytic_amplitude_error_pullback
    {E Q : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup Q] [NormedSpace ℂ Q]
    (L : E →L[ℂ] Q) (D : Set Q) (hD : IsOpen D) (A : Q → Coeff ⊤) (hAa : AnalyticOnNhd ℂ A D)
    (V : Set E) (hV : IsOpen V) (q : E) (hqV : q∈V) (hqD : L q∈D)
    (a : ℕ+ → ℝ) (ha : ∀ n,0<a n) (ha1 : ∀ n,a n≤1)
    (hpos : ∀ n : ℕ+,0<(A (L q) (n:ℤ)).re)
    (N : ℕ) (K : ℝ) (hK : 0≤K)
    (hsq : ∀ n : ℕ+,N≤(n:ℕ) → ∀ p∈V,(1+(n:ℝ))*‖(A (L p) (n:ℤ)/(a n:ℂ))^2-1‖≤K) :
    ∃ U : Set E,IsOpen U ∧ q∈U ∧ (∀ p∈U,L p∈D) ∧
      ∃ C : ℝ,∃ M : E → Coeff ⊤,0≤C ∧ AnalyticOnNhd ℂ M U ∧ ∀ p∈U,
        ‖M p‖≤C ∧ (∀ j : ℤ,j≤0 → M p j=0) ∧ ∀ n : ℕ+,
          M p (n:ℤ)=(1+(n:ℂ))*(A (L p) (n:ℤ)-(a n:ℂ)) := by
  let W := V∩L ⁻¹' D
  have hW : IsOpen W := hV.inter (hD.preimage L.continuous)
  have hWa : AnalyticOnNhd ℂ (fun p => A (L p)) W :=
    (NLS.ComplexAnalysis.analyticOnNhd_clm_preimage L A D hAa).mono inter_subset_right
  obtain ⟨U,hU,hqU,hUW,C,M,hC,hMa,hM⟩ := exists_analytic_uniform_amplitude_error W hW q ⟨hqV,hqD⟩
    (fun p => A (L p)) hWa a ha ha1 hpos N K hK (fun n hn p hp => hsq n hn p hp.1)
  exact ⟨U,hU,hqU,(fun p hp => (hUW hp).2),C,M,hC,hMa,hM⟩

end NLS.Coeff
