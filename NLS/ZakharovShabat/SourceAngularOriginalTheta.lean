import NLS.ZakharovShabat.SourceAngularOriginalBetaSeries
import NLS.ZakharovShabat.SourceAngularOriginalEtaIntegral

/-!
# The literal theta sum on the original domain

Theta is the constructed eta integral plus the actual off-diagonal beta
series. Its real analytic local representatives agree with this literal
sum modulo π, and its values are real at real-type sources.
-/

noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
def sourceAngularOriginalTheta (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (ψ : CoeffPair p) : ℂ :=
  sourceAngularOriginalEta hp hp1 n s ψ+sourceAngularBetaCorrection hp hp1 n s ψ

/-- Theta is literally the chosen endpoint integral plus the off-diagonal series. -/
theorem sourceAngularOriginalTheta_eq_series (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (ψ : CoeffPair p) :
    sourceAngularOriginalTheta hp hp1 n s ψ = sourceAngularOriginalEta hp hp1 n s ψ+
      ∑' m : ℤ, sourceAngularBetaSeriesTerm hp hp1 n s ψ m := rfl

namespace SourceLemma12_12Data
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- Replacing eta by any actual normalized integral preserves theta modulo 2π. -/
theorem theta_original_integral_choice_period (H : SourceLemma12_12Data hp hp1 W₀ W s)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (n : ℤ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n ≠ 0)
    {v : ℂ} (hv : v ∈ sourceAngularOriginalEtaIntegralValues hp hp1 n s ψ) :
    ∃ k : ℤ, (v+sourceAngularBetaCorrection hp hp1 n s ψ)-sourceAngularOriginalTheta hp hp1 n s ψ =
      (k:ℂ)*(2*Real.pi) := by
  simpa only [sourceAngularOriginalTheta,add_sub_add_right_eq_sub] using
    H.eta_original_integral_values_period ψ hψ n hgap hv (H.eta_original_integral_mem ψ hψ n hgap)
theorem theta_original_im_eq_zero (H : SourceLemma12_12Data hp hp1 W₀ W s)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (hreal : IsRealType (CoeffPair.toMax p ψ)) (n : ℤ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n ≠ 0) :
    (sourceAngularOriginalTheta hp hp1 n s ψ).im = 0 := by
  simp only [sourceAngularOriginalTheta,Complex.add_im,
    H.eta_original_integral_im_eq_zero ψ hψ hreal n hgap,
    H.beta_original_correction_im_eq_zero ψ hψ hreal n,add_zero]

theorem theta_original_phase (H : SourceLemma12_12Data hp hp1 W₀ W s)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (n : ℤ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n ≠ 0) :
    Complex.exp (2*Complex.I*sourceAngularOriginalTheta hp hp1 n s ψ) =
      sourceAngularThetaAnalyticPhase hp hp1 n s ψ := by
  rw [sourceAngularOriginalTheta,mul_add,Complex.exp_add,
    H.eta_original_integral_phase ψ hψ n hgap,sourceAngularThetaAnalyticPhase]

theorem theta_original_phase_analytic (H : SourceLemma12_12Data hp hp1 W₀ W s) (n : ℤ) :
    AnalyticOnNhd ℂ (sourceAngularThetaAnalyticPhase hp hp1 n s)
      {ψ : CoeffPair p | ψ ∈ W ∧
        canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n ≠ 0} := by
  intro ψ hψ
  exact ((H.eta_original_phase_analytic n).2.1 ψ hψ).mul
    ((analyticAt_const.mul (H.beta_original_series.analytic_correction n ψ hψ.1)).cexp')

theorem theta_original_local_representative (H : SourceLemma12_12Data hp hp1 W₀ W s)
    (φ : CoeffPair p) (hφ : φ ∈ W) (n : ℤ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n ≠ 0) :
    ∃ U : Set (CoeffPair p), ∃ f : CoeffPair p → ℂ,
      IsOpen U ∧ φ ∈ U ∧ U ⊆ W ∧
      (∀ ψ ∈ U, canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n ≠ 0) ∧
      AnalyticOnNhd ℂ f U ∧
      (∀ ψ ∈ U, IsRealType (CoeffPair.toMax p ψ) → (f ψ).im = 0) ∧
      ∀ ψ ∈ U, ∃ k : ℤ, sourceAngularOriginalTheta hp hp1 n s ψ-f ψ = (k:ℂ)*Real.pi := by
  obtain ⟨U,f,ho,hφU,hUW,hg,ha,hr,hv⟩ := H.eta_original_value_local_representative φ hφ n hgap
  refine ⟨U,fun ψ => f ψ+sourceAngularBetaCorrection hp hp1 n s ψ,ho,hφU,hUW,hg,?_,?_,?_⟩
  · exact fun ψ hψ => (ha ψ hψ).add (H.beta_original_series.analytic_correction n ψ (hUW hψ))
  · intro ψ hψ hreal
    simp only [Complex.add_im,hr ψ hψ hreal,H.beta_original_correction_im_eq_zero ψ (hUW hψ) hreal n,add_zero]
  · intro ψ hψ
    simpa only [sourceAngularOriginalTheta,add_sub_add_right_eq_sub] using hv ψ hψ

end SourceLemma12_12Data
end NLS.ZakharovShabat
