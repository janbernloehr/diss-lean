import NLS.ZakharovShabat.SourceAngularCauchyReal
import NLS.ZakharovShabat.SourceAngularEtaAnalyticPhase
import NLS.ZakharovShabat.SourceAngularBetaSeriesAnalytic

/-! # The angle coordinate: eta plus the actual beta correction

Full eta representatives and the convergent off-diagonal correction
give analytic angle representatives modulo pi. Their single phase is
`exp(2i theta)`. Reality of the individual terms and absolute convergence
give real correction values and real angle representatives.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def sourceAngularThetaCauchyRepresentative
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k)
    (c : ℂ) (r R : ℝ) (z₀ : ℂ) (ρ : ℝ) (ε : CoeffPair p → ℂ) (ψ : CoeffPair p) : ℂ :=
  sourceAngularEtaCauchyRepresentative hp hp1 n s c r R z₀ ρ ε ψ+
    sourceAngularBetaCorrection hp hp1 n s ψ

def sourceAngularThetaAnalyticPhase
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (ψ : CoeffPair p) : ℂ :=
  sourceAngularEtaAnalyticPhase hp hp1 n s ψ*
    Complex.exp (2*I*sourceAngularBetaCorrection hp hp1 n s ψ)

theorem SourceAngularBetaSeriesAnalyticData.correction_im_eq_zero_of_terms
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}
    (D : SourceAngularBetaSeriesAnalyticData hp hp1 W s)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (n : ℤ)
    (hreal : ∀ m : ℤ, m ≠ n → (sourceAngularBeta hp hp1 n m s ψ).im = 0) :
    (sourceAngularBetaCorrection hp hp1 n s ψ).im = 0 := by
  classical
  rw [sourceAngularBetaCorrection,Complex.im_tsum (D.summable_norm ψ hψ n).of_norm]
  have hzero (m : ℤ) : (sourceAngularBetaSeriesTerm hp hp1 n s ψ m).im = 0 := by
    by_cases hmn : m = n
    · simp only [sourceAngularBetaSeriesTerm,if_pos hmn,Complex.zero_im]
    · simpa only [sourceAngularBetaSeriesTerm,if_neg hmn] using hreal m hmn
  simp only [hzero,tsum_zero]

namespace SourceAngularEtaAnalyticChartData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {n : ℤ}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}
  {W V U : Set (CoeffPair p)} {c : ℤ → ℂ} {T : ℤ → ℝ}
  {r R : ℝ} {z₀ : ℂ} {ρ : ℝ} {δ ε : CoeffPair p → ℂ}

theorem theta_representative_analytic
    (D : SourceAngularEtaAnalyticChartData hp hp1 n s W V U c T r R z₀ ρ δ ε)
    (hbeta : AnalyticOnNhd ℂ (sourceAngularBetaCorrection hp hp1 n s) U) :
    AnalyticOnNhd ℂ (sourceAngularThetaCauchyRepresentative hp hp1 n s (c n) r R z₀ ρ ε) U :=
  fun ψ hψ => (D.eta_analytic ψ hψ).add (hbeta ψ hψ)

theorem theta_representative_sub_eq_int_pi
    (D : SourceAngularEtaAnalyticChartData hp hp1 n s W V U c T r R z₀ ρ δ ε)
    {W' V' U' : Set (CoeffPair p)} {c' : ℤ → ℂ} {T' : ℤ → ℝ}
    {r' R' : ℝ} {z₀' : ℂ} {ρ' : ℝ} {δ' ε' : CoeffPair p → ℂ}
    (D' : SourceAngularEtaAnalyticChartData hp hp1 n s W' V' U' c' T' r' R' z₀' ρ' δ' ε')
    (ψ : CoeffPair p) (hψ : ψ ∈ U) (hψ' : ψ ∈ U') :
    ∃ k : ℤ, sourceAngularThetaCauchyRepresentative hp hp1 n s (c n) r R z₀ ρ ε ψ-
      sourceAngularThetaCauchyRepresentative hp hp1 n s (c' n) r' R' z₀' ρ' ε' ψ = (k:ℂ)*(Real.pi:ℂ) := by
  obtain ⟨k,hk⟩ := D.representative_sub_eq_int_pi D' ψ hψ hψ'
  exact ⟨k,by simpa only [sourceAngularThetaCauchyRepresentative,add_sub_add_right_eq_sub] using hk⟩

theorem theta_phase_eq_exp_representative
    (D : SourceAngularEtaAnalyticChartData hp hp1 n s W V U c T r R z₀ ρ δ ε)
    (ψ : CoeffPair p) (hψ : ψ ∈ U) :
    sourceAngularThetaAnalyticPhase hp hp1 n s ψ =
      Complex.exp (2*I*sourceAngularThetaCauchyRepresentative hp hp1 n s (c n) r R z₀ ρ ε ψ) := by
  rw [sourceAngularThetaAnalyticPhase,D.phase_eq_exp_representative ψ hψ,
    sourceAngularThetaCauchyRepresentative,mul_add,Complex.exp_add]

theorem theta_phase_ne_zero
    (D : SourceAngularEtaAnalyticChartData hp hp1 n s W V U c T r R z₀ ρ δ ε)
    (ψ : CoeffPair p) (hψ : ψ ∈ U) : sourceAngularThetaAnalyticPhase hp hp1 n s ψ ≠ 0 := by
  rw [D.theta_phase_eq_exp_representative ψ hψ]
  exact Complex.exp_ne_zero _

theorem theta_phase_analytic
    (D : SourceAngularEtaAnalyticChartData hp hp1 n s W V U c T r R z₀ ρ δ ε)
    (hbeta : AnalyticOnNhd ℂ (sourceAngularBetaCorrection hp hp1 n s) U) :
    AnalyticOnNhd ℂ (sourceAngularThetaAnalyticPhase hp hp1 n s) U :=
  fun ψ hψ => (D.analyticOnNhd_phase ψ hψ).mul ((analyticAt_const.mul (hbeta ψ hψ)).cexp')

theorem theta_representative_im_eq_zero_of_realType
    (D : SourceAngularEtaAnalyticChartData hp hp1 n s W V U c T r R z₀ ρ δ ε)
    {W₀ : Set (CoeffPair p)} (hs : SourcePsiIsolatingComplexExtension hp hp1 W₀ s)
    (ψ : CoeffPair p) (hψ : ψ ∈ U) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (hbeta : (sourceAngularBetaCorrection hp hp1 n s ψ).im = 0) :
    (sourceAngularThetaCauchyRepresentative hp hp1 n s (c n) r R z₀ ρ ε ψ).im = 0 := by
  simp only [sourceAngularThetaCauchyRepresentative,Complex.add_im,
    D.representative_im_eq_zero_of_realType hs ψ hψ hreal,hbeta,add_zero]

theorem theta_phase_norm_eq_one_of_realType
    (D : SourceAngularEtaAnalyticChartData hp hp1 n s W V U c T r R z₀ ρ δ ε)
    {W₀ : Set (CoeffPair p)} (hs : SourcePsiIsolatingComplexExtension hp hp1 W₀ s)
    (ψ : CoeffPair p) (hψ : ψ ∈ U) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (hbeta : (sourceAngularBetaCorrection hp hp1 n s ψ).im = 0) :
    ‖sourceAngularThetaAnalyticPhase hp hp1 n s ψ‖ = 1 := by
  rw [D.theta_phase_eq_exp_representative ψ hψ,Complex.norm_exp]
  simp [Complex.mul_re,D.theta_representative_im_eq_zero_of_realType hs ψ hψ hreal hbeta]

end SourceAngularEtaAnalyticChartData
end NLS.ZakharovShabat
