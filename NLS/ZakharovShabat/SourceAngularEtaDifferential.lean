import NLS.ZakharovShabat.SourceAngularEtaAnalyticPhase
import NLS.ZakharovShabat.SourceAngularThetaDifferential
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-! # A single analytic differential for the angle coordinate

The logarithmic differential of the nonzero phase `exp(2i eta)`
recovers the derivative of every local eta representative. It is
analytic on the every actual open-gap chart and independent
of annuli, half-gap signs, and angle choices. This is the cotangent
needed to formulate Corollary 13.2 without selecting an angle branch.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def sourceAngularEtaDifferential (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (ψ : CoeffPair p) : CoeffPair p →L[ℂ] ℂ :=
  (2*I*sourceAngularEtaAnalyticPhase hp hp1 n s ψ)⁻¹ •
    fderiv ℂ (sourceAngularEtaAnalyticPhase hp hp1 n s) ψ

theorem SourceAngularEtaAnalyticChartData.etaDifferential_eq_fderiv_representative
    {hp : p ≠ ⊤} {hp1 : 1 < p} {n : ℤ}
    {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}
    {W V U : Set (CoeffPair p)} {c : ℤ → ℂ} {T : ℤ → ℝ}
    {r R : ℝ} {z₀ : ℂ} {ρ : ℝ} {δ ε : CoeffPair p → ℂ}
    (D : SourceAngularEtaAnalyticChartData hp hp1 n s W V U c T r R z₀ ρ δ ε)
    (ψ : CoeffPair p) (hψ : ψ ∈ U) :
    sourceAngularEtaDifferential hp hp1 n s ψ =
      fderiv ℂ (sourceAngularEtaCauchyRepresentative hp hp1 n s (c n) r R z₀ ρ ε) ψ := by
  let η := sourceAngularEtaCauchyRepresentative hp hp1 n s (c n) r R z₀ ρ ε
  have hη : DifferentiableAt ℂ η ψ := (D.eta_analytic ψ hψ).differentiableAt
  have hd := (hη.hasFDerivAt.const_mul (2*I)).cexp
  have hlocal : sourceAngularEtaAnalyticPhase hp hp1 n s =ᶠ[𝓝 ψ]
      (fun χ => Complex.exp (2*I*η χ)) := by
    filter_upwards [D.angle.source_open.mem_nhds hψ] with χ hχ
    exact D.phase_eq_exp_representative χ hχ
  have hfd := hlocal.fderiv_eq.trans hd.fderiv
  have hne : 2*I*sourceAngularEtaAnalyticPhase hp hp1 n s ψ ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) I_ne_zero) (D.phase_ne_zero ψ hψ)
  rw [sourceAngularEtaDifferential,hfd]
  apply ContinuousLinearMap.ext
  intro h
  simp only [smul_apply,smul_eq_mul]
  rw [← D.phase_eq_exp_representative ψ hψ]
  have he : (2*I*sourceAngularEtaAnalyticPhase hp hp1 n s ψ)⁻¹*
      sourceAngularEtaAnalyticPhase hp hp1 n s ψ*(2*I) = 1 := by
    calc
      _ = (2*I*sourceAngularEtaAnalyticPhase hp hp1 n s ψ)⁻¹*
          (2*I*sourceAngularEtaAnalyticPhase hp hp1 n s ψ) := by ring
      _ = 1 := inv_mul_cancel₀ hne
  change (2*I*sourceAngularEtaAnalyticPhase hp hp1 n s ψ)⁻¹*
    (sourceAngularEtaAnalyticPhase hp hp1 n s ψ*(2*I*(fderiv ℂ η ψ) h)) = (fderiv ℂ η ψ) h
  linear_combination (fderiv ℂ η ψ) h*he

theorem SourceAngularEtaAnalyticChartData.analyticOnNhd_etaDifferential
    {hp : p ≠ ⊤} {hp1 : 1 < p} {n : ℤ}
    {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}
    {W V U : Set (CoeffPair p)} {c : ℤ → ℂ} {T : ℤ → ℝ}
    {r R : ℝ} {z₀ : ℂ} {ρ : ℝ} {δ ε : CoeffPair p → ℂ}
    (D : SourceAngularEtaAnalyticChartData hp hp1 n s W V U c T r R z₀ ρ δ ε) :
    AnalyticOnNhd ℂ (sourceAngularEtaDifferential hp hp1 n s) U := by
  intro ψ hψ
  have hphase := D.analyticOnNhd_phase ψ hψ
  have hne : 2*I*sourceAngularEtaAnalyticPhase hp hp1 n s ψ ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) I_ne_zero) (D.phase_ne_zero ψ hψ)
  exact ((analyticAt_const.mul hphase).inv hne).smul (D.analyticOnNhd_phase.fderiv ψ hψ)

/-- The actual single theta cotangent splits into the single eta
cotangent and the derivative of the actual analytic beta correction. -/
theorem SourceAngularEtaAnalyticChartData.thetaDifferential_eq_eta_add_betaCorrection
    {hp : p ≠ ⊤} {hp1 : 1 < p} {n : ℤ}
    {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}
    {W V U : Set (CoeffPair p)} {c : ℤ → ℂ} {T : ℤ → ℝ}
    {r R : ℝ} {z₀ : ℂ} {ρ : ℝ} {δ ε : CoeffPair p → ℂ}
    (D : SourceAngularEtaAnalyticChartData hp hp1 n s W V U c T r R z₀ ρ δ ε)
    (hbeta : AnalyticOnNhd ℂ (sourceAngularBetaCorrection hp hp1 n s) U)
    (ψ : CoeffPair p) (hψ : ψ ∈ U) :
    sourceAngularThetaDifferential hp hp1 n s ψ =
      sourceAngularEtaDifferential hp hp1 n s ψ+
        fderiv ℂ (sourceAngularBetaCorrection hp hp1 n s) ψ := by
  rw [D.thetaDifferential_eq_fderiv_representative hbeta ψ hψ,
    D.etaDifferential_eq_fderiv_representative ψ hψ]
  exact fderiv_fun_add (D.eta_analytic ψ hψ).differentiableAt (hbeta ψ hψ).differentiableAt

end NLS.ZakharovShabat
