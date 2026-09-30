import NLS.ZakharovShabat.SourceAngularThetaTheorem13_1
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-! # A single analytic differential for the angle coordinate

The logarithmic differential of the nonzero phase `exp(2i theta)`
recovers the derivative of every local theta representative. It is
analytic on the entire indexed open-gap source domain and independent
of annuli, half-gap signs, and angle choices. This is the cotangent
needed to formulate Corollary 13.2 without selecting an angle branch.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def sourceAngularThetaDifferential (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (ψ : CoeffPair p) : CoeffPair p →L[ℂ] ℂ :=
  (2*I*sourceAngularThetaAnalyticPhase hp hp1 n s ψ)⁻¹ •
    fderiv ℂ (sourceAngularThetaAnalyticPhase hp hp1 n s) ψ

theorem SourceAngularEtaAnalyticChartData.thetaDifferential_eq_fderiv_representative
    {hp : p ≠ ⊤} {hp1 : 1 < p} {n : ℤ}
    {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}
    {W V U : Set (CoeffPair p)} {c : ℤ → ℂ} {T : ℤ → ℝ}
    {r R : ℝ} {z₀ : ℂ} {ρ : ℝ} {δ ε : CoeffPair p → ℂ}
    (D : SourceAngularEtaAnalyticChartData hp hp1 n s W V U c T r R z₀ ρ δ ε)
    (hbeta : AnalyticOnNhd ℂ (sourceAngularBetaCorrection hp hp1 n s) U)
    (ψ : CoeffPair p) (hψ : ψ ∈ U) :
    sourceAngularThetaDifferential hp hp1 n s ψ =
      fderiv ℂ (sourceAngularThetaCauchyRepresentative hp hp1 n s (c n) r R z₀ ρ ε) ψ := by
  let θ := sourceAngularThetaCauchyRepresentative hp hp1 n s (c n) r R z₀ ρ ε
  have hθ : DifferentiableAt ℂ θ ψ := (D.theta_representative_analytic hbeta ψ hψ).differentiableAt
  have hd := (hθ.hasFDerivAt.const_mul (2*I)).cexp
  have hlocal : sourceAngularThetaAnalyticPhase hp hp1 n s =ᶠ[𝓝 ψ]
      (fun χ => Complex.exp (2*I*θ χ)) := by
    filter_upwards [D.angle.source_open.mem_nhds hψ] with χ hχ
    exact D.theta_phase_eq_exp_representative χ hχ
  have hfd := hlocal.fderiv_eq.trans hd.fderiv
  have hne : 2*I*sourceAngularThetaAnalyticPhase hp hp1 n s ψ ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) I_ne_zero) (D.theta_phase_ne_zero ψ hψ)
  rw [sourceAngularThetaDifferential,hfd]
  apply ContinuousLinearMap.ext
  intro h
  simp only [smul_apply,smul_eq_mul]
  rw [← D.theta_phase_eq_exp_representative ψ hψ]
  have he : (2*I*sourceAngularThetaAnalyticPhase hp hp1 n s ψ)⁻¹*
      sourceAngularThetaAnalyticPhase hp hp1 n s ψ*(2*I) = 1 := by
    calc
      _ = (2*I*sourceAngularThetaAnalyticPhase hp hp1 n s ψ)⁻¹*
          (2*I*sourceAngularThetaAnalyticPhase hp hp1 n s ψ) := by ring
      _ = 1 := inv_mul_cancel₀ hne
  change (2*I*sourceAngularThetaAnalyticPhase hp hp1 n s ψ)⁻¹*
    (sourceAngularThetaAnalyticPhase hp hp1 n s ψ*(2*I*(fderiv ℂ θ ψ) h)) = (fderiv ℂ θ ψ) h
  linear_combination (fderiv ℂ θ ψ) h*he

theorem SourceAngularThetaCommonDomainData.analyticOnNhd_thetaDifferential
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
    {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}
    (D : SourceAngularThetaCommonDomainData hp hp1 W₀ B W s) (n : ℤ) :
    AnalyticOnNhd ℂ (sourceAngularThetaDifferential hp hp1 n s)
      {ψ : CoeffPair p | ψ ∈ W ∧ canonicalPeriodicGap hp hp1
        (periodOnePotential ψ) (periodOnePotential_mem ψ) n ≠ 0} := by
  intro ψ hψ
  have hphase := D.theta_phase_analytic n ψ hψ
  have hne : 2*I*sourceAngularThetaAnalyticPhase hp hp1 n s ψ ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) I_ne_zero) (D.theta_phase_ne_zero ψ hψ.1 n hψ.2)
  exact ((analyticAt_const.mul hphase).inv hne).smul ((D.theta_phase_analytic n).fderiv ψ hψ)

end NLS.ZakharovShabat
