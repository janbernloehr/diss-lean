import NLS.ZakharovShabat.SourceBirkhoffCoordinateAngle
import NLS.ZakharovShabat.SourceAngularThetaDifferential
import NLS.ZakharovShabat.SourceComplexActionAnalytic
import NLS.ComplexAnalysis.RectangularDifferential

/-! # The actual rectangular differentials on open real gaps

An analytic half-gap supplies the local polar amplitude. Its square
is twice the actual action, so differentiating the exact rectangular
formulas identifies their full source cotangents, including all moving
spectral and angular contributions.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceAngularEtaAnalyticChartData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {n : ℤ}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}
  {W V U : Set (CoeffPair p)} {c : ℤ → ℂ} {T : ℤ → ℝ}
  {r R : ℝ} {z₀ : ℂ} {ρ : ℝ} {δ ε : CoeffPair p → ℂ}

/-- The derivative formulas apply to the actual extended coordinates,
with the branch-independent full theta differential. -/
theorem birkhoffXY_fderiv_of_realType
    (D : SourceAngularEtaAnalyticChartData hp hp1 n s W V U c T r R z₀ ρ δ ε)
    (hβ : AnalyticOnNhd ℂ (sourceAngularBetaCorrection hp hp1 n s) U)
    (ψ : CoeffPair p) (hψ : ψ ∈ U) (hreal : IsRealType (CoeffPair.toMax p ψ)) :
    fderiv ℂ (sourceBirkhoffX hp hp1 n s) ψ =
      (sourceBirkhoffX hp hp1 n s ψ / (2*sourceComplexAction hp hp1 n ψ)) •
        fderiv ℂ (sourceComplexAction hp hp1 n) ψ +
          (-sourceBirkhoffY hp hp1 n s ψ) • sourceAngularThetaDifferential hp hp1 n s ψ ∧
    fderiv ℂ (sourceBirkhoffY hp hp1 n s) ψ =
      (sourceBirkhoffY hp hp1 n s ψ / (2*sourceComplexAction hp hp1 n ψ)) •
        fderiv ℂ (sourceComplexAction hp hp1 n) ψ +
          sourceBirkhoffX hp hp1 n s ψ • sourceAngularThetaDifferential hp hp1 n s ψ := by
  obtain ⟨A,hA,hψA,hξ,hfactor⟩ := exists_local_sourceNormalizedActionRoot_allIndices_analytic hp hp1 ψ hreal
  let a : CoeffPair p → ℂ := fun χ => sourceNormalizedActionRoot hp hp1 n χ * (2*δ χ) / (Real.sqrt 2 : ℂ)
  let θ := sourceAngularThetaCauchyRepresentative hp hp1 n s (c n) r R z₀ ρ ε
  have hden : (Real.sqrt 2 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (by norm_num)))
  have hdenSq : (Real.sqrt 2 : ℂ)^2 = 2 := by
    norm_cast
    exact Real.sq_sqrt (by norm_num)
  have ha : DifferentiableAt ℂ a ψ :=
    (((hξ n ψ hψA).mul (analyticAt_const.mul (D.angle.halfGap_analytic ψ hψ))).div
      analyticAt_const hden).differentiableAt
  have hsq : (fun χ => a χ ^ 2) =ᶠ[𝓝 ψ] (fun χ => 2*sourceComplexAction hp hp1 n χ) := by
    filter_upwards [hA.mem_nhds hψA,D.angle.source_open.mem_nhds hψ] with χ hχA hχ
    obtain ⟨hroot,hI⟩ := hfactor χ hχA n
    have hδ := D.angle.halfGap_sq χ hχ
    dsimp only [a]
    rw [div_pow,mul_pow,mul_pow,hdenSq,hroot,hδ,hI,sourcePeriodicGapDisplacement_apply]
    ring
  have hrootne : sourceNormalizedActionRoot hp hp1 n ψ ≠ 0 := by
    intro hz
    have hroot := (hfactor ψ hψA n).1
    rw [hz,zero_pow (by norm_num : 2 ≠ 0)] at hroot
    have hF := sourceNormalizedActionComplexExtension_ne_zero_of_realType hp hp1 n ψ hreal
    exact hF ((mul_eq_zero.mp hroot.symm).resolve_left (by norm_num))
  have hane : a ψ ≠ 0 := div_ne_zero (mul_ne_zero hrootne
    (mul_ne_zero (by norm_num) (D.angle.halfGap_ne_zero ψ hψ))) hden
  have hXY : (sourceBirkhoffX hp hp1 n s =ᶠ[𝓝 ψ] (fun χ => a χ*Complex.cos (θ χ))) ∧
      (sourceBirkhoffY hp hp1 n s =ᶠ[𝓝 ψ] (fun χ => a χ*Complex.sin (θ χ))) := by
    constructor <;> filter_upwards [D.angle.source_open.mem_nhds hψ] with χ hχ
    · exact (D.birkhoffXY_eq_halfGap_cos_sin χ hχ).1
    · exact (D.birkhoffXY_eq_halfGap_cos_sin χ hχ).2
  have h := NLS.ComplexAnalysis.fderiv_rectangular_of_sq a θ (sourceComplexAction hp hp1 n)
    (sourceBirkhoffX hp hp1 n s) (sourceBirkhoffY hp hp1 n s) ψ ha
    (D.theta_representative_analytic hβ ψ hψ).differentiableAt
    (analyticAt_sourceComplexAction_of_realType hp hp1 n ψ hreal).differentiableAt hane hsq hXY.1 hXY.2
  rwa [← D.thetaDifferential_eq_fderiv_representative hβ ψ hψ] at h

end SourceAngularEtaAnalyticChartData
end NLS.ZakharovShabat
