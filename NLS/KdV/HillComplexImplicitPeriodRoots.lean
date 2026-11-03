import NLS.KdV.HillComplexSupportedPeriodMap
import NLS.ComplexAnalysis.AnalyticImplicitBanachRoot

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal

namespace NLS.KdV

variable
    (hq : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem partial_fderiv_hillComplexSupportedPeriodMap_zero (n : ℕ) (hn : 1 ≤ n) :
    (fderiv ℂ (hillComplexSupportedPeriodMap hq hr n) (0,0)).comp
      (ContinuousLinearMap.inl ℂ (PositiveDeletedCoeff 2 (n : ℤ)) (Coeff 2)) =
        -ContinuousLinearMap.id ℂ (PositiveDeletedCoeff 2 (n : ℤ)) := by
  obtain ⟨ε,D,hε,hD,hc⟩ := exists_hillComplexPeriodControl hq hr
  have hF := analyticOnNhd_hillComplexSupportedPeriodMap hq hr n hn ε D hD.le hc
    (0,0) ⟨mem_univ _,mem_ball_self hε⟩
  have hd := hF.differentiableAt.hasFDerivAt.comp (0 : PositiveDeletedCoeff 2 (n : ℤ))
    (ContinuousLinearMap.inl ℂ (PositiveDeletedCoeff 2 (n : ℤ)) (Coeff 2)).hasFDerivAt
  have he : (fun a : PositiveDeletedCoeff 2 (n : ℤ) => hillComplexSupportedPeriodMap hq hr n (a,0)) =
      hillFreeSupportedPeriodMap hq hr n hn := funext (hillComplexSupportedPeriodMap_zero_potential hq hr n hn)
  have hd' : HasFDerivAt (hillFreeSupportedPeriodMap hq hr n hn)
      ((fderiv ℂ (hillComplexSupportedPeriodMap hq hr n) (0,0)).comp
        (ContinuousLinearMap.inl ℂ (PositiveDeletedCoeff 2 (n : ℤ)) (Coeff 2))) 0 := by
    convert! hd using 1
    exact he.symm
  exact hd'.unique (hasFDerivAt_hillFreeSupportedPeriodMap_zero hq hr n hn)

theorem exists_hillComplexSupportedPeriod_implicit_roots (n : ℕ) (hn : 1 ≤ n) :
    ∃ a : Coeff 2 → PositiveDeletedCoeff 2 (n : ℤ),
      AnalyticAt ℂ a 0 ∧ a 0 = 0 ∧
        ∀ᶠ p in 𝓝 (0 : Coeff 2), hillComplexSupportedPeriodMap hq hr n (a p,p) = 0 := by
  obtain ⟨ε,D,hε,hD,hc⟩ := exists_hillComplexPeriodControl hq hr
  apply exists_analytic_implicitBanachRoot (hillComplexSupportedPeriodMap hq hr n) 0 0
  · exact analyticOnNhd_hillComplexSupportedPeriodMap hq hr n hn ε D hD.le hc
      (0,0) ⟨mem_univ _,mem_ball_self hε⟩
  · exact hillComplexSupportedPeriodMap_zero hq hr n hn
  · rw [partial_fderiv_hillComplexSupportedPeriodMap_zero hq hr n hn]
    exact ⟨neg_injective,fun y => ⟨-y,neg_neg y⟩⟩

end NLS.KdV
