import NLS.KdV.HillDirichletQuadraticSystem
import NLS.KdV.HillGradientSecondDerivatives

/-! # Periodic first-derivative traces of the independent Hill cotangents

Both gradients vanish at the interval endpoints. The Dirichlet gradient's
first derivative vanishes there; the log-norming gradient's first
derivative equals one at both ends by the actual Wronskian. Thus the
weak Magri formulas retain the periodic boundary normalization.
-/
noncomputable section
open Set Complex Filter Topology MeasureTheory
open NLS.LinearVolterra NLS.ZakharovShabat NLS.ComplexAnalysis NLS.FunctionalAnalysis
open scoped ENNReal
namespace NLS.KdV

theorem hillLogNormingGradientSpatialCurve_endpoints (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1 ≤ n) :
    hillLogNormingGradientSpatialCurve q n hn ⟨0,by norm_num⟩ = 1 ∧
      hillLogNormingGradientSpatialCurve q n hn ⟨1,by norm_num⟩ = 1 := by
  constructor
  · dsimp only [hillLogNormingGradientSpatialCurve,hillDirichletStateCurve,hillDirichletCosineCurve,
      ContinuousMap.smul_apply,ContinuousMap.sub_apply,ContinuousMap.add_apply,ContinuousMap.mul_apply,
      ContinuousMap.comp_apply,ContinuousMap.fst,ContinuousMap.snd,ContinuousMap.coe_mk,smul_eq_mul]
    rw [hillL2FrequencyStateCurve_zero,hillL2FrequencyStateCurve_zero]
    ring
  · have hs : (hillDirichletStateCurve q n hn ⟨1,by norm_num⟩).1 = 0 :=
      hillDirichletEnergy_zero q.val q.property.1 q.property.2 n hn
    have hw := hillL2FrequencyStateCurve_wronskian (SpectralWeight.one.toCoeff q.val)
      (Complex.sqrt (hillDirichletEnergy q.val q.property.1 q.property.2 n hn)) ⟨1,by norm_num⟩
    change (hillDirichletCosineCurve q n hn ⟨1,by norm_num⟩).1*(hillDirichletStateCurve q n hn ⟨1,by norm_num⟩).2-
      (hillDirichletStateCurve q n hn ⟨1,by norm_num⟩).1*(hillDirichletCosineCurve q n hn ⟨1,by norm_num⟩).2 = 1 at hw
    change (hillDirichletCosineCurve q n hn ⟨1,by norm_num⟩).2*(hillDirichletStateCurve q n hn ⟨1,by norm_num⟩).1+
      (hillDirichletCosineCurve q n hn ⟨1,by norm_num⟩).1*(hillDirichletStateCurve q n hn ⟨1,by norm_num⟩).2-
      (2*hillLogNormingProjection q n hn)*((hillDirichletStateCurve q n hn ⟨1,by norm_num⟩).1*
        (hillDirichletStateCurve q n hn ⟨1,by norm_num⟩).2) = 1
    rw [hs] at hw ⊢
    simpa only [zero_mul,mul_zero,sub_zero,zero_add] using hw

end NLS.KdV
