import NLS.KdV.HillDirichletTraceCotangent
import NLS.KdV.HillDiscriminantMeanShift

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.ZakharovShabat NLS.FunctionalAnalysis NLS.LinearVolterra
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



/-- The coefficient in the exact Dirichlet trace-cotangent decomposition is
minus the actual energy derivative, fixed by constant-potential translation. -/
theorem hillDirichletTraceCotangent_coefficient_eq_neg_deriv
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1≤n) :
    (scalarStateMass (hillDirichletStateCurve q n hn) : ℂ)*
      (hillDirichletSheetRoot (SpectralWeight.one.toCoeff q.val)
          (hillDirichletEnergy q.val q.property.1 q.property.2 n hn)*hillLogNormingProjection q n hn-
        (hillDirichletCosineCurve q n hn ⟨1,by norm_num⟩).2)=
      -deriv (hillL2Discriminant (SpectralWeight.one.toCoeff q.val))
        (hillDirichletEnergy q.val q.property.1 q.property.2 n hn) := by
  have h := congrArg unitComplexCurveIntegralCLM (hillEnergyDiscriminantGradient_dirichlet_decomposition q n hn)
  simp only [map_add,map_smul,smul_eq_mul] at h
  change (∫ x in (0 : ℝ)..1,NLS.LinearVolterra.extend
      (hillEnergyDiscriminantGradientCurve (SpectralWeight.one.toCoeff q.val)
        (hillDirichletEnergy q.val q.property.1 q.property.2 n hn)) x)=
    _*(∫ x in (0 : ℝ)..1,NLS.LinearVolterra.extend (hillLogNormingGradientCurve q n hn) x)+
    _*(∫ x in (0 : ℝ)..1,NLS.LinearVolterra.extend (hillDirichletGradientCurve q n hn) x) at h
  rw [hillLogNormingGradient_integral_eq_zero,hillDirichletGradient_integral_eq_one,
    mul_zero,zero_add,mul_one] at h
  exact h.symm.trans (hillEnergyDiscriminantGradient_integral_eq_neg_deriv _ _)

/-- The exact moving-Dirichlet trace cotangent in its intrinsic energy normalization. -/
theorem hillEnergyDiscriminantGradient_dirichlet_eq_sheet_log_sub_deriv_dirichlet
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1≤n) :
    hillEnergyDiscriminantGradientCurve (SpectralWeight.one.toCoeff q.val)
        (hillDirichletEnergy q.val q.property.1 q.property.2 n hn)=
      hillDirichletSheetRoot (SpectralWeight.one.toCoeff q.val)
          (hillDirichletEnergy q.val q.property.1 q.property.2 n hn) • hillLogNormingGradientCurve q n hn-
        deriv (hillL2Discriminant (SpectralWeight.one.toCoeff q.val))
          (hillDirichletEnergy q.val q.property.1 q.property.2 n hn) • hillDirichletGradientCurve q n hn := by
  rw [hillEnergyDiscriminantGradient_dirichlet_decomposition,
    hillDirichletTraceCotangent_coefficient_eq_neg_deriv]
  ext t
  change hillDirichletSheetRoot (SpectralWeight.one.toCoeff q.val)
      (hillDirichletEnergy q.val q.property.1 q.property.2 n hn)*(hillLogNormingGradientCurve q n hn t)+
    (-(deriv (hillL2Discriminant (SpectralWeight.one.toCoeff q.val))
      (hillDirichletEnergy q.val q.property.1 q.property.2 n hn)))*(hillDirichletGradientCurve q n hn t)=
    hillDirichletSheetRoot (SpectralWeight.one.toCoeff q.val)
      (hillDirichletEnergy q.val q.property.1 q.property.2 n hn)*(hillLogNormingGradientCurve q n hn t)-
    deriv (hillL2Discriminant (SpectralWeight.one.toCoeff q.val))
      (hillDirichletEnergy q.val q.property.1 q.property.2 n hn)*(hillDirichletGradientCurve q n hn t)
  ring

end NLS.KdV
