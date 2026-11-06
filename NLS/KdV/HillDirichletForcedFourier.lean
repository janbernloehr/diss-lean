import NLS.KdV.HillRoughScalarEquation
import NLS.Fourier.UnitIntervalHillBoundaryForcing
import NLS.KdV.HillDirichletSlope

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.LinearVolterra NLS.ZakharovShabat NLS.FunctionalAnalysis NLS.Fourier
open scoped ENNReal Classical

namespace NLS.KdV



/-- The original normalized Dirichlet position with initial data (0,1). -/
def hillL2DirichletPosition (q : Coeff 2) (energy : ℂ) (x : ℝ) : ℂ :=
  (extend (hillL2FrequencyStateCurve q (Complex.sqrt energy) (0,1)) x).1

/-- The actual derivative coordinate of the original Dirichlet solution. -/
def hillL2DirichletMomentum (q : Coeff 2) (energy : ℂ) (x : ℝ) : ℂ :=
  (extend (hillL2FrequencyStateCurve q (Complex.sqrt energy) (0,1)) x).2

/-- Actual unit-interval contribution to the period-two Fourier coefficient. -/
def hillL2DirichletHalfCoefficient (q : Coeff 2) (energy : ℂ) (k : ℤ) : ℂ :=
  halfCoefficient (hillL2DirichletPosition q energy) k

theorem hillL2DirichletPosition_zero (q : Coeff 2) (energy : ℂ) :
    hillL2DirichletPosition q energy 0 = 0 := by
  have hh := congrArg Prod.fst (hillL2FrequencyStateCurve_zero q (Complex.sqrt energy) (0,1))
  simpa only [hillL2DirichletPosition,← extend_coe] using hh

theorem hillL2DirichletMomentum_zero (q : Coeff 2) (energy : ℂ) :
    hillL2DirichletMomentum q energy 0 = 1 := by
  have hh := congrArg Prod.snd (hillL2FrequencyStateCurve_zero q (Complex.sqrt energy) (0,1))
  simpa only [hillL2DirichletMomentum,← extend_coe] using hh

theorem hillL2DirichletPosition_one (q : Coeff 2) (energy : ℂ) :
    hillL2DirichletPosition q energy 1 = hillL2DirichletCharacteristic q energy := by
  rw [hillL2DirichletPosition]
  change (extend (hillL2FrequencyStateCurve q (Complex.sqrt energy) (0,1))
    (⟨1,by norm_num⟩ : Icc (0 : ℝ) 1)).1 = _
  rw [extend_coe]
  rfl

theorem hillL2DirichletMomentum_one (q : Coeff 2) (energy : ℂ) :
    hillL2DirichletMomentum q energy 1 = hillL2DirichletSlope q energy := by
  rw [hillL2DirichletMomentum]
  change (extend (hillL2FrequencyStateCurve q (Complex.sqrt energy) (0,1))
    (⟨1,by norm_num⟩ : Icc (0 : ℝ) 1)).2 = _
  rw [extend_coe]
  rfl

/-- The actual rough normalized solution has both boundary terms before
imposing its Dirichlet spectral equation. -/
theorem hillL2DirichletHalfCoefficient_equation (q : Coeff 2) (energy : ℂ) (k : ℤ) :
    (energy-(freeHillValue k : ℂ))*hillL2DirichletHalfCoefficient q energy k =
      halfCoefficient (fun x => hillL2ScalarRepresentative q x*hillL2DirichletPosition q energy x) k -
        (hillL2DirichletSlope q energy*wave (-k) 1-1)/2 -
        (I*(Real.pi : ℂ)*k)*(hillL2DirichletCharacteristic q energy*wave (-k) 1)/2 := by
  have hA := absolutelyContinuousOnInterval_hillStateCurve q (Complex.sqrt energy) (0,1)
  have hf := absolutelyContinuousOnInterval_clm hA (ContinuousLinearMap.fst ℝ ℂ ℂ)
  have hg := absolutelyContinuousOnInterval_clm hA (ContinuousLinearMap.snd ℝ ℂ ℂ)
  have hfst := ae_hasDerivAt_hillL2FrequencyStateCurve_fst q (Complex.sqrt energy) (0,1)
  have hsnd := ae_hasDerivAt_hillL2FrequencyStateCurve_snd q (Complex.sqrt energy) (0,1)
  rw [NLS.ComplexAnalysis.complex_sqrt_sq] at hsnd
  have hh := halfCoefficient_hill_equation_with_boundary (hillL2ScalarRepresentative q)
    (hillL2DirichletPosition q energy) (hillL2DirichletMomentum q energy) energy hf hg
    (intervalIntegrable_hillL2ScalarRepresentative_mul_state q (Complex.sqrt energy) (0,1)) hfst hsnd k
  simp only [hillL2DirichletPosition_zero,hillL2DirichletPosition_one,
    hillL2DirichletMomentum_zero,hillL2DirichletMomentum_one,sub_zero] at hh
  convert hh using 1
  simp only [freeHillValue,hillL2DirichletHalfCoefficient]
  push_cast
  ring

/-- Every actual Dirichlet zero satisfies the Fourier equation with its
literal terminal derivative jump. No periodic derivative is assumed. -/
theorem hillL2DirichletHalfCoefficient_forced_equation (q : Coeff 2) (energy : ℂ)
    (hzero : hillL2DirichletCharacteristic q energy = 0) (k : ℤ) :
    (energy-(freeHillValue k : ℂ))*hillL2DirichletHalfCoefficient q energy k =
      halfCoefficient (fun x => hillL2ScalarRepresentative q x*hillL2DirichletPosition q energy x) k -
        (hillL2DirichletSlope q energy*wave (-k) 1-1)/2 := by
  simpa only [hzero,zero_mul,mul_zero,zero_div,sub_zero] using
    hillL2DirichletHalfCoefficient_equation q energy k

end NLS.KdV
