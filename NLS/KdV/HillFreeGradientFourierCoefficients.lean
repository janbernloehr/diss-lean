import NLS.Fourier.UnitFourierTrigonometricProfiles
import NLS.KdV.HillFreeDirichletGradientNormalization
import NLS.KdV.HillDiscriminantCotangentModes

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology MeasureTheory
open NLS.LinearVolterra NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.KdV

/-- The literal even source mode pairs with the reversed unit Fourier
coefficient of the actual physical curve. -/
theorem hillPhysicalDirectionPairing_single_unitFourier (j : ℤ) (v : Curve ℂ) :
    hillPhysicalDirectionPairing (lp.single 2 (2*j) 1) v =
      Fourier.unitFourierCoefficient (NLS.LinearVolterra.extend v) (-j) := by
  rw [hillPhysicalDirectionPairing_apply]
  unfold Fourier.unitFourierCoefficient
  apply intervalIntegral.integral_congr_ae_restrict
  rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  filter_upwards [hillPhysicalDirection_single_lower_ae (2*j)] with x hx
  rw [hx,show -(2*(-j)) = 2*j by ring,mul_comm]

variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

/-- Exact unit Fourier coefficients of the ORIGINAL free energy gradient. -/
theorem unitFourierCoefficient_hillDirichletGradient_free (n : ℕ) (hn : 1 ≤ n) (k : ℤ) :
    Fourier.unitFourierCoefficient
      (NLS.LinearVolterra.extend (hillDirichletGradientCurve (⟨0,h0q,h0r⟩ : RealPeriodOneHillPotential) n hn)) k =
      (if k = 0 then 1 else 0) - ((if (n : ℤ) = k then 1 else 0)+(if -(n : ℤ) = k then 1 else 0))/2 := by
  have he : NLS.LinearVolterra.extend (hillDirichletGradientCurve (⟨0,h0q,h0r⟩ : RealPeriodOneHillPotential) n hn)
      =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] (fun x => 2*sin ((n : ℂ)*Real.pi*x)^2) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    dsimp only [NLS.LinearVolterra.extend]
    rw [projIcc_of_mem _ (show x ∈ Icc (0 : ℝ) 1 from ⟨hx.1.le,hx.2⟩),
      hillDirichletGradientCurve_free h0q h0r n hn]
  rw [Fourier.unitFourierCoefficient_congr_ae he]
  exact Fourier.unitFourierCoefficient_twice_sin_sq (n : ℤ) k

/-- Exact signed unit Fourier coefficients of the ORIGINAL free norming gradient. -/
theorem unitFourierCoefficient_hillLogNormingGradient_free (n : ℕ) (hn : 1 ≤ n) (k : ℤ) :
    Fourier.unitFourierCoefficient
      (NLS.LinearVolterra.extend (hillLogNormingGradientCurve (⟨0,h0q,h0r⟩ : RealPeriodOneHillPotential) n hn)) k =
      ((if (n : ℤ) = k then 1 else 0)-(if -(n : ℤ) = k then 1 else 0))/(4*I*((n : ℂ)*Real.pi)) := by
  have he : NLS.LinearVolterra.extend (hillLogNormingGradientCurve (⟨0,h0q,h0r⟩ : RealPeriodOneHillPotential) n hn)
      =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)]
        (fun x => cos ((n : ℂ)*Real.pi*x)*sin ((n : ℂ)*Real.pi*x)/((n : ℂ)*Real.pi)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    dsimp only [NLS.LinearVolterra.extend]
    rw [projIcc_of_mem _ (show x ∈ Icc (0 : ℝ) 1 from ⟨hx.1.le,hx.2⟩),
      hillLogNormingGradientCurve_free h0q h0r n hn]
  rw [Fourier.unitFourierCoefficient_congr_ae he]
  exact Fourier.unitFourierCoefficient_cos_mul_sin_div (n : ℤ) k _

end NLS.KdV
