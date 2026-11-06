import NLS.KdV.HillFreeDirichletEnergyDerivatives
import NLS.KdV.HillLogNormingGradient
import NLS.KdV.HillLogNormingCotangent

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology MeasureTheory
open NLS.LinearVolterra NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.KdV

private theorem free_energy (n : ℕ) : (freeHillValue n : ℂ) = ((n : ℂ)*Real.pi)^2 := by
  simp only [freeHillValue,Int.cast_natCast,ofReal_mul,ofReal_pow,ofReal_natCast]
  ring

private theorem sin_free_frequency (n : ℕ) : sin ((n : ℂ)*Real.pi) = 0 := by
  rw [←ofReal_natCast,←ofReal_mul,←ofReal_sin,Real.sin_nat_mul_pi,ofReal_zero]

/-- Exact free ORIGINAL Dirichlet mass. The constant is proved using the
energy derivative and the genuine Dirichlet normalization identity. -/
theorem scalarStateMass_hillDirichletStateCurve_free
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))
    (n : ℕ) (hn : 1 ≤ n) :
    (scalarStateMass (hillDirichletStateCurve (⟨0,h0q,h0r⟩ : RealPeriodOneHillPotential) n hn) : ℂ) =
      (2*((n : ℂ)*Real.pi)^2)⁻¹ := by
  let z : ℂ := (n : ℂ)*Real.pi
  have hz : z ≠ 0 := mul_ne_zero
    (by exact_mod_cast (by omega : n ≠ 0)) (ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hs : sin z = 0 := sin_free_frequency n
  have hc : (cos z)^2 = 1 := by
    simpa only [hs,zero_pow (by norm_num : 2 ≠ 0),zero_add] using Complex.sin_sq_add_cos_sq z
  have hzero : hillL2DirichletCharacteristic 0 (freeHillValue n : ℂ) = 0 := by
    rw [free_energy,hillL2DirichletCharacteristic_free_sq z hz,hs,zero_div]
  have hnorm := hillL2Dirichlet_derivative_normalization 0 (by intro k; simp) _ hzero
  rw [hillFreeGap_sqrt,hillL2FrequencyStateCurve_free_sine z hz] at hnorm
  simp only [ofReal_one,mul_one] at hnorm
  have hd : deriv (hillL2DirichletCharacteristic 0) (freeHillValue n : ℂ) =
      (z*cos z-sin z)/(2*z^3) := by
    rw [free_energy]
    exact hillL2DirichletCharacteristic_free_energy_deriv z hz
  rw [hd,hs,sub_zero] at hnorm
  rw [hillDirichletStateCurve,hillDirichletEnergy_free h0q h0r n hn,map_zero,hillFreeGap_sqrt]
  have hrat : (z*cos z/(2*z^3))*cos z = (2*z^2)⁻¹ := by
    field_simp [hz]
    linear_combination hc
  exact hnorm.symm.trans hrat

/-- The exact free cross mass vanishes for the original cosine/sine pair. -/
theorem scalarStateCrossMass_hillDirichletCurves_free
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))
    (n : ℕ) (hn : 1 ≤ n) :
    scalarStateCrossMass (hillDirichletCosineCurve (⟨0,h0q,h0r⟩ : RealPeriodOneHillPotential) n hn)
      (hillDirichletStateCurve (⟨0,h0q,h0r⟩ : RealPeriodOneHillPotential) n hn) = 0 := by
  let z : ℂ := (n : ℂ)*Real.pi
  have hz : z ≠ 0 := mul_ne_zero
    (by exact_mod_cast (by omega : n ≠ 0)) (ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hs : sin z = 0 := sin_free_frequency n
  have hc : cos z ≠ 0 := by
    intro he
    have hh := Complex.sin_sq_add_cos_sq z
    rw [hs,he] at hh
    norm_num at hh
  have hd : deriv (hillL2DirichletSlope 0) (freeHillValue n : ℂ) = 0 := by
    rw [free_energy,hillL2DirichletSlope_free_energy_deriv z hz,hs,neg_zero,zero_div]
  have he : hillL2DirichletSlope 0 (freeHillValue n : ℂ) = cos z := by
    rw [free_energy]
    exact hillL2DirichletSlope_free_sq z hz
  have hi := hillL2DirichletSlope_energy_integral 0 (freeHillValue n : ℂ)
  rw [hd,hillFreeGap_sqrt,hillL2FrequencyStateCurve_free_cosine z,ofReal_one,mul_one,hs,mul_zero,mul_zero,zero_sub,he] at hi
  have hzprod :
      (∫ x in (0 : ℝ)..1,(NLS.LinearVolterra.extend (hillL2FrequencyStateCurve 0 z (1,0)) x).1*
        (NLS.LinearVolterra.extend (hillL2FrequencyStateCurve 0 z (0,1)) x).1) = 0 := by
    apply (mul_eq_zero.mp (neg_eq_zero.mp hi.symm)).resolve_right hc
  rw [hillDirichletCosineCurve,hillDirichletStateCurve,hillDirichletEnergy_free h0q h0r n hn,map_zero,
    hillFreeGap_sqrt,scalarStateCrossMass_eq_integral]
  exact hzprod

/-- The ORIGINAL free logarithmic-norming projection is exactly zero. -/
theorem hillLogNormingProjection_free
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))
    (n : ℕ) (hn : 1 ≤ n) : hillLogNormingProjection (⟨0,h0q,h0r⟩ : RealPeriodOneHillPotential) n hn = 0 := by
  rw [hillLogNormingProjection,scalarStateCrossMass_hillDirichletCurves_free h0q h0r n hn,zero_div]

/-- The free ORIGINAL energy gradient has its exact sine-square profile. -/
theorem hillDirichletGradientCurve_free
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))
    (n : ℕ) (hn : 1 ≤ n) (t : Icc (0 : ℝ) 1) :
    hillDirichletGradientCurve (⟨0,h0q,h0r⟩ : RealPeriodOneHillPotential) n hn t =
      2*sin ((n : ℂ)*Real.pi*t.val)^2 := by
  let z : ℂ := (n : ℂ)*Real.pi
  have hz : z ≠ 0 := mul_ne_zero
    (by exact_mod_cast (by omega : n ≠ 0)) (ofReal_ne_zero.mpr Real.pi_ne_zero)
  change (scalarStateMass (hillDirichletStateCurve (⟨0,h0q,h0r⟩ : RealPeriodOneHillPotential) n hn) : ℂ)⁻¹ *
      (hillDirichletStateCurve (⟨0,h0q,h0r⟩ : RealPeriodOneHillPotential) n hn t).1^2 = _
  rw [scalarStateMass_hillDirichletStateCurve_free h0q h0r n hn,inv_inv,
    hillDirichletStateCurve_free h0q h0r n hn t]
  change (2*z^2)*(sin (z*t.val)/z)^2 = 2*sin (z*t.val)^2
  field_simp [hz]

/-- The free ORIGINAL logarithmic-norming gradient has its exact mixed
sine/cosine profile, with the original sign and factor retained. -/
theorem hillLogNormingGradientCurve_free
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))
    (n : ℕ) (hn : 1 ≤ n) (t : Icc (0 : ℝ) 1) :
    hillLogNormingGradientCurve (⟨0,h0q,h0r⟩ : RealPeriodOneHillPotential) n hn t =
      cos ((n : ℂ)*Real.pi*t.val)*sin ((n : ℂ)*Real.pi*t.val)/((n : ℂ)*Real.pi) := by
  change (hillDirichletCosineCurve (⟨0,h0q,h0r⟩ : RealPeriodOneHillPotential) n hn t).1 *
      (hillDirichletStateCurve (⟨0,h0q,h0r⟩ : RealPeriodOneHillPotential) n hn t).1 -
      hillLogNormingProjection (⟨0,h0q,h0r⟩ : RealPeriodOneHillPotential) n hn *
        (hillDirichletStateCurve (⟨0,h0q,h0r⟩ : RealPeriodOneHillPotential) n hn t).1^2 = _
  rw [hillLogNormingProjection_free h0q h0r n hn,zero_mul,sub_zero,
    hillDirichletCosineCurve_free h0q h0r n hn t,hillDirichletStateCurve_free h0q h0r n hn t]
  ring

end NLS.KdV
