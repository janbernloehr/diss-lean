import NLS.KdV.HillDirichletSheetRoot
import NLS.KdV.HillDiscriminantDirichletPairing

/-! # Original sheet and mass normalization of the divisor resolvent

The determinant-one scalar monodromy and the actual characteristic
derivative remove the terminal slope and squared-state mass. The resulting
energy identity includes closed gaps and coincident energies.
-/
noncomputable section
open Set Complex Filter Topology MeasureTheory
open NLS.LinearVolterra NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.KdV

theorem hillDirichletSlope_mul_sheetRoot (q : Coeff 2) (E : ℂ)
    (hzero : hillL2DirichletCharacteristic q E = 0) :
    hillL2DirichletSlope q E*hillDirichletSheetRoot q E = (hillL2DirichletSlope q E)^2-1 := by
  let z := Complex.sqrt E
  let t : Icc (0 : ℝ) 1 := ⟨1,by norm_num⟩
  let c := (hillL2FrequencyStateCurve q z (1,0) t).1
  let d := hillL2DirichletSlope q E
  have hb : (hillL2FrequencyStateCurve q z (0,1) t).1 = 0 := hzero
  have hw := hillL2FrequencyStateCurve_wronskian q z t
  rw [hb,zero_mul,sub_zero] at hw
  have hprod : c*d = 1 := hw
  have htrace : c+d = hillL2Discriminant q E := by
    have ht := hillL2FrequencyStateCurve_trace q z
    rw [← hillL2Discriminant_sq,complex_sqrt_sq E] at ht
    exact ht
  unfold hillDirichletSheetRoot
  rw [← htrace]
  change d*(2*d-(c+d)) = d^2-1
  linear_combination -hprod

theorem hillDirichlet_sheet_mass_ratio (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1 ≤ n) :
    let μ : ℂ := hillDirichletEnergy q.val q.property.1 q.property.2 n hn
    let s := hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q.val)
    ((hillL2DirichletSlope (SpectralWeight.one.toCoeff q.val) μ)^2-1)/
      (scalarStateMass (hillDirichletStateCurve q n hn) : ℂ) =
        hillDirichletSheetRoot (SpectralWeight.one.toCoeff q.val) μ/deriv s μ := by
  let μ : ℂ := hillDirichletEnergy q.val q.property.1 q.property.2 n hn
  have hz := hillDirichletEnergy_zero q.val q.property.1 q.property.2 n hn
  have hd := hillL2DirichletCharacteristic_deriv_ne_zero _ q.property.2 μ hz
  have hM : (scalarStateMass (hillDirichletStateCurve q n hn) : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (hillDirichletState_mass_pos q n hn).ne'
  have hm := hillL2Dirichlet_derivative_normalization _ q.property.2 μ hz
  change deriv (hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q.val)) μ*
    hillL2DirichletSlope (SpectralWeight.one.toCoeff q.val) μ =
      (scalarStateMass (hillDirichletStateCurve q n hn) : ℂ) at hm
  have hs := hillDirichletSlope_mul_sheetRoot _ μ hz
  dsimp only
  apply (div_eq_div_iff hM hd).mpr
  rw [← hm]
  linear_combination -deriv (hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q.val)) μ*hs

theorem integral_hillDirichletGradient_discriminantSpatial_sheet_energy
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1 ≤ n) (E : ℂ) :
    let μ : ℂ := hillDirichletEnergy q.val q.property.1 q.property.2 n hn
    let s := hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q.val)
    2*(μ-E)*(∫ x in (0 : ℝ)..1,extend (hillDirichletGradientCurve q n hn) x*
      extend (hillDiscriminantGradientSpatialCurve (SpectralWeight.one.toCoeff q.val) E) x) =
        hillDirichletSheetRoot (SpectralWeight.one.toCoeff q.val) μ*s E/deriv s μ := by
  dsimp only
  rw [integral_hillDirichletGradient_discriminantSpatial_energy]
  have hs := hillDirichlet_sheet_mass_ratio q n hn
  dsimp only at hs ⊢
  rw [mul_div_right_comm,hs]
  ring

theorem integral_hillDirichletGradient_discriminantSpatial_sheet_resolvent
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1 ≤ n) (E : ℂ)
    (hE : (hillDirichletEnergy q.val q.property.1 q.property.2 n hn : ℂ) ≠ E) :
    let μ : ℂ := hillDirichletEnergy q.val q.property.1 q.property.2 n hn
    let s := hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q.val)
    (∫ x in (0 : ℝ)..1,extend (hillDirichletGradientCurve q n hn) x*
      extend (hillDiscriminantGradientSpatialCurve (SpectralWeight.one.toCoeff q.val) E) x) =
        hillDirichletSheetRoot (SpectralWeight.one.toCoeff q.val) μ*s E/(2*(μ-E)*deriv s μ) := by
  have hs := integral_hillDirichletGradient_discriminantSpatial_sheet_energy q n hn E
  dsimp only at hs ⊢
  have hd := hillL2DirichletCharacteristic_deriv_ne_zero _ q.property.2 _
    (hillDirichletEnergy_zero q.val q.property.1 q.property.2 n hn)
  rw [eq_div_iff hd] at hs
  apply (eq_div_iff (mul_ne_zero (mul_ne_zero (by norm_num) (sub_ne_zero.mpr hE)) hd)).mpr
  linear_combination hs

end NLS.KdV
