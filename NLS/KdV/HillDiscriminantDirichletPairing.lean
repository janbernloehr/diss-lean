import NLS.KdV.HillDirichletProductPairings
import NLS.KdV.HillDiscriminantGradientRegularity

/-! # Exact Dirichlet pairing with the actual periodic trace gradient -/
noncomputable section
open Set Complex Filter Topology MeasureTheory
open NLS.LinearVolterra NLS.ZakharovShabat NLS.ComplexAnalysis NLS.FunctionalAnalysis
open scoped ENNReal
namespace NLS.KdV

private theorem curve_pairing_smul (f g : Curve ℂ) (c : ℂ) :
    (∫ x in (0 : ℝ)..1,extend f x*extend (c • g) x) =
      c*(∫ x in (0 : ℝ)..1,extend f x*extend g x) := by
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x _
  change extend f x*(c*extend g x) = c*(extend f x*extend g x)
  ring

private theorem curve_pairing_add (f g h : Curve ℂ) :
    (∫ x in (0 : ℝ)..1,extend f x*extend (g+h) x) =
      (∫ x in (0 : ℝ)..1,extend f x*extend g x)+(∫ x in (0 : ℝ)..1,extend f x*extend h x) := by
  have he : (fun x => extend f x*extend (g+h) x) = fun x => extend f x*extend g x+extend f x*extend h x := by
    funext x
    change extend f x*(extend g x+extend h x) = _
    ring
  rw [he]
  exact intervalIntegral.integral_add ((continuous_extend f).mul (continuous_extend g) |>.intervalIntegrable 0 1)
    ((continuous_extend f).mul (continuous_extend h) |>.intervalIntegrable 0 1)

private theorem curve_pairing_sub (f g h : Curve ℂ) :
    (∫ x in (0 : ℝ)..1,extend f x*extend (g-h) x) =
      (∫ x in (0 : ℝ)..1,extend f x*extend g x)-(∫ x in (0 : ℝ)..1,extend f x*extend h x) := by
  have he : (fun x => extend f x*extend (g-h) x) = fun x => extend f x*extend g x-extend f x*extend h x := by
    funext x
    change extend f x*(extend g x-extend h x) = _
    ring
  rw [he]
  exact intervalIntegral.integral_sub ((continuous_extend f).mul (continuous_extend g) |>.intervalIntegrable 0 1)
    ((continuous_extend f).mul (continuous_extend h) |>.intervalIntegrable 0 1)

theorem integral_hillDirichletGradient_discriminantSpatial_energy
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1 ≤ n) (E : ℂ) :
    2*((hillDirichletEnergy q.val q.property.1 q.property.2 n hn : ℂ)-E)*
      (∫ x in (0 : ℝ)..1,extend (hillDirichletGradientCurve q n hn) x*
        extend (hillDiscriminantGradientSpatialCurve (SpectralWeight.one.toCoeff q.val) E) x) =
      ((hillL2DirichletSlope (SpectralWeight.one.toCoeff q.val)
        (hillDirichletEnergy q.val q.property.1 q.property.2 n hn))^2-1)*
          hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q.val) E/
            (scalarStateMass (hillDirichletStateCurve q n hn) : ℂ) := by
  let r := SpectralWeight.one.toCoeff q.val
  have hCC := integral_hillDirichletGradient_productSpatial_energy q n hn E (1,0) (1,0)
  have hCS := integral_hillDirichletGradient_productSpatial_energy q n hn E (1,0) (0,1)
  have hSS := integral_hillDirichletGradient_productSpatial_energy q n hn E (0,1) (0,1)
  have hM : (scalarStateMass (hillDirichletStateCurve q n hn) : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (hillDirichletState_mass_pos q n hn).ne'
  have hg0 := (hillDiscriminantGradientCurve_endpoints r E).1
  have hg1 := (hillDiscriminantGradientCurve_endpoints r E).2
  rw [hillDiscriminantGradientCurve_eq_products] at hg0 hg1
  dsimp only [ContinuousMap.sub_apply,ContinuousMap.add_apply,ContinuousMap.smul_apply,smul_eq_mul] at hg0 hg1
  rw [hillDiscriminantGradientSpatialCurve,curve_pairing_sub,curve_pairing_add,
    curve_pairing_smul,curve_pairing_smul,curve_pairing_smul]
  rw [eq_div_iff hM] at hCC hCS hSS ⊢
  linear_combination
    (hillL2FrequencyStateCurve r (Complex.sqrt E) (0,1) ⟨1,by norm_num⟩).1*hCC+
    ((hillL2FrequencyStateCurve r (Complex.sqrt E) (0,1) ⟨1,by norm_num⟩).2-
      (hillL2FrequencyStateCurve r (Complex.sqrt E) (1,0) ⟨1,by norm_num⟩).1)*hCS-
    (hillL2FrequencyStateCurve r (Complex.sqrt E) (1,0) ⟨1,by norm_num⟩).2*hSS+
    ((hillL2DirichletSlope r (hillDirichletEnergy q.val q.property.1 q.property.2 n hn))^2)*hg1-hg0

end NLS.KdV
