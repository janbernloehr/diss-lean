import NLS.KdV.HillActionDirichletBrackets
import NLS.KdV.HillDirichletSheetRoot

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.ZakharovShabat NLS.LinearVolterra NLS.FunctionalAnalysis
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



theorem hillDirichletSlope_mul_sheetRoot (p : Coeff 2) (E : ℂ)
    (hzero : hillL2DirichletCharacteristic p E=0) :
    hillL2DirichletSlope p E*hillDirichletSheetRoot p E=(hillL2DirichletSlope p E)^2-1 := by
  let z := Complex.sqrt E
  let t : Icc (0 : ℝ) 1 := ⟨1,by norm_num⟩
  let c := (hillL2FrequencyStateCurve p z (1,0) t).1
  let d := hillL2DirichletSlope p E
  have hb : (hillL2FrequencyStateCurve p z (0,1) t).1=0 := hzero
  have hw := hillL2FrequencyStateCurve_wronskian p z t
  rw [hb,zero_mul,sub_zero] at hw
  have hprod : c*d=1 := hw
  have htrace : c+d=hillL2Discriminant p E := by
    have ht := hillL2FrequencyStateCurve_trace p z
    rw [← hillL2Discriminant_sq,complex_sqrt_sq E] at ht
    exact ht
  unfold hillDirichletSheetRoot
  rw [← htrace]
  change d*(2*d-(c+d))=d^2-1
  linear_combination -hprod

theorem hillDirichlet_sheet_residue_normalization
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1≤n) :
    (scalarStateMass (hillDirichletStateCurve q n hn) : ℂ)⁻¹*
        ((hillL2DirichletSlope (SpectralWeight.one.toCoeff q.val)
          (hillDirichletEnergy q.val q.property.1 q.property.2 n hn))^2-1)=
      hillDirichletSheetRoot (SpectralWeight.one.toCoeff q.val)
        (hillDirichletEnergy q.val q.property.1 q.property.2 n hn)/
        deriv (hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q.val))
          (hillDirichletEnergy q.val q.property.1 q.property.2 n hn) := by
  let p := SpectralWeight.one.toCoeff q.val
  let E : ℂ := hillDirichletEnergy q.val q.property.1 q.property.2 n hn
  have hz : hillL2DirichletCharacteristic p E=0 :=
    hillDirichletEnergy_zero q.val q.property.1 q.property.2 n hn
  have hM := hillL2Dirichlet_derivative_normalization p q.property.2 E hz
  change deriv (hillL2DirichletCharacteristic p) E*hillL2DirichletSlope p E=
    (scalarStateMass (hillDirichletStateCurve q n hn) : ℂ) at hM
  have hsheet := hillDirichletSlope_mul_sheetRoot p E hz
  have hderiv := hillL2DirichletCharacteristic_deriv_ne_zero p q.property.2 E hz
  have hmass : (scalarStateMass (hillDirichletStateCurve q n hn) : ℂ)≠0 :=
    ofReal_ne_zero.mpr (hillDirichletState_mass_pos q n hn).ne'
  apply (eq_div_iff hderiv).mpr
  rw [← hsheet]
  calc
    _ = ((scalarStateMass (hillDirichletStateCurve q n hn) : ℂ)⁻¹*
        (deriv (hillL2DirichletCharacteristic p) E*hillL2DirichletSlope p E))*hillDirichletSheetRoot p E := by ring
    _ = _ := by rw [hM,inv_mul_cancel₀ hmass,one_mul]

/-- Every physical Dirichlet motion has its exact sheet factor times
the Cauchy residue coefficient. The formula remains valid at zero sheet
factor, so it does not divide by a terminal square root. -/
theorem hillPhysicalMomentGradient_dirichlet_bracket_eq_residue
    (q : RealPeriodOneHillPotential) (k n : ℕ) (hk : 1≤k) (hn : 1≤n) (m : ℕ) :
    (∫ x in (0 : ℝ)..1,NLS.LinearVolterra.extend
      (hillPhysicalMomentGradient q.val q.property.1 q.property.2 k m) x*
        deriv (NLS.LinearVolterra.extend (hillDirichletGradientCurve q n hn)) x)=
      (hillDirichletSheetRoot (SpectralWeight.one.toCoeff q.val)
        (hillDirichletEnergy q.val q.property.1 q.property.2 n hn)/
          (2*deriv (hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q.val))
            (hillDirichletEnergy q.val q.property.1 q.property.2 n hn)))*
        ∮ z in C((hillRealGapCenter q.val q.property.1 q.property.2 k : ℂ),
          hillRealGapHalfLength q.val q.property.1 q.property.2 k+hillRealGapCollar q.val q.property.1 q.property.2 k),
          hillPhysicalMomentGradientWeight (SpectralWeight.one.toCoeff q.val) m z*
            hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q.val) z/
              (z-(hillDirichletEnergy q.val q.property.1 q.property.2 n hn : ℂ)) := by
  rw [hillPhysicalMomentGradient_dirichlet_bracket q k n hk hn m,
    ← circleIntegral.integral_const_mul]
  apply circleIntegral.integral_congr
    (add_nonneg (hillRealGapContour_geometry q.val q.property.1 q.property.2 k hk).1
      (hillRealGapContour_geometry q.val q.property.1 q.property.2 k hk).2.1.le)
  intro z _
  dsimp only
  calc
    _ = ((scalarStateMass (hillDirichletStateCurve q n hn) : ℂ)⁻¹*
        ((hillL2DirichletSlope (SpectralWeight.one.toCoeff q.val)
          (hillDirichletEnergy q.val q.property.1 q.property.2 n hn))^2-1))*(2 : ℂ)⁻¹*
        (hillPhysicalMomentGradientWeight (SpectralWeight.one.toCoeff q.val) m z*
          hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q.val) z/
            (z-(hillDirichletEnergy q.val q.property.1 q.property.2 n hn : ℂ))) := by
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring
    _ = _ := by
      rw [hillDirichlet_sheet_residue_normalization q n hn]
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring

end NLS.KdV
