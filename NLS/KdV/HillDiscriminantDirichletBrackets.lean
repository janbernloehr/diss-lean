import NLS.KdV.HillDirichletQuadraticSystem
import NLS.ComplexAnalysis.QuadraticHillSystemBoundaryPairing

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology MeasureTheory
open NLS.LinearVolterra NLS.ZakharovShabat NLS.ComplexAnalysis NLS.FunctionalAnalysis
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



private theorem extend_at_zero (f : Curve ℂ) :
    NLS.LinearVolterra.extend f 0=f ⟨0,by norm_num⟩ := by
  dsimp only [NLS.LinearVolterra.extend]
  rw [projIcc_of_mem _ (show (0 : ℝ)∈Icc 0 1 by norm_num)]

private theorem extend_at_one (f : Curve ℂ) :
    NLS.LinearVolterra.extend f 1=f ⟨1,by norm_num⟩ := by
  dsimp only [NLS.LinearVolterra.extend]
  rw [projIcc_of_mem _ (show (1 : ℝ)∈Icc 0 1 by norm_num)]

def hillDiscriminantDirichletGardnerBracket
    (q : RealPeriodOneHillPotential) (z : ℂ) (n : ℕ) (hn : 1≤n) : ℂ :=
  ∫ x in (0 : ℝ)..1,NLS.LinearVolterra.extend
    (hillDiscriminantGradientCurve (SpectralWeight.one.toCoeff q.val) z) x*
      deriv (NLS.LinearVolterra.extend (hillDirichletGradientCurve q n hn)) x

/-- The actual trace/Dirichlet pairing has the exact boundary jump,
including coinciding energies, at arbitrary real rough Hill sources. -/
theorem hillDiscriminantDirichletGardnerBracket_boundary
    (q : RealPeriodOneHillPotential) (z : ℂ) (n : ℕ) (hn : 1≤n) :
    2*(z^2-(hillDirichletEnergy q.val q.property.1 q.property.2 n hn : ℂ))*
      hillDiscriminantDirichletGardnerBracket q z n hn=
      (hillL2FrequencyStateCurve (SpectralWeight.one.toCoeff q.val) z (0,1) ⟨1,by norm_num⟩).1*
        ((scalarStateMass (hillDirichletStateCurve q n hn) : ℂ)⁻¹*
          ((hillL2DirichletSlope (SpectralWeight.one.toCoeff q.val)
            (hillDirichletEnergy q.val q.property.1 q.property.2 n hn))^2-1)) := by
  let p := SpectralWeight.one.toCoeff q.val
  have hD := absolutelyContinuousOnInterval_hillDiscriminantQuadraticSystem p z
  have hG := absolutelyContinuousOnInterval_hillDirichletQuadraticSystem q n hn
  have he := hillDiscriminantGradientCurve_endpoints p z
  have hg := hillDirichletGradientCurve_endpoints q n hn
  have hh := hillDirichletGradientSpatialCurve_endpoints q n hn
  have hper : NLS.LinearVolterra.extend (hillDiscriminantGradientCurve p z) 1=
      NLS.LinearVolterra.extend (hillDiscriminantGradientCurve p z) 0 := by
    rw [extend_at_zero,extend_at_one,he.1,he.2]
  have h0 : NLS.LinearVolterra.extend (hillDirichletGradientCurve q n hn) 0=0 := by
    rw [extend_at_zero,hg.1]
  have h1 : NLS.LinearVolterra.extend (hillDirichletGradientCurve q n hn) 1=0 := by
    rw [extend_at_one,hg.2]
  have hH0 : NLS.LinearVolterra.extend (hillDirichletGradientSpatialCurve q n hn) 0=0 := by
    rw [extend_at_zero,hh.1]
  have hH1 : NLS.LinearVolterra.extend (hillDirichletGradientSpatialCurve q n hn) 1=0 := by
    rw [extend_at_one,hh.2]
  have hi := quadraticHillSystem_pairing_dirichlet_boundary (z^2)
    (hillDirichletEnergy q.val q.property.1 q.property.2 n hn : ℂ) (hillL2ScalarRepresentative p)
    (hillDiscriminantGradientCurve p z) (hillDiscriminantGradientSpatialCurve p z)
    (hillDiscriminantQuadraticMomentumCurve p z) (hillDirichletGradientCurve q n hn)
    (hillDirichletGradientSpatialCurve q n hn) (hillDirichletQuadraticMomentumCurve q n hn)
    (absolutelyContinuousOnInterval_hillDiscriminantGradientCurve p z) hD.1 hD.2
    (absolutelyContinuousOnInterval_hillDirichletGradientCurve q n hn) hG.1 hG.2
    (ae_hasDerivAt_hillDiscriminantQuadraticSystem p z)
    (ae_hasDerivAt_hillDirichletQuadraticSystem q n hn) hper h0 h1 hH0 hH1
  have hbr : hillDiscriminantDirichletGardnerBracket q z n hn=
      ∫ x in (0 : ℝ)..1,NLS.LinearVolterra.extend (hillDiscriminantGradientCurve p z) x*
        NLS.LinearVolterra.extend (hillDirichletGradientSpatialCurve q n hn) x := by
    apply intervalIntegral.integral_congr_ae_restrict
    rw [uIoc_of_le (by norm_num : (0 : ℝ)≤1)]
    filter_upwards [ae_hasDerivAt_hillDirichletGradientCurve q n hn] with x hx
    rw [hx.deriv]
  rw [hbr,hi,extend_at_zero,extend_at_one,extend_at_zero,he.1,
    (hillDirichletQuadraticMomentumCurve_endpoints q n hn).1,
    (hillDirichletQuadraticMomentumCurve_endpoints q n hn).2]
  ring

theorem hillDiscriminantDirichletGardnerBracket_eq
    (q : RealPeriodOneHillPotential) (z : ℂ) (n : ℕ) (hn : 1≤n)
    (hne : z^2≠(hillDirichletEnergy q.val q.property.1 q.property.2 n hn : ℂ)) :
    hillDiscriminantDirichletGardnerBracket q z n hn=
      ((hillL2FrequencyStateCurve (SpectralWeight.one.toCoeff q.val) z (0,1) ⟨1,by norm_num⟩).1*
        ((hillL2DirichletSlope (SpectralWeight.one.toCoeff q.val)
          (hillDirichletEnergy q.val q.property.1 q.property.2 n hn))^2-1))/
      (2*(scalarStateMass (hillDirichletStateCurve q n hn) : ℂ)*
        (z^2-(hillDirichletEnergy q.val q.property.1 q.property.2 n hn : ℂ))) := by
  have hm : (scalarStateMass (hillDirichletStateCurve q n hn) : ℂ)≠0 :=
    ofReal_ne_zero.mpr (hillDirichletState_mass_pos q n hn).ne'
  have hi := hillDiscriminantDirichletGardnerBracket_boundary q z n hn
  apply (eq_div_iff (mul_ne_zero (mul_ne_zero (by norm_num) hm) (sub_ne_zero.mpr hne))).mpr
  field_simp at hi
  linear_combination hi

end NLS.KdV
