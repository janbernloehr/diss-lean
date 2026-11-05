import NLS.KdV.HillDiscriminantDirichletPairing
import NLS.KdV.HillDirichletMagriBoundary

/-! # The contour-energy Lenard factor for the actual Hill trace

The exact endpoint term changes the apparent Dirichlet-energy factor to
the running spectral energy. This identity is valid also at a closed gap
and at coincident energies, without dividing by a spectral difference.
-/
noncomputable section
open Set Complex Filter Topology MeasureTheory
open NLS.LinearVolterra NLS.ZakharovShabat NLS.ComplexAnalysis NLS.FunctionalAnalysis
open scoped ENNReal
namespace NLS.KdV

def hillDirichletDiscriminantMagriBracket (q : RealPeriodOneHillPotential)
    (n : ℕ) (hn : 1 ≤ n) (E : ℂ) : ℂ :=
  hillWeakGradientMagri (SpectralWeight.one.toCoeff q.val) (hillDirichletGradientCurve q n hn)
    (hillDirichletGradientSpatialCurve q n hn) (hillDirichletGradientSecond q n hn)
    (hillDiscriminantGradientCurve (SpectralWeight.one.toCoeff q.val) E)
    (hillDiscriminantGradientSpatialCurve (SpectralWeight.one.toCoeff q.val) E)

theorem hillDirichletDiscriminantMagriBracket_eq_energy_first
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1 ≤ n) (E : ℂ) :
    hillDirichletDiscriminantMagriBracket q n hn E =
      4*E*(∫ x in (0 : ℝ)..1,extend (hillDirichletGradientCurve q n hn) x*
        extend (hillDiscriminantGradientSpatialCurve (SpectralWeight.one.toCoeff q.val) E) x) := by
  have hb := hillWeakGradientMagri_Dirichlet_boundary q n hn
    (hillDiscriminantGradientCurve (SpectralWeight.one.toCoeff q.val) E)
    (hillDiscriminantGradientSpatialCurve (SpectralWeight.one.toCoeff q.val) E)
    (absolutelyContinuousOnInterval_hillDiscriminantGradientCurve _ E)
    (ae_hasDerivAt_hillDiscriminantGradientCurve _ E)
  rw [(hillDiscriminantGradientCurve_endpoints _ E).1,
    (hillDiscriminantGradientCurve_endpoints _ E).2] at hb
  have hp := integral_hillDirichletGradient_discriminantSpatial_energy q n hn E
  change hillDirichletDiscriminantMagriBracket q n hn E = _ at hb
  calc
    _ = _ := hb
    _ = _ := by linear_combination 2*hp

theorem hillDirichletDiscriminantMagriBracket_div_energy
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1 ≤ n) (E : ℂ) (hE : E ≠ 0) :
    hillDirichletDiscriminantMagriBracket q n hn E/E =
      4*(∫ x in (0 : ℝ)..1,extend (hillDirichletGradientCurve q n hn) x*
        extend (hillDiscriminantGradientSpatialCurve (SpectralWeight.one.toCoeff q.val) E) x) := by
  rw [hillDirichletDiscriminantMagriBracket_eq_energy_first]
  field_simp

theorem hillDirichletDiscriminantMagriBracket_resolvent
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1 ≤ n) (E : ℂ)
    (hE : (hillDirichletEnergy q.val q.property.1 q.property.2 n hn : ℂ) ≠ E) :
    hillDirichletDiscriminantMagriBracket q n hn E =
      2*E*((hillL2DirichletSlope (SpectralWeight.one.toCoeff q.val)
        (hillDirichletEnergy q.val q.property.1 q.property.2 n hn))^2-1)*
          hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q.val) E/
            (((hillDirichletEnergy q.val q.property.1 q.property.2 n hn : ℂ)-E)*
              (scalarStateMass (hillDirichletStateCurve q n hn) : ℂ)) := by
  have hp := integral_hillDirichletGradient_discriminantSpatial_energy q n hn E
  have hM : (scalarStateMass (hillDirichletStateCurve q n hn) : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (hillDirichletState_mass_pos q n hn).ne'
  rw [eq_div_iff hM] at hp
  rw [hillDirichletDiscriminantMagriBracket_eq_energy_first]
  apply (eq_div_iff (mul_ne_zero (sub_ne_zero.mpr hE) hM)).mpr
  linear_combination 2*E*hp

end NLS.KdV
