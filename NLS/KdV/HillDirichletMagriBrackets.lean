import NLS.KdV.HillWeakGradientMagri
import NLS.KdV.HillMixedGardnerBrackets

/-! # Actual weak Magri brackets of independent Dirichlet spectral data

The pairing uses the actual second derivative of the first gradient,
not a prescribed bracket matrix. All real period-one L² Hill potentials
are included, with arbitrary closed gaps.
-/
noncomputable section
open Set Complex Filter Topology MeasureTheory
open NLS.LinearVolterra NLS.ZakharovShabat NLS.ComplexAnalysis NLS.FunctionalAnalysis
open scoped ENNReal
namespace NLS.KdV

theorem integral_curve_mul_spatial_eq_deriv (f g dg : Curve ℂ)
    (hdg : ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1), HasDerivAt (extend g) (extend dg x) x) :
    (∫ x in (0 : ℝ)..1,extend f x*extend dg x) =
      ∫ x in (0 : ℝ)..1,extend f x*deriv (extend g) x := by
  apply intervalIntegral.integral_congr_ae_restrict
  rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  filter_upwards [hdg] with x hx
  rw [hx.deriv]

def hillDirichletMagriBracket (q : RealPeriodOneHillPotential) (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) : ℂ :=
  hillWeakGradientMagri (SpectralWeight.one.toCoeff q.val) (hillDirichletGradientCurve q n hn)
    (hillDirichletGradientSpatialCurve q n hn) (hillDirichletGradientSecond q n hn)
    (hillDirichletGradientCurve q m hm) (hillDirichletGradientSpatialCurve q m hm)

def hillDirichletLogMagriBracket (q : RealPeriodOneHillPotential) (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) : ℂ :=
  hillWeakGradientMagri (SpectralWeight.one.toCoeff q.val) (hillDirichletGradientCurve q n hn)
    (hillDirichletGradientSpatialCurve q n hn) (hillDirichletGradientSecond q n hn)
    (hillLogNormingGradientCurve q m hm) (hillLogNormingGradientSpatialCurve q m hm)

theorem hillDirichletMagriBracket_eq_first (q : RealPeriodOneHillPotential) (n m : ℕ)
    (hn : 1 ≤ n) (hm : 1 ≤ m) : hillDirichletMagriBracket q n m hn hm =
      4*(hillDirichletEnergy q.val q.property.1 q.property.2 n hn : ℂ)*hillDirichletGardnerBracket q n m hn hm := by
  have h := hillWeakGradientMagri_Dirichlet_eq_first q n hn _ _
    (absolutelyContinuousOnInterval_hillDirichletGradientCurve q m hm)
    (ae_hasDerivAt_hillDirichletGradientCurve q m hm)
    (hillDirichletGradientCurve_endpoints q m hm).1 (hillDirichletGradientCurve_endpoints q m hm).2
  rw [integral_curve_mul_spatial_eq_deriv _ _ _ (ae_hasDerivAt_hillDirichletGradientCurve q m hm)] at h
  exact h

theorem hillDirichletMagriBracket_eq_zero (q : RealPeriodOneHillPotential) (n m : ℕ)
    (hn : 1 ≤ n) (hm : 1 ≤ m) : hillDirichletMagriBracket q n m hn hm = 0 := by
  rw [hillDirichletMagriBracket_eq_first,hillDirichletGardnerBracket_eq_zero,mul_zero]

theorem hillDirichletLogMagriBracket_eq_first (q : RealPeriodOneHillPotential) (n m : ℕ)
    (hn : 1 ≤ n) (hm : 1 ≤ m) : hillDirichletLogMagriBracket q n m hn hm =
      4*(hillDirichletEnergy q.val q.property.1 q.property.2 n hn : ℂ)*hillDirichletLogGardnerBracket q n m hn hm := by
  have h := hillWeakGradientMagri_Dirichlet_eq_first q n hn _ _
    (absolutelyContinuousOnInterval_hillLogNormingGradientCurve q m hm)
    (ae_hasDerivAt_hillLogNormingGradientCurve q m hm)
    (hillLogNormingGradientCurve_endpoints q m hm).1 (hillLogNormingGradientCurve_endpoints q m hm).2
  rw [integral_curve_mul_spatial_eq_deriv _ _ _ (ae_hasDerivAt_hillLogNormingGradientCurve q m hm)] at h
  exact h

theorem hillDirichletLogMagriBracket_eq (q : RealPeriodOneHillPotential) (n m : ℕ)
    (hn : 1 ≤ n) (hm : 1 ≤ m) : hillDirichletLogMagriBracket q n m hn hm =
      if n = m then -2*(hillDirichletEnergy q.val q.property.1 q.property.2 n hn : ℂ) else 0 := by
  rw [hillDirichletLogMagriBracket_eq_first,hillDirichletLogGardnerBracket_eq]
  by_cases h : n = m <;> simp only [h,ite_true,ite_false] <;> ring

end NLS.KdV
