import NLS.KdV.HillDirichletMagriBrackets
import NLS.KdV.HillLogNormingGardnerBrackets
import NLS.KdV.HillWeakMagriAntisymmetry

/-! # The log-norming block of the actual weak Hill Magri bracket

This is the independently constructed logarithmic Dirichlet-slope
cotangent. The actual weak pairing is reduced by the rough Hill equation
to its already checked first Gardner pairing, with the exact energy factor.
-/
noncomputable section
open Set Complex Filter Topology MeasureTheory
open NLS.LinearVolterra NLS.ZakharovShabat NLS.ComplexAnalysis NLS.FunctionalAnalysis
open scoped ENNReal
namespace NLS.KdV

def hillLogNormingMagriBracket (q : RealPeriodOneHillPotential) (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) : ℂ :=
  hillWeakGradientMagri (SpectralWeight.one.toCoeff q.val) (hillLogNormingGradientCurve q n hn)
    (hillLogNormingGradientSpatialCurve q n hn) (hillLogNormingGradientSecond q n hn)
    (hillLogNormingGradientCurve q m hm) (hillLogNormingGradientSpatialCurve q m hm)

theorem hillLogNormingMagriBracket_eq_first (q : RealPeriodOneHillPotential) (n m : ℕ)
    (hn : 1 ≤ n) (hm : 1 ≤ m) : hillLogNormingMagriBracket q n m hn hm =
      4*(hillDirichletEnergy q.val q.property.1 q.property.2 n hn : ℂ)*hillLogNormingGardnerBracket q n m hn hm := by
  have h := hillWeakGradientMagri_logNorming_eq_first q n hn _ _
    (absolutelyContinuousOnInterval_hillLogNormingGradientCurve q m hm)
    (ae_hasDerivAt_hillLogNormingGradientCurve q m hm)
    (hillLogNormingGradientCurve_endpoints q m hm).1 (hillLogNormingGradientCurve_endpoints q m hm).2
  rw [integral_curve_mul_spatial_eq_deriv _ _ _ (ae_hasDerivAt_hillLogNormingGradientCurve q m hm)] at h
  exact h

theorem hillLogNormingMagriBracket_eq_zero (q : RealPeriodOneHillPotential) (n m : ℕ)
    (hn : 1 ≤ n) (hm : 1 ≤ m) : hillLogNormingMagriBracket q n m hn hm = 0 := by
  rw [hillLogNormingMagriBracket_eq_first,hillLogNormingGardnerBracket_eq_zero,mul_zero]


def hillLogDirichletMagriBracket (q : RealPeriodOneHillPotential) (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) : ℂ :=
  hillWeakGradientMagri (SpectralWeight.one.toCoeff q.val) (hillLogNormingGradientCurve q n hn)
    (hillLogNormingGradientSpatialCurve q n hn) (hillLogNormingGradientSecond q n hn)
    (hillDirichletGradientCurve q m hm) (hillDirichletGradientSpatialCurve q m hm)

theorem hillLogDirichletMagriBracket_eq (q : RealPeriodOneHillPotential) (n m : ℕ)
    (hn : 1 ≤ n) (hm : 1 ≤ m) : hillLogDirichletMagriBracket q n m hn hm =
      if n = m then 2*(hillDirichletEnergy q.val q.property.1 q.property.2 n hn : ℂ) else 0 := by
  have htrace : extend (hillLogNormingGradientSpatialCurve q n hn) 1*extend (hillDirichletGradientSpatialCurve q m hm) 1 =
      extend (hillLogNormingGradientSpatialCurve q n hn) 0*extend (hillDirichletGradientSpatialCurve q m hm) 0 := by
    have he := hillDirichletGradientSpatialCurve_endpoints q m hm
    have h0 : extend (hillDirichletGradientSpatialCurve q m hm) 0 = 0 := by
      simpa only [NLS.LinearVolterra.extend,projIcc_of_mem _ (show (0 : ℝ) ∈ Icc 0 1 by norm_num)] using he.1
    have h1 : extend (hillDirichletGradientSpatialCurve q m hm) 1 = 0 := by
      simpa only [NLS.LinearVolterra.extend,projIcc_of_mem _ (show (1 : ℝ) ∈ Icc 0 1 by norm_num)] using he.2
    rw [h0,h1,mul_zero,mul_zero]
  have he := hillWeakGradientMagri_antisymm (SpectralWeight.one.toCoeff q.val)
    (hillLogNormingGradientCurve q n hn) (hillLogNormingGradientSpatialCurve q n hn)
    (hillLogNormingGradientSecond q n hn) (hillDirichletGradientCurve q m hm)
    (hillDirichletGradientSpatialCurve q m hm) (hillDirichletGradientSecond q m hm)
    (absolutelyContinuousOnInterval_hillLogNormingGradientSpatialCurve q n hn)
    (absolutelyContinuousOnInterval_hillDirichletGradientSpatialCurve q m hm)
    (memLp_hillLogNormingGradientSecond q n hn) (memLp_hillDirichletGradientSecond q m hm)
    (ae_hasDerivAt_hillLogNormingGradientSpatialCurve q n hn)
    (ae_hasDerivAt_hillDirichletGradientSpatialCurve q m hm) htrace
  change hillLogDirichletMagriBracket q n m hn hm = -hillDirichletLogMagriBracket q m n hm hn at he
  rw [he,hillDirichletLogMagriBracket_eq]
  by_cases h : n = m
  · subst m
    simp only [ite_true,neg_mul,neg_neg]
  · have h' : m ≠ n := Ne.symm h
    simp only [h,h',ite_false,neg_zero]

end NLS.KdV
