import NLS.KdV.HillNativeMeanZeroComplexMap
import NLS.Poisson.HminusGardnerBracket
import NLS.FunctionalAnalysis.LinearTargetDerivative

/-! Actual signed native coordinates have genuine H1 gradients and
well-defined analytic unit-period Gardner brackets on the COMMON native
complex domain. This does not assume their global canonicality. -/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.KdV

def hillHminusNativeCoordinate (k : ℤ) (q : PeriodOneHminusOne) : ℂ :=
  (hillHminusNativeComplexMap q).val k

theorem analyticOnNhd_hillHminusNativeCoordinate (k : ℤ) :
    AnalyticOnNhd ℂ (hillHminusNativeCoordinate k) hillHminusActionAngleNativeDomain := by
  intro q hq
  exact ((WeightedCoeff.evalCLM (Weight.signedSobolev (-1/2)) 2 k).analyticAt _).comp
    (analyticOnNhd_hillHminusNativeComplexMap q hq)

theorem fderiv_hillHminusNativeCoordinate (k : ℤ) (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusActionAngleNativeDomain) (h : PeriodOneHminusOne) :
    (fderiv ℂ (hillHminusNativeCoordinate k) q) h=((fderiv ℂ hillHminusNativeComplexMap q) h).val k :=
  NLS.FunctionalAnalysis.fderiv_comp_clm_apply hillHminusNativeComplexMap
    (WeightedCoeff.evalCLM (Weight.signedSobolev (-1/2)) 2 k) q h
      (analyticOnNhd_hillHminusNativeComplexMap q hq).differentiableAt

def hillHminusNativeCoordinateGradient (k : ℤ) (q : PeriodOneHminusOne) : WeightedCoeff (Weight.sobolev 1) 2 :=
  NLS.Poisson.hminusScalarGradient (hillHminusNativeCoordinate k) q

theorem hillHminusNativeCoordinateGradient_represents (k : ℤ) (q h : PeriodOneHminusOne) :
    (fderiv ℂ (hillHminusNativeCoordinate k) q) h=
      WeightedCoeff.sobolevBilinearPairing 1 (hillHminusNativeCoordinateGradient k q) h :=
  NLS.Poisson.hminusScalarGradient_represents _ q h

theorem analyticOnNhd_hillHminusNativeCoordinateGradient (k : ℤ) :
    AnalyticOnNhd ℂ (hillHminusNativeCoordinateGradient k) hillHminusActionAngleNativeDomain :=
  NLS.Poisson.analyticOnNhd_hminusScalarGradient _ (analyticOnNhd_hillHminusNativeCoordinate k)

theorem norm_hillHminusNativeCoordinateGradient (k : ℤ) (q : PeriodOneHminusOne) :
    ‖hillHminusNativeCoordinateGradient k q‖=‖fderiv ℂ (hillHminusNativeCoordinate k) q‖ :=
  NLS.Poisson.norm_hminusScalarGradient _ q

theorem hillHminusNativeCoordinateGradient_apply (k : ℤ) (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusActionAngleNativeDomain) (m : ℤ) :
    (hillHminusNativeCoordinateGradient k q).val m=
      ((fderiv ℂ hillHminusNativeComplexMap q)
        (WeightedCoeff.ofFinsupp (Weight.sobolev (-1)) 2 (Finsupp.single (-m) 1))).val k := by
  rw [hillHminusNativeCoordinateGradient,NLS.Poisson.hminusScalarGradient_apply,
    fderiv_hillHminusNativeCoordinate k q hq]

theorem hillHminusNativeCoordinateGradient_zero_nonzero_mode (k m : ℤ) (hm : m ≠ 0) :
    (hillHminusNativeCoordinateGradient k 0).val m=if m= -k then WeightedCoeff.halfFourierSymbol k else 0 := by
  have hreal : IsRealPeriodOneHminusOne (0 : PeriodOneHminusOne) := by intro j; simp
  have hmean : (WeightedCoeff.ofFinsupp (Weight.sobolev (-1)) 2 (Finsupp.single (-m) 1)).val 0=0 := by
    simp [WeightedCoeff.ofFinsupp_apply,hm]
  rw [hillHminusNativeCoordinateGradient_apply k 0 (real_mem_hillHminusActionAngleNativeDomain 0 hreal),
    fderiv_hillHminusNativeComplexMap_eq_halfFourier _ hmean,WeightedCoeff.halfFourierEquiv_apply,
    WeightedCoeff.ofFinsupp_apply,Finsupp.single_apply]
  by_cases he : m= -k
  · rw [if_pos he,if_pos (by omega : -m=k),mul_one]
  · rw [if_neg he,if_neg (by omega : -m ≠ k),mul_zero]

def hillHminusNativeGardnerBracket (k l : ℤ) (q : PeriodOneHminusOne) : ℂ :=
  NLS.Poisson.hminusGardnerBracket (hillHminusNativeCoordinate k) (hillHminusNativeCoordinate l) q

theorem analyticOnNhd_hillHminusNativeGardnerBracket (k l : ℤ) :
    AnalyticOnNhd ℂ (hillHminusNativeGardnerBracket k l) hillHminusActionAngleNativeDomain :=
  NLS.Poisson.analyticOnNhd_hminusGardnerBracket _ _
    (analyticOnNhd_hillHminusNativeCoordinate k) (analyticOnNhd_hillHminusNativeCoordinate l)

theorem hillHminusNativeGardnerBracket_antisymm (k l : ℤ) (q : PeriodOneHminusOne) :
    hillHminusNativeGardnerBracket k l q= -hillHminusNativeGardnerBracket l k q :=
  NLS.Poisson.hminusGardnerBracket_antisymm _ _ q

theorem hillHminusNativeGardnerBracket_self (k : ℤ) (q : PeriodOneHminusOne) :
    hillHminusNativeGardnerBracket k k q=0 := NLS.Poisson.hminusGardnerBracket_self _ q

end NLS.KdV
