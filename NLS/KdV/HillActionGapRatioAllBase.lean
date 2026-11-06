import NLS.KdV.HillActionGapRatioAnalytic

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV



variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

theorem analyticAt_hillLocalActionGapRatio (n : ℕ) (hn : 1 ≤ n) :
    AnalyticAt ℂ (hillLocalActionGapRatio q hq hr n) (SpectralWeight.one.toCoeff q) := by
  obtain ⟨A,_,hqA,hM,hS,_⟩ := exists_hillLocalGapSymmetricData_analytic_neighborhood q hq hr n hn
  have hdata := hillLocalGapSymmetricData_eq_physical_of_geometry q hq hr q hq hr n hn
    (hillRealGapContour_band_bounds q hq hr n hn) (hillRealGapSegment_subset_intrinsic_contour_ball q hq hr n hn)
  obtain ⟨hd,hη,_⟩ := hillRealGapContour_geometry q hq hr n hn
  let δ := hillRealGapHalfLength q hq hr n
  let S := δ+hillRealGapCollar q hq hr n/2
  let D := hillLocalDeflatedRootDomain q hq hr n
  have hD : IsOpen D := isOpen_hillLocalDeflatedRootDomain q hq hr n hn
  have hH' := analyticOnNhd_spectral_deriv_of_analyticOnNhd
    (hillLocalDeflatedTraceNumerator q hq hr n) D hD (analyticOnNhd_hillLocalDeflatedTraceNumerator q hq hr n hn)
  have hsq : AnalyticAt ℂ (fun p : Coeff 2 => (Complex.sqrt (hillLocalGapSquare q hq hr n p/4))^2) (SpectralWeight.one.toCoeff q) := by
    simpa only [complex_sqrt_sq] using (hS _ hqA).div_const (c := (4 : ℂ))
  have hbase : (Complex.sqrt (hillLocalGapSquare q hq hr n (SpectralWeight.one.toCoeff q)/4))^2 = (δ : ℂ)^2 := by
    rw [complex_sqrt_sq,hdata.2]
    change (2*(δ : ℂ))^2/4 = (δ : ℂ)^2
    ring
  have hnorm : ‖Complex.sqrt (hillLocalGapSquare q hq hr n (SpectralWeight.one.toCoeff q)/4)‖ = δ := by
    have h := congrArg norm hbase
    rw [norm_pow,norm_pow,norm_real,Real.norm_eq_abs,abs_of_nonneg hd] at h
    nlinarith [norm_nonneg (Complex.sqrt (hillLocalGapSquare q hq hr n (SpectralWeight.one.toCoeff q)/4))]
  have hm := analyticAt_parametricSineSquareCosineMean_of_analytic_square _
    (hillLocalGapMidpoint q hq hr n) (fun p => Complex.sqrt (hillLocalGapSquare q hq hr n p/4)) D hD hH'
    (SpectralWeight.one.toCoeff q) (hM _ hqA) hsq S
    (by rw [hnorm];dsimp [S];linarith)
    (by
      intro z hz
      rw [hdata.1] at hz
      exact mem_hillLocalDeflatedRootDomain_base q hq hr n hn z
        (closedBall_subset_ball (by dsimp [S,δ];linarith : S < hillRealGapHalfLength q hq hr n+hillRealGapCollar q hq hr n) hz))
  exact analyticAt_const.mul hm

theorem continuous_hillActionGapRatio :
    ∀ n : ℕ, 1 ≤ n → Continuous (fun p : RealPeriodOneHillPotential => hillActionGapRatio p.val p.property.1 p.property.2 n) := by
  intro n hn
  apply continuous_iff_continuousAt.mpr
  intro p
  let P : RealPeriodOneHillPotential → Coeff 2 := fun p => SpectralWeight.one.toCoeff p.val
  have hP : Continuous P := SpectralWeight.one.toCoeff.continuous.comp continuous_subtype_val
  have hc : ContinuousAt (fun r : RealPeriodOneHillPotential => hillLocalActionGapRatio p.val p.property.1 p.property.2 n (P r)) p :=
    ContinuousAt.comp (f := P) (analyticAt_hillLocalActionGapRatio p.val p.property.1 p.property.2 n hn).continuousAt hP.continuousAt
  exact hc.congr_of_eventuallyEq (Filter.EventuallyEq.symm (hillLocalActionGapRatio_eventually_eq_physical p.val p.property.1 p.property.2 n hn))

end NLS.KdV
