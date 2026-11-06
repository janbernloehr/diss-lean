import NLS.KdV.HillGardnerLocalRootVariation
import NLS.ComplexAnalysis.ParametricCircleStationarity
import NLS.ComplexAnalysis.QuotientDerivative
import NLS.KdV.HillAbelianComplexPeriods

/-! # Actual Gardner stationarity of the Abelian contour periods

The locally normalized analytic root is stationary by its proved radicand
identity. Uniform analytic contour differentiation then proves stationarity
of the actual periods with the numerator coefficients held fixed.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV
variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
  (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
  (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

/-- The actual local contour-root chart is stationary wherever it is defined. -/
theorem fderiv_hillAbelianComplexRoot_gardnerDirection_eq_zero
    (p : Coeff 2) (E b : ℂ) (hp : (E,p)∈hillAbelianComplexRootDomain q hq hr) :
    (fderiv ℂ (fun s : Coeff 2 => hillAbelianComplexRoot q hq hr (E,s)) p)
      (hillL2DiscriminantGardnerDirection p b)=0 := by
  have hA : AnalyticAt ℂ (fun s : Coeff 2 => hillAbelianComplexRoot q hq hr (E,s)) p :=
    (analyticOnNhd_hillAbelianComplexRoot q hq hr (E,p) hp).comp
      (f := fun s : Coeff 2 => (E,s)) (analyticAt_const.prod analyticAt_id)
  apply fderiv_hillL2RadicandRoot_gardnerDirection_eq_zero p E b _ hA.differentiableAt
    (hillAbelianComplexRoot_ne_zero q hq hr (E,p) hp)
  have hinc : Continuous (fun s : Coeff 2 => (E,s)) := continuous_const.prodMk continuous_id
  have hN := ((isOpen_hillAbelianComplexRootDomain q hq hr).preimage hinc).mem_nhds hp
  filter_upwards [hN] with s hs
  exact hillAbelianComplexRoot_sq q hq hr (E,s) hs

/-- With the actual numerator coefficients fixed, the Abelian integrand has zero source variation. -/
theorem fderiv_hillAbelianIntegrand_gardnerDirection_eq_zero
    (n : ℕ) (a p : Coeff 2) (E b : ℂ)
    (hp : (E,p)∈hillAbelianComplexRootDomain q hq hr) :
    (fderiv ℂ (fun s : Coeff 2 => hillAbelianHilbertPsi n (E,a)/
      hillAbelianComplexRoot q hq hr (E,s)) p) (hillL2DiscriminantGardnerDirection p b)=0 := by
  have hR : AnalyticAt ℂ (fun s : Coeff 2 => hillAbelianComplexRoot q hq hr (E,s)) p :=
    (analyticOnNhd_hillAbelianComplexRoot q hq hr (E,p) hp).comp
      (f := fun s : Coeff 2 => (E,s)) (analyticAt_const.prod analyticAt_id)
  rw [fderiv_div_apply _ _ p (differentiableAt_const _) hR.differentiableAt
    (hillAbelianComplexRoot_ne_zero q hq hr (E,p) hp)]
  rw [fderiv_hillAbelianComplexRoot_gardnerDirection_eq_zero q hq hr p E b hp]
  simp

/-- Actual intrinsic contour periods are stationary in the source direction. -/
theorem fderiv_hillAbelianComplexPeriod_source_gardnerDirection_eq_zero
    (n k : ℕ) (hk : 1≤k) (a p0 : Coeff 2) (b : ℂ)
    (hc0 : ∀ E ∈ sphere (hillRealGapCenter q hq hr k : ℂ)
      (hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k),
        (E,p0)∈hillAbelianComplexRootDomain q hq hr) :
    (fderiv ℂ (fun p : Coeff 2 => hillAbelianComplexPeriod q hq hr n k (a,p)) p0)
      (hillL2DiscriminantGardnerDirection p0 b)=0 := by
  let F (t : ℂ × Coeff 2) := hillAbelianHilbertPsi n (t.1,a)/hillAbelianComplexRoot q hq hr t
  let D := hillAbelianComplexRootDomain q hq hr
  let c : ℂ := hillRealGapCenter q hq hr k
  let r := hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k
  let X := hillL2DiscriminantGardnerDirection p0 b
  have hF : AnalyticOnNhd ℂ F D := by
    intro t ht
    have hN : AnalyticAt ℂ (fun s : ℂ × Coeff 2 => hillAbelianHilbertPsi n (s.1,a)) t :=
      (analyticOnNhd_hillAbelianHilbertPsi n (t.1,a) (mem_univ _)).comp
        (f := fun s : ℂ × Coeff 2 => (s.1,a)) (analyticAt_fst.prod analyticAt_const)
    exact hN.div (analyticOnNhd_hillAbelianComplexRoot q hq hr t ht)
      (hillAbelianComplexRoot_ne_zero q hq hr t ht)
  have hr0 : 0≤r := add_nonneg (hillRealGapContour_geometry q hq hr k hk).1
    (hillRealGapContour_geometry q hq hr k hk).2.1.le
  have hzero : (fderiv ℂ (fun p : Coeff 2 => ∮ z in C(c,r),F (z,p)) p0) X=0 := by
    apply fderiv_circleIntegral_apply_eq_zero_of_jointAnalytic F D
      (isOpen_hillAbelianComplexRootDomain q hq hr) hF c r hr0 p0 X hc0
    intro E hE
    exact fderiv_hillAbelianIntegrand_gardnerDirection_eq_zero q hq hr n a p0 E b (hc0 E hE)
  obtain ⟨U,hU,hpU,_M,_,hb⟩ := exists_uniform_joint_fderiv_bound_on_circle F D
    (isOpen_hillAbelianComplexRootDomain q hq hr) hF c r p0 hc0
  have hcircle (p : Coeff 2) (hp : p∈U) (E : ℂ) (hE : E∈sphere c r) : (E,p)∈D :=
    (hb E hE p hp).1
  have hA := analyticOnNhd_circleIntegral_of_jointAnalytic F
    (isOpen_hillAbelianComplexRootDomain q hq hr) hF c r hr0 hU hcircle
  have hd := congrArg (fun L : Coeff 2 →L[ℂ] ℂ => L X)
    (((hA p0 hpU).differentiableAt.hasFDerivAt).const_smul ((2*(Real.pi : ℂ))⁻¹)).fderiv
  change (fderiv ℂ (fun p : Coeff 2 => hillAbelianComplexPeriod q hq hr n k (a,p)) p0) X=
    (2*(Real.pi : ℂ))⁻¹*((fderiv ℂ (fun p : Coeff 2 => ∮ z in C(c,r),F (z,p)) p0) X) at hd
  rw [hzero,mul_zero] at hd
  exact hd

/-- At the physical base every actual intrinsic contour satisfies the required chart condition. -/
theorem fderiv_hillAbelianComplexPeriod_gardnerDirection_eq_zero
    (n k : ℕ) (hk : 1≤k) (a : Coeff 2) (b : ℂ) :
    (fderiv ℂ (fun p : Coeff 2 => hillAbelianComplexPeriod q hq hr n k (a,p))
      (SpectralWeight.one.toCoeff q))
        (hillL2DiscriminantGardnerDirection (SpectralWeight.one.toCoeff q) b)=0 := by
  apply fderiv_hillAbelianComplexPeriod_source_gardnerDirection_eq_zero q hq hr n k hk a _ b
  intro E hE
  exact mem_hillAbelianComplexRootDomain_base q hq hr E
    (hillRealGapContour_sphere_subset q hq hr k hk hE)

end NLS.KdV
