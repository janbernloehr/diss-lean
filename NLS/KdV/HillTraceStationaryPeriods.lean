import NLS.KdV.HillAbelianGardnerPeriods
import NLS.KdV.HillTraceStationaryData

/-! # Actual intrinsic and free-tail Abelian period stationarity

The numerator coefficients are held fixed. The actual local root identity
and analytic contour differentiation propagate trace stationarity.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV
variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
  (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
  (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
theorem fderiv_hillAbelianComplexRoot_of_trace_stationary
    (p : Coeff 2) (E : ℂ) (V : Coeff 2)
    (hV : ∀ z : ℂ, (fderiv ℂ (fun p : Coeff 2 => hillL2Discriminant p z) (p)) V=0) (hp : (E,p)∈hillAbelianComplexRootDomain q hq hr) :
    (fderiv ℂ (fun s : Coeff 2 => hillAbelianComplexRoot q hq hr (E,s)) p)
      (V)=0 := by
  have hA : AnalyticAt ℂ (fun s : Coeff 2 => hillAbelianComplexRoot q hq hr (E,s)) p :=
    (analyticOnNhd_hillAbelianComplexRoot q hq hr (E,p) hp).comp
      (f := fun s : Coeff 2 => (E,s)) (analyticAt_const.prod analyticAt_id)
  apply fderiv_hillL2RadicandRoot_of_trace_stationary p E V hV _ hA.differentiableAt
    (hillAbelianComplexRoot_ne_zero q hq hr (E,p) hp)
  have hinc : Continuous (fun s : Coeff 2 => (E,s)) := continuous_const.prodMk continuous_id
  have hN := ((isOpen_hillAbelianComplexRootDomain q hq hr).preimage hinc).mem_nhds hp
  filter_upwards [hN] with s hs
  exact hillAbelianComplexRoot_sq q hq hr (E,s) hs


theorem fderiv_hillAbelianIntegrand_of_trace_stationary
    (n : ℕ) (a p : Coeff 2) (E : ℂ) (V : Coeff 2)
    (hV : ∀ z : ℂ, (fderiv ℂ (fun p : Coeff 2 => hillL2Discriminant p z) (p)) V=0)
    (hp : (E,p)∈hillAbelianComplexRootDomain q hq hr) :
    (fderiv ℂ (fun s : Coeff 2 => hillAbelianHilbertPsi n (E,a)/
      hillAbelianComplexRoot q hq hr (E,s)) p) (V)=0 := by
  have hR : AnalyticAt ℂ (fun s : Coeff 2 => hillAbelianComplexRoot q hq hr (E,s)) p :=
    (analyticOnNhd_hillAbelianComplexRoot q hq hr (E,p) hp).comp
      (f := fun s : Coeff 2 => (E,s)) (analyticAt_const.prod analyticAt_id)
  rw [fderiv_div_apply _ _ p (differentiableAt_const _) hR.differentiableAt
    (hillAbelianComplexRoot_ne_zero q hq hr (E,p) hp)]
  rw [fderiv_hillAbelianComplexRoot_of_trace_stationary q hq hr p E V hV hp]
  simp


theorem fderiv_hillAbelianComplexPeriod_source_of_trace_stationary
    (n k : ℕ) (hk : 1≤k) (a p0 : Coeff 2) (V : Coeff 2)
    (hV : ∀ z : ℂ, (fderiv ℂ (fun p : Coeff 2 => hillL2Discriminant p z) (p0)) V=0)
    (hc0 : ∀ E ∈ sphere (hillRealGapCenter q hq hr k : ℂ)
      (hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k),
        (E,p0)∈hillAbelianComplexRootDomain q hq hr) :
    (fderiv ℂ (fun p : Coeff 2 => hillAbelianComplexPeriod q hq hr n k (a,p)) p0)
      (V)=0 := by
  let F (t : ℂ × Coeff 2) := hillAbelianHilbertPsi n (t.1,a)/hillAbelianComplexRoot q hq hr t
  let D := hillAbelianComplexRootDomain q hq hr
  let c : ℂ := hillRealGapCenter q hq hr k
  let r := hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k
  let X := V
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
    exact fderiv_hillAbelianIntegrand_of_trace_stationary q hq hr n a p0 E V hV (hc0 E hE)
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


theorem fderiv_hillAbelianComplexPeriod_of_trace_stationary
    (n k : ℕ) (hk : 1≤k) (a : Coeff 2) (V : Coeff 2)
    (hV : ∀ z : ℂ, (fderiv ℂ (fun p : Coeff 2 => hillL2Discriminant p z) (SpectralWeight.one.toCoeff q)) V=0) :
    (fderiv ℂ (fun p : Coeff 2 => hillAbelianComplexPeriod q hq hr n k (a,p))
      (SpectralWeight.one.toCoeff q))
        (V)=0 := by
  apply fderiv_hillAbelianComplexPeriod_source_of_trace_stationary q hq hr n k hk a _ V hV
  intro E hE
  exact mem_hillAbelianComplexRootDomain_base q hq hr E
    (hillRealGapContour_sphere_subset q hq hr k hk hE)

end NLS.KdV
