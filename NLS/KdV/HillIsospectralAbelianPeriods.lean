import NLS.KdV.HillAbelianComplexPeriods
import NLS.ComplexAnalysis.TraceRootIsospectralDerivative
import NLS.ComplexAnalysis.TracePrimitiveMomentDifferential
import NLS.ComplexAnalysis.QuotientDerivative

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.ZakharovShabat NLS.LinearVolterra NLS.FunctionalAnalysis
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

theorem hillAbelianComplexRoot_isospectral_fderiv
    (p h : Coeff 2)
    (hiso : ∀ E : ℂ, (fderiv ℂ (fun b : Coeff 2 => hillL2Discriminant b E) p) h=0)
    (E : ℂ) (hE : (E,p)∈hillAbelianComplexRootDomain q hq hr) :
    (fderiv ℂ (fun b : Coeff 2 => hillAbelianComplexRoot q hq hr (E,b)) p) h=0 := by
  have hR : AnalyticAt ℂ (fun b : Coeff 2 => hillAbelianComplexRoot q hq hr (E,b)) p :=
    (analyticOnNhd_hillAbelianComplexRoot q hq hr (E,p) hE).comp
      (f := fun b : Coeff 2 => (E,b)) (analyticAt_const.prod analyticAt_id)
  have hT : AnalyticAt ℂ (fun b : Coeff 2 => hillL2Discriminant b E) p :=
    (analyticOnNhd_hillL2Discriminant_joint (E,p) (mem_univ _)).comp
      (f := fun b : Coeff 2 => (E,b)) (analyticAt_const.prod analyticAt_id)
  have hdom : ∀ᶠ b : Coeff 2 in 𝓝 p, (E,b)∈hillAbelianComplexRootDomain q hq hr :=
    (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds
      ((isOpen_hillAbelianComplexRootDomain q hq hr).mem_nhds hE)
  apply traceRoot_fderiv_eq_zero_of_trace_kernel _ _ p h hR hT ?_
    (hillAbelianComplexRoot_ne_zero q hq hr (E,p) hE) (hiso E)
  filter_upwards [hdom] with b hb
  exact hillAbelianComplexRoot_sq q hq hr (E,b) hb

/-- A fixed entire numerator has zero contour-period variation in
every actual isospectral source direction, throughout the verified root chart. -/
theorem hillAbelianContour_isospectral_fderiv
    (p h : Coeff 2)
    (hiso : ∀ E : ℂ, (fderiv ℂ (fun b : Coeff 2 => hillL2Discriminant b E) p) h=0)
    (F : ℂ → ℂ) (hF : AnalyticOnNhd ℂ F univ) (c : ℂ) (r : ℝ) (hradius : 0≤r)
    (hc : ∀ E∈sphere c r, (E,p)∈hillAbelianComplexRootDomain q hq hr) :
    DifferentiableAt ℂ (fun b : Coeff 2 => ∮ E in C(c,r),F E/hillAbelianComplexRoot q hq hr (E,b)) p ∧
      (fderiv ℂ (fun b : Coeff 2 => ∮ E in C(c,r),F E/hillAbelianComplexRoot q hq hr (E,b)) p) h=0 := by
  let G : ℂ × Coeff 2 → ℂ := fun t => F t.1/hillAbelianComplexRoot q hq hr t
  have hG : AnalyticOnNhd ℂ G (hillAbelianComplexRootDomain q hq hr) := by
    intro t ht
    exact ((hF t.1 (mem_univ _)).comp analyticAt_fst).div
      (analyticOnNhd_hillAbelianComplexRoot q hq hr t ht) (hillAbelianComplexRoot_ne_zero q hq hr t ht)
  obtain ⟨V,hV,hpV,M,_,hbound⟩ := exists_uniform_joint_fderiv_bound_on_circle G
    (hillAbelianComplexRootDomain q hq hr) (isOpen_hillAbelianComplexRootDomain q hq hr) hG c r p hc
  have hdom (b : Coeff 2) (hb : b∈V) (θ : ℝ) :
      (circleMap c r θ,b)∈hillAbelianComplexRootDomain q hq hr :=
    (hbound _ (circleMap_mem_sphere c hradius θ) b hb).1
  have hbd (b : Coeff 2) (hb : b∈V) (θ : ℝ) : ‖fderiv ℂ G (circleMap c r θ,b)‖≤M :=
    (hbound _ (circleMap_mem_sphere c hradius θ) b hb).2
  have hdiff := differentiableAt_circleIntegral_of_jointAnalytic G (hillAbelianComplexRootDomain q hq hr)
    (isOpen_hillAbelianComplexRootDomain q hq hr) hG c r hradius V hV p hpV M hdom hbd
  have hd := fderiv_circleIntegral_apply_of_jointAnalytic G (hillAbelianComplexRootDomain q hq hr)
    (isOpen_hillAbelianComplexRootDomain q hq hr) hG c r hradius V hV p hpV M hdom hbd h
  refine ⟨hdiff,?_⟩
  rw [hd]
  calc
    _ = ∮ E in C(c,r),(0 : ℂ) := by
      apply circleIntegral.integral_congr hradius
      intro E hE
      have hR : AnalyticAt ℂ (fun b : Coeff 2 => hillAbelianComplexRoot q hq hr (E,b)) p :=
        (analyticOnNhd_hillAbelianComplexRoot q hq hr (E,p) (hc E hE)).comp
          (f := fun b : Coeff 2 => (E,b)) (analyticAt_const.prod analyticAt_id)
      change (fderiv ℂ (fun b : Coeff 2 => F E/hillAbelianComplexRoot q hq hr (E,b)) p) h=0
      rw [fderiv_div_apply _ _ p (differentiableAt_const (F E)) hR.differentiableAt
        (hillAbelianComplexRoot_ne_zero q hq hr (E,p) (hc E hE)) h]
      rw [hillAbelianComplexRoot_isospectral_fderiv q hq hr p h hiso E (hc E hE)]
      simp only [fderiv_const_apply,zero_apply,zero_mul,mul_zero,sub_zero,zero_div]
    _ = 0 := by simp only [circleIntegral,smul_zero,intervalIntegral.integral_zero]

theorem hillAbelianComplexPeriod_isospectral_potential_fderiv
    (n k : ℕ) (hk : 1≤k) (a p h : Coeff 2)
    (hiso : ∀ E : ℂ, (fderiv ℂ (fun b : Coeff 2 => hillL2Discriminant b E) p) h=0)
    (hc : ∀ E∈sphere (hillRealGapCenter q hq hr k : ℂ)
      (hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k),
      (E,p)∈hillAbelianComplexRootDomain q hq hr) :
    DifferentiableAt ℂ (fun b : Coeff 2 => hillAbelianComplexPeriod q hq hr n k (a,b)) p ∧
      (fderiv ℂ (fun b : Coeff 2 => hillAbelianComplexPeriod q hq hr n k (a,b)) p) h=0 := by
  have hF : AnalyticOnNhd ℂ (fun E : ℂ => hillAbelianHilbertPsi n (E,a)) univ := by
    intro E _
    exact (analyticOnNhd_hillAbelianHilbertPsi n (E,a) (mem_univ _)).comp
      (f := fun E : ℂ => (E,a)) (analyticAt_id.prod analyticAt_const)
  have hcont := hillAbelianContour_isospectral_fderiv q hq hr p h hiso _ hF
    (hillRealGapCenter q hq hr k : ℂ) (hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k)
    (add_nonneg (hillRealGapContour_geometry q hq hr k hk).1 (hillRealGapContour_geometry q hq hr k hk).2.1.le) hc
  refine ⟨hcont.1.const_mul (2*(Real.pi : ℂ))⁻¹,?_⟩
  change (fderiv ℂ (fun b : Coeff 2 => (2*(Real.pi : ℂ))⁻¹*
    (∮ E in C((hillRealGapCenter q hq hr k : ℂ),hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k),
      hillAbelianHilbertPsi n (E,a)/hillAbelianComplexRoot q hq hr (E,b))) p) h=0
  rw [fderiv_const_mul hcont.1]
  simp only [smul_apply,smul_eq_mul,hcont.2,mul_zero]

end NLS.KdV
