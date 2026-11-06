import NLS.KdV.HillEntireNumeratorRootVariation
import NLS.ComplexAnalysis.ParametricCircleIntegralHigher

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV

variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

theorem fderiv_hillAbelianHilbertPeriod_eq_intrinsic_variation
    (n k : ℕ) (hk : 1 ≤ k) (a h : Coeff 2) :
    fderiv ℂ (hillAbelianHilbertPeriod q hq hr n k) a h =
      hillIntrinsicGapPeriod q hq hr k (hillAbelianNumeratorRootVariation n a h) := by
  let D : Set (ℂ × Coeff 2) := hillL2RealCutDomain q hq hr ×ˢ univ
  let F : ℂ × Coeff 2 → ℂ := fun t => hillAbelianHilbertPsi n t/hillEnergyCanonicalRootProduct q hq hr t.1
  let c := (hillRealGapCenter q hq hr k : ℂ)
  let R := hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k
  have hD : IsOpen D := (isOpen_hillL2RealCutDomain q hq hr).prod isOpen_univ
  have hF : AnalyticOnNhd ℂ F D := by
    intro t ht
    have hd : AnalyticAt ℂ (fun v : ℂ × Coeff 2 => hillEnergyCanonicalRootProduct q hq hr v.1) t :=
      (analyticOnNhd_hillEnergyCanonicalRootProduct q hq hr t.1 ht.1).comp analyticAt_fst
    exact (analyticOnNhd_hillAbelianHilbertPsi n t (mem_univ _)).div hd
      (hillEnergyCanonicalRootProduct_ne_zero_on_realCutDomain q hq hr t.1 ht.1)
  have hR : 0 ≤ R := add_nonneg (hillRealGapContour_geometry q hq hr k hk).1
    (hillRealGapContour_geometry q hq hr k hk).2.1.le
  have hcircle (b : Coeff 2) (E : ℂ) (hE : E ∈ sphere c R) : (E,b) ∈ D :=
    ⟨hillRealGapContour_sphere_subset q hq hr k hk hE,mem_univ _⟩
  obtain ⟨W,hW,haW,M,_,hbound⟩ := exists_uniform_joint_fderiv_bound_on_circle F D hD hF c R a (hcircle a)
  have hdom (b : Coeff 2) (hb : b ∈ W) (θ : ℝ) : (circleMap c R θ,b) ∈ D :=
    (hbound _ (circleMap_mem_sphere c hR θ) b hb).1
  have hbd (b : Coeff 2) (hb : b ∈ W) (θ : ℝ) : ‖fderiv ℂ F (circleMap c R θ,b)‖ ≤ M :=
    (hbound _ (circleMap_mem_sphere c hR θ) b hb).2
  have hi := hasFDerivAt_circleIntegral_of_jointAnalytic F D hD hF c R hR W hW a haW M hdom hbd
  have hc := hi.const_mul ((2*(Real.pi : ℂ))⁻¹)
  have hv := congrArg (fun T : Coeff 2 →L[ℂ] ℂ => T h) hc.fderiv
  rw [← hi.fderiv] at hv
  simp only [smul_apply,smul_eq_mul] at hv
  rw [fderiv_circleIntegral_apply_of_jointAnalytic F D hD hF c R hR W hW a haW M hdom hbd h] at hv
  have he (E : ℂ) : (fderiv ℂ (fun b : Coeff 2 => F (E,b)) a) h =
      hillAbelianNumeratorRootVariation n a h E/hillEnergyCanonicalRootProduct q hq hr E := by
    have hN : AnalyticAt ℂ (fun b : Coeff 2 => hillAbelianHilbertPsi n (E,b)) a :=
      (analyticOnNhd_hillAbelianHilbertPsi n (E,a) (mem_univ _)).comp
        (f := fun b : Coeff 2 => (E,b)) (analyticAt_const.prod analyticAt_id)
    have hd := hN.differentiableAt.hasFDerivAt.mul_const ((hillEnergyCanonicalRootProduct q hq hr E)⁻¹)
    have hh := congrArg (fun T : Coeff 2 →L[ℂ] ℂ => T h) hd.fderiv
    rw [hillAbelianNumeratorRootVariation_eq_fderiv]
    simpa only [F,smul_apply,smul_eq_mul,div_eq_mul_inv,mul_comm] using hh
  simp_rw [he] at hv
  exact hv

end NLS.KdV
