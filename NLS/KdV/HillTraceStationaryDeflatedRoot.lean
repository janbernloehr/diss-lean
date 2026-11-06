import NLS.KdV.HillGardnerDeflatedRoot
import NLS.KdV.HillTraceStationaryData

/-! # Actual gap deflation along trace-stationary tangents -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV
variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
  (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
  (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
theorem fderiv_hillLocalGapPolynomial_of_trace_stationary
    (k : ℕ) (hk : 1≤k) (E : ℂ) (V : Coeff 2)
    (hV : ∀ z : ℂ, (fderiv ℂ (fun p : Coeff 2 => hillL2Discriminant p z) (SpectralWeight.one.toCoeff q)) V=0) :
    (fderiv ℂ (fun p : Coeff 2 => hillLocalGapPolynomial q hq hr k p E) (SpectralWeight.one.toCoeff q))
      (V)=0 := by
  let p0 := SpectralWeight.one.toCoeff q
  let X := V
  obtain ⟨U,_,hpU,hM,hS,_⟩ := exists_hillLocalGapSymmetricData_analytic_neighborhood q hq hr k hk
  let H (u : ℂ × ℂ) := (E-u.1)^2-u.2/4
  have hH : AnalyticAt ℂ H (hillLocalGapMidpoint q hq hr k p0,hillLocalGapSquare q hq hr k p0) :=
    ((analyticAt_const.sub analyticAt_fst).pow 2).sub (analyticAt_snd.div_const)
  have hd := congrArg (fun L : Coeff 2 →L[ℂ] ℂ => L X)
    (hH.differentiableAt.hasFDerivAt.comp p0
      ((hM p0 hpU).differentiableAt.hasFDerivAt.prodMk (hS p0 hpU).differentiableAt.hasFDerivAt)).fderiv
  change (fderiv ℂ (fun p : Coeff 2 => hillLocalGapPolynomial q hq hr k p E) p0) X=
    (fderiv ℂ H (hillLocalGapMidpoint q hq hr k p0,hillLocalGapSquare q hq hr k p0))
      ((fderiv ℂ (hillLocalGapMidpoint q hq hr k) p0) X,(fderiv ℂ (hillLocalGapSquare q hq hr k) p0) X) at hd
  rw [fderiv_hillLocalGapMidpoint_of_trace_stationary q hq hr k hk V hV,
    fderiv_hillLocalGapSquare_of_trace_stationary q hq hr k hk V hV] at hd
  change (fderiv ℂ (fun p : Coeff 2 => hillLocalGapPolynomial q hq hr k p E) p0) X=
    (fderiv ℂ H _) (0 : ℂ × ℂ) at hd
  rw [map_zero] at hd
  exact hd


theorem fderiv_hillLocalGapQuotient_of_trace_stationary
    (k : ℕ) (hk : 1≤k) (w : ℂ) (V : Coeff 2)
    (hV : ∀ z : ℂ, (fderiv ℂ (fun p : Coeff 2 => hillL2Discriminant p z) (SpectralWeight.one.toCoeff q)) V=0)
    (hw : w∈sphere (hillRealGapCenter q hq hr k : ℂ)
      (hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k)) :
    (fderiv ℂ (fun p : Coeff 2 => hillL2Radicand p w/hillLocalGapPolynomial q hq hr k p w)
      (SpectralWeight.one.toCoeff q))
        (V)=0 := by
  have hR := (analyticOnNhd_hillL2Radicand_joint (w,SpectralWeight.one.toCoeff q) (mem_univ _)).comp
    (f := fun p : Coeff 2 => (w,p)) (analyticAt_const.prod analyticAt_id)
  have hP := (analyticAt_hillLocalGapPolynomial_base q hq hr k hk w).comp
    (f := fun p : Coeff 2 => (w,p)) (analyticAt_const.prod analyticAt_id)
  rw [fderiv_div_apply (fun p : Coeff 2 => hillL2Radicand p w)
    (fun p : Coeff 2 => hillLocalGapPolynomial q hq hr k p w) _ hR.differentiableAt hP.differentiableAt
      (hillLocalGapPolynomial_ne_zero_base_circle q hq hr k hk w hw),
    fderiv_hillL2Radicand_of_trace_stationary (SpectralWeight.one.toCoeff q) w V hV,
    fderiv_hillLocalGapPolynomial_of_trace_stationary q hq hr k hk w V hV]
  simp


theorem fderiv_hillLocalGapUnit_of_trace_stationary
    (k : ℕ) (hk : 1≤k) (E : ℂ) (V : Coeff 2)
    (hV : ∀ z : ℂ, (fderiv ℂ (fun p : Coeff 2 => hillL2Discriminant p z) (SpectralWeight.one.toCoeff q)) V=0)
    (hE : E∈ball (hillRealGapCenter q hq hr k : ℂ)
      (hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k)) :
    (fderiv ℂ (fun p : Coeff 2 => hillLocalGapUnit q hq hr k (E,p)) (SpectralWeight.one.toCoeff q))
      (V)=0 := by
  let F (t : ℂ × Coeff 2) := hillL2Radicand t.2 t.1/hillLocalGapPolynomial q hq hr k t.2 t.1
  let D := {t | AnalyticAt ℂ F t}
  have hc (w : ℂ) (hw : w∈sphere (hillRealGapCenter q hq hr k : ℂ)
      (hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k)) : (w,SpectralWeight.one.toCoeff q)∈D :=
    (analyticOnNhd_hillL2Radicand_joint _ (mem_univ _)).div
      (analyticAt_hillLocalGapPolynomial_base q hq hr k hk w)
      (hillLocalGapPolynomial_ne_zero_base_circle q hq hr k hk w hw)
  exact fderiv_parametricCircleCauchyTransform_source_apply_eq_zero F D (isOpen_analyticAt ℂ F)
    (fun _ ht => ht) _ _
    (add_nonneg (hillRealGapContour_geometry q hq hr k hk).1 (hillRealGapContour_geometry q hq hr k hk).2.1.le)
    _ _ E (fun he => (ne_of_lt hE) he) hc
    (fun w hw => fderiv_hillLocalGapQuotient_of_trace_stationary q hq hr k hk w V hV hw)


theorem fderiv_hillLocalDeflatedComplexRoot_of_trace_stationary
    (k : ℕ) (hk : 1≤k) (E : ℂ) (V : Coeff 2)
    (hV : ∀ z : ℂ, (fderiv ℂ (fun p : Coeff 2 => hillL2Discriminant p z) (SpectralWeight.one.toCoeff q)) V=0)
    (hE : E∈ball (hillRealGapCenter q hq hr k : ℂ)
      (hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k)) :
    (fderiv ℂ (fun p : Coeff 2 => hillLocalDeflatedComplexRoot q hq hr k (E,p)) (SpectralWeight.one.toCoeff q))
      (V)=0 := by
  have hdom := mem_hillLocalDeflatedRootDomain_base q hq hr k hk E hE
  have hA := (analyticOnNhd_hillLocalDeflatedComplexRoot q hq hr k hk _ hdom).comp
    (f := fun p : Coeff 2 => (E,p)) (analyticAt_const.prod analyticAt_id)
  apply fderiv_apply_eq_zero_of_eventually_sq
    (fun p : Coeff 2 => hillLocalDeflatedComplexRoot q hq hr k (E,p))
    (fun p : Coeff 2 => hillLocalGapUnit q hq hr k (E,p)) _ _ hA.differentiableAt
    (hillLocalDeflatedComplexRoot_ne_zero q hq hr k hk _ hdom) _
    (fderiv_hillLocalGapUnit_of_trace_stationary q hq hr k hk E V hV hE)
  have hinc : Continuous (fun p : Coeff 2 => (E,p)) := continuous_const.prodMk continuous_id
  filter_upwards [((isOpen_hillLocalDeflatedRootDomain q hq hr k hk).preimage hinc).mem_nhds hdom] with p hp
  exact hillLocalDeflatedComplexRoot_sq q hq hr k hk (E,p) hp


theorem fderiv_hillGapHalfLength_root_of_trace_stationary
    (k : ℕ) (hk : 1≤k) (d : Coeff 2 → ℂ) (hd : DifferentiableAt ℂ d (SpectralWeight.one.toCoeff q))
    (hne : d (SpectralWeight.one.toCoeff q)≠0)
    (hsq : ∀ᶠ p in 𝓝 (SpectralWeight.one.toCoeff q), d p^2=hillLocalGapSquare q hq hr k p/4) (V : Coeff 2)
    (hV : ∀ z : ℂ, (fderiv ℂ (fun p : Coeff 2 => hillL2Discriminant p z) (SpectralWeight.one.toCoeff q)) V=0) :
    (fderiv ℂ d (SpectralWeight.one.toCoeff q))
      (V)=0 := by
  apply fderiv_apply_eq_zero_of_eventually_sq d (fun p => hillLocalGapSquare q hq hr k p/4) _ _ hd hne hsq
  have heq : (fun p : Coeff 2 => hillLocalGapSquare q hq hr k p/4)=
      (4 : ℂ)⁻¹ • hillLocalGapSquare q hq hr k := by
    funext p
    simp only [Pi.smul_apply,smul_eq_mul,div_eq_mul_inv,mul_comm]
  rw [heq,fderiv_const_smul_field]
  change (4 : ℂ)⁻¹*((fderiv ℂ (hillLocalGapSquare q hq hr k) (SpectralWeight.one.toCoeff q)) _)=0
  rw [fderiv_hillLocalGapSquare_of_trace_stationary q hq hr k hk V hV,mul_zero]


theorem fderiv_hillGapHalfLength_extension_of_trace_stationary
    (k : ℕ) (hk : 1≤k) (hgap : hillRealGapHalfLength q hq hr k≠0)
    (d : Coeff 2 → ℂ) (hd : DifferentiableAt ℂ d (SpectralWeight.one.toCoeff q))
    (hmatch : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
      d (SpectralWeight.one.toCoeff p.val)=(hillRealGapHalfLength p.val p.property.1 p.property.2 k : ℂ)) (V : Coeff 2)
    (hV : ∀ z : ℂ, (fderiv ℂ (fun p : Coeff 2 => hillL2Discriminant p z) (SpectralWeight.one.toCoeff q)) V=0) (hVp : V∈Coeff.paritySubspace 0) :
    (fderiv ℂ d (SpectralWeight.one.toCoeff q))
      (V)=0 := by
  obtain ⟨R,hR,hR0,hsq,hreal⟩ := exists_hillGapHalfLength_analytic_extension q hq hr k hk hgap
  have he : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
      d (SpectralWeight.one.toCoeff p.val)=R (SpectralWeight.one.toCoeff p.val) := by
    filter_upwards [hmatch,hreal] with p hp hpR
    exact hp.trans hpR.symm
  rw [fderiv_eq_on_parity_of_eventuallyEq_realPotentials q hq hr d R hd hR.differentiableAt he _
    hVp]
  exact fderiv_hillGapHalfLength_root_of_trace_stationary q hq hr k hk R hR.differentiableAt
    (hR0 ▸ ofReal_ne_zero.mpr hgap) (hsq.mono (fun _ hp => hp.2)) V hV

end NLS.KdV
