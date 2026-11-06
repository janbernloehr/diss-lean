import NLS.ComplexAnalysis.JointSpectralDerivativeAnalytic
import NLS.KdV.HillGardnerGapMoments
/-! # Actual spectral data along trace-stationary source tangents

A fixed complex tangent annihilating every actual Hill trace also
annihilates its spectral derivative, continued primitive and roots, and
actual symmetric gap data. No isospectral path is assumed.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.LinearVolterra NLS.ZakharovShabat NLS.ComplexAnalysis
namespace NLS.KdV
/-- Joint trace differentiation in the actual source tangent also vanishes. -/
theorem fderiv_hillL2Discriminant_joint_of_trace_stationary
    (q : Coeff 2) (a : ℂ) (V : Coeff 2)
    (hV : ∀ E : ℂ, (fderiv ℂ (fun p : Coeff 2 => hillL2Discriminant p E) q) V=0) :
    (fderiv ℂ (fun t : ℂ × Coeff 2 => hillL2Discriminant t.2 t.1) (a,q))
      (0,V)=0 := by
  have hd := ((analyticOnNhd_hillL2Discriminant_joint (a,q) (mem_univ _)).differentiableAt.hasFDerivAt.comp
    q (hasFDerivAt_prodMk_right a q)).fderiv
  have he := congrArg (fun L : Coeff 2 →L[ℂ] ℂ => L V) hd
  change (fderiv ℂ (fun p : Coeff 2 => hillL2Discriminant p a) q)
    V=
      (fderiv ℂ (fun t : ℂ × Coeff 2 => hillL2Discriminant t.2 t.1) (a,q))
        (0,V) at he
  exact he.symm.trans (hV a)

/-- The actual continued primitive has zero source variation along every trace direction. -/
theorem fderiv_hillL2ContinuedPrimitive_of_trace_stationary
    (q : Coeff 2) (a : ℂ) (V : Coeff 2)
    (hV : ∀ E : ℂ, (fderiv ℂ (fun p : Coeff 2 => hillL2Discriminant p E) q) V=0) (ha : (a,q)∈hillL2ContinuationDomain) :
    (fderiv ℂ (fun p : Coeff 2 => hillL2ContinuedPrimitive (a,p)) q)
      V=0 := by
  have hd := ((hasFDerivAt_hillL2ContinuedPrimitive (a,q) ha).comp
    q (hasFDerivAt_prodMk_right a q)).fderiv
  have he := congrArg (fun L : Coeff 2 →L[ℂ] ℂ => L V) hd
  change (fderiv ℂ (fun p : Coeff 2 => hillL2ContinuedPrimitive (a,p)) q)
    V=
      (hillL2ContinuedRoot (a,q))⁻¹*
        (fderiv ℂ (fun t : ℂ × Coeff 2 => hillL2Discriminant t.2 t.1) (a,q))
          (0,V) at he
  rw [fderiv_hillL2Discriminant_joint_of_trace_stationary q a V hV,mul_zero] at he
  exact he

/-- The joint primitive differential is stationary on exactly the same actual domain. -/
theorem fderiv_hillL2ContinuedPrimitive_joint_of_trace_stationary
    (q : Coeff 2) (a : ℂ) (V : Coeff 2)
    (hV : ∀ E : ℂ, (fderiv ℂ (fun p : Coeff 2 => hillL2Discriminant p E) q) V=0) (ha : (a,q)∈hillL2ContinuationDomain) :
    (fderiv ℂ hillL2ContinuedPrimitive (a,q)) (0,V)=0 := by
  rw [(hasFDerivAt_hillL2ContinuedPrimitive (a,q) ha).fderiv]
  change (hillL2ContinuedRoot (a,q))⁻¹*
    (fderiv ℂ (fun t : ℂ × Coeff 2 => hillL2Discriminant t.2 t.1) (a,q))
      (0,V)=0
  rw [fderiv_hillL2Discriminant_joint_of_trace_stationary q a V hV,mul_zero]

/-- The sign-normalized continued root is also stationary on its actual open domain. -/
theorem fderiv_hillL2ContinuedRoot_joint_of_trace_stationary
    (q : Coeff 2) (a : ℂ) (V : Coeff 2)
    (hV : ∀ E : ℂ, (fderiv ℂ (fun p : Coeff 2 => hillL2Discriminant p E) q) V=0) (ha : (a,q)∈hillL2ContinuationDomain) :
    (fderiv ℂ hillL2ContinuedRoot (a,q)) (0,V)=0 := by
  have heq : (fun t : ℂ × Coeff 2 => 2*sinh (hillL2ContinuedPrimitive t)) =ᶠ[𝓝 (a,q)]
      hillL2ContinuedRoot := by
    filter_upwards [isOpen_hillL2ContinuationDomain.mem_nhds ha] with t ht
    exact (hillL2ContinuedPrimitive_trace t ht).2
  have hd := (((analyticOnNhd_hillL2ContinuedPrimitive (a,q) ha).differentiableAt.hasFDerivAt.csinh).const_smul (2 : ℂ)).congr_of_eventuallyEq heq.symm
  have he := congrArg (fun L : (ℂ × Coeff 2) →L[ℂ] ℂ => L (0,V)) hd.fderiv
  change (fderiv ℂ hillL2ContinuedRoot (a,q)) (0,V)=
    2*(cosh (hillL2ContinuedPrimitive (a,q))*
      (fderiv ℂ hillL2ContinuedPrimitive (a,q)) (0,V)) at he
  rw [fderiv_hillL2ContinuedPrimitive_joint_of_trace_stationary q a V hV ha,mul_zero,mul_zero] at he
  exact he

theorem fderiv_hillL2ContinuedRoot_of_trace_stationary
    (q : Coeff 2) (a : ℂ) (V : Coeff 2)
    (hV : ∀ E : ℂ, (fderiv ℂ (fun p : Coeff 2 => hillL2Discriminant p E) q) V=0) (ha : (a,q)∈hillL2ContinuationDomain) :
    (fderiv ℂ (fun p : Coeff 2 => hillL2ContinuedRoot (a,p)) q)
      V=0 := by
  have hd := ((analyticOnNhd_hillL2ContinuedRoot (a,q) ha).differentiableAt.hasFDerivAt.comp
    q (hasFDerivAt_prodMk_right a q)).fderiv
  have he := congrArg (fun L : Coeff 2 →L[ℂ] ℂ => L V) hd
  change (fderiv ℂ (fun p : Coeff 2 => hillL2ContinuedRoot (a,p)) q)
    V=
      (fderiv ℂ hillL2ContinuedRoot (a,q)) (0,V) at he
  exact he.trans (fderiv_hillL2ContinuedRoot_joint_of_trace_stationary q a V hV ha)

/-- Source stationarity commutes with the actual spectral derivative of the trace. -/
theorem fderiv_deriv_hillL2Discriminant_of_trace_stationary
    (q : Coeff 2) (a : ℂ) (V : Coeff 2)
    (hV : ∀ E : ℂ, (fderiv ℂ (fun p : Coeff 2 => hillL2Discriminant p E) q) V=0) :
    (fderiv ℂ (fun p : Coeff 2 => deriv (hillL2Discriminant p) a) q)
      V=0 := by
  let F (t : ℂ × Coeff 2) := hillL2Discriminant t.2 t.1
  let X := V
  let e : ℂ × Coeff 2 := (1,0)
  let v : ℂ × Coeff 2 := (0,X)
  let ev : ((ℂ × Coeff 2) →L[ℂ] ℂ) →L[ℂ] ℂ := ContinuousLinearMap.apply ℂ ℂ v
  let ee : ((ℂ × Coeff 2) →L[ℂ] ℂ) →L[ℂ] ℂ := ContinuousLinearMap.apply ℂ ℂ e
  have ha := analyticOnNhd_hillL2Discriminant_joint (a,q) (mem_univ _)
  have hdF : DifferentiableAt ℂ (fderiv ℂ F) (a,q) :=
    (analyticOnNhd_hillL2Discriminant_joint.fderiv (a,q) (mem_univ _)).differentiableAt
  have hv := (ev.hasFDerivAt.comp (a,q) hdF.hasFDerivAt).comp_hasDerivAt a
    ((hasDerivAt_id a).prodMk (hasDerivAt_const a q))
  have hdf : (fderiv ℂ (fderiv ℂ F) (a,q)) e v=0 := by
    have heq : (fun z : ℂ => (fderiv ℂ F (z,q)) v)=(fun _ : ℂ => (0 : ℂ)) := by
      funext z
      exact fderiv_hillL2Discriminant_joint_of_trace_stationary q z V hV
    have he := hv.deriv
    change deriv (fun z : ℂ => (fderiv ℂ F (z,q)) v) a=
      (fderiv ℂ (fderiv ℂ F) (a,q)) e v at he
    rw [heq,deriv_const] at he
    exact he.symm
  have he := congrArg (fun L : Coeff 2 →L[ℂ] ℂ => L X)
    (((ee.hasFDerivAt.comp (a,q) hdF.hasFDerivAt).comp q (hasFDerivAt_prodMk_right a q)).fderiv)
  change (fderiv ℂ (fun p : Coeff 2 => (fderiv ℂ F (a,p)) e) q) X=
    (fderiv ℂ (fderiv ℂ F) (a,q)) v e at he
  have hspec : (fun p : Coeff 2 => deriv (hillL2Discriminant p) a)=
      (fun p : Coeff 2 => (fderiv ℂ F (a,p)) e) := by
    funext p
    exact deriv_spectral_section_eq_fderiv F a p
      (analyticOnNhd_hillL2Discriminant_joint (a,p) (mem_univ _)).differentiableAt
  rw [hspec]
  exact he.trans (((ha.contDiffAt.isSymmSndFDerivAt_of_omega).eq v e).trans hdf)

theorem fderiv_hillL2Radicand_of_trace_stationary
    (q : Coeff 2) (E : ℂ) (V : Coeff 2)
    (hV : ∀ z : ℂ, (fderiv ℂ (fun p : Coeff 2 => hillL2Discriminant p z) q) V=0) :
    (fderiv ℂ (fun p : Coeff 2 => hillL2Radicand p E) q)
      V=0 := by
  have hA : AnalyticAt ℂ (fun p : Coeff 2 => hillL2Discriminant p E) q :=
    (analyticOnNhd_hillL2Discriminant_joint (E,q) (mem_univ _)).comp
      (f := fun p : Coeff 2 => (E,p)) (analyticAt_const.prod analyticAt_id)
  have hD := hA.differentiableAt.hasFDerivAt
  have hd := congrArg (fun L : Coeff 2 →L[ℂ] ℂ => L V)
    ((hD.mul hD).sub_const 4).fderiv
  have heq : (fun p : Coeff 2 => hillL2Discriminant p E*hillL2Discriminant p E-4)=
      (fun p => hillL2Radicand p E) := by
    funext p
    simp only [hillL2Radicand,pow_two]
  change (fderiv ℂ (fun p : Coeff 2 => hillL2Discriminant p E*hillL2Discriminant p E-4) q) _ = _ at hd
  rw [heq] at hd
  simp only [add_apply,smul_apply,smul_eq_mul] at hd
  change (fderiv ℂ (fun p : Coeff 2 => hillL2Radicand p E) q)
    V=
      hillL2Discriminant q E*((fderiv ℂ (fun p : Coeff 2 => hillL2Discriminant p E) q)
        V)+
      hillL2Discriminant q E*((fderiv ℂ (fun p : Coeff 2 => hillL2Discriminant p E) q)
        V) at hd
  rw [hV E,mul_zero,add_zero] at hd
  exact hd

/-- Every actual differentiable local nonzero radicand root is stationary
along the constructed Hill trace direction; no root derivative is assumed. -/
theorem fderiv_hillL2RadicandRoot_of_trace_stationary
    (q : Coeff 2) (E : ℂ) (V : Coeff 2)
    (hV : ∀ z : ℂ, (fderiv ℂ (fun p : Coeff 2 => hillL2Discriminant p z) q) V=0) (R : Coeff 2 → ℂ)
    (hR : DifferentiableAt ℂ R q) (hne : R q≠0)
    (hsq : ∀ᶠ p in 𝓝 q, R p^2=hillL2Radicand p E) :
    (fderiv ℂ R q) V=0 := by
  have heq : (fun p : Coeff 2 => R p*R p) =ᶠ[𝓝 q] (fun p => hillL2Radicand p E) := by
    filter_upwards [hsq] with p hp
    simpa only [pow_two] using hp
  have hd := congrArg (fun L : Coeff 2 →L[ℂ] ℂ => L V) heq.fderiv_eq
  have hdR := (hR.hasFDerivAt.mul hR.hasFDerivAt).fderiv
  change fderiv ℂ (fun p : Coeff 2 => R p*R p) q = _ at hdR
  rw [hdR] at hd
  simp only [add_apply,smul_apply,smul_eq_mul] at hd
  change R q*((fderiv ℂ R q) V)+
      R q*((fderiv ℂ R q) V)=
      (fderiv ℂ (fun p : Coeff 2 => hillL2Radicand p E) q)
        V at hd
  rw [fderiv_hillL2Radicand_of_trace_stationary q E V hV] at hd
  have hzero : R q*((fderiv ℂ R q) V)=0 := by
    linear_combination hd/2
  exact (mul_eq_zero.mp hzero).resolve_left hne


/-- Spectral differentiation of the actual radicand remains source stationary. -/
theorem fderiv_deriv_hillL2Radicand_of_trace_stationary
    (q : Coeff 2) (E : ℂ) (V : Coeff 2)
    (hV : ∀ z : ℂ, (fderiv ℂ (fun p : Coeff 2 => hillL2Discriminant p z) q) V=0) :
    (fderiv ℂ (fun p : Coeff 2 => deriv (hillL2Radicand p) E) q)
      (V)=0 := by
  have hD : AnalyticAt ℂ (fun p : Coeff 2 => hillL2Discriminant p E) q :=
    (analyticOnNhd_hillL2Discriminant_joint (E,q) (mem_univ _)).comp
      (f := fun p : Coeff 2 => (E,p)) (analyticAt_const.prod analyticAt_id)
  have hDD : AnalyticAt ℂ (fun p : Coeff 2 => deriv (hillL2Discriminant p) E) q :=
    (analyticOnNhd_spectral_deriv_of_analyticOnNhd
      (fun t : ℂ × Coeff 2 => hillL2Discriminant t.2 t.1) univ isOpen_univ
      analyticOnNhd_hillL2Discriminant_joint (E,q) (mem_univ _)).comp
        (f := fun p : Coeff 2 => (E,p)) (analyticAt_const.prod analyticAt_id)
  have hformula : (fun p : Coeff 2 => deriv (hillL2Radicand p) E)=
      (fun p : Coeff 2 => 2*(hillL2Discriminant p E*deriv (hillL2Discriminant p) E)) := by
    funext p
    have hd := (((analyticOnNhd_hillL2Discriminant p E (mem_univ _)).differentiableAt.hasDerivAt.pow 2).sub_const 4).deriv
    change deriv (hillL2Radicand p) E=_ at hd
    rw [hd]
    ring
  rw [hformula]
  have hd := congrArg (fun L : Coeff 2 →L[ℂ] ℂ => L (V))
    ((hD.differentiableAt.hasFDerivAt.mul hDD.differentiableAt.hasFDerivAt).const_smul (2 : ℂ)).fderiv
  change (fderiv ℂ (fun p : Coeff 2 => 2*(hillL2Discriminant p E*deriv (hillL2Discriminant p) E)) q)
      (V)=
    2*(hillL2Discriminant q E*((fderiv ℂ (fun p : Coeff 2 => deriv (hillL2Discriminant p) E) q)
      (V))+deriv (hillL2Discriminant q) E*
      ((fderiv ℂ (fun p : Coeff 2 => hillL2Discriminant p E) q) (V))) at hd
  rw [fderiv_deriv_hillL2Discriminant_of_trace_stationary q E V hV,
    hV E,mul_zero,mul_zero,add_zero,mul_zero] at hd
  exact hd

variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
  (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
  (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

/-- Every actual logarithmic gap moment is stationary, without an open-gap hypothesis. -/
theorem fderiv_hillLogarithmicCircleMoment_of_trace_stationary
    (k j : ℕ) (hk : 1≤k) (V : Coeff 2)
    (hV : ∀ E : ℂ, (fderiv ℂ (fun p : Coeff 2 => hillL2Discriminant p E) (SpectralWeight.one.toCoeff q)) V=0) :
    (fderiv ℂ (logarithmicCircleMoment (fun t : ℂ × Coeff 2 => hillL2Radicand t.2 t.1)
      (hillRealGapCenter q hq hr k : ℂ) (hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k) j)
      (SpectralWeight.one.toCoeff q))
        (V)=0 := by
  let p0 := SpectralWeight.one.toCoeff q
  let X := V
  let c : ℂ := hillRealGapCenter q hq hr k
  let r := hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k
  let D : Set (ℂ × Coeff 2) := {t | hillL2Radicand t.2 t.1≠0}
  let F (t : ℂ × Coeff 2) := t.1^j*logDeriv (hillL2Radicand t.2) t.1
  have hD : IsOpen D := isOpen_ne_fun analyticOnNhd_hillL2Radicand_joint.continuous continuous_const
  have hA := analyticOnNhd_spectral_deriv_of_analyticOnNhd
    (fun t : ℂ × Coeff 2 => hillL2Radicand t.2 t.1) univ isOpen_univ analyticOnNhd_hillL2Radicand_joint
  have hF : AnalyticOnNhd ℂ F D := by
    intro t ht
    exact (analyticAt_fst.pow j).mul ((hA t (mem_univ _)).div
      (analyticOnNhd_hillL2Radicand_joint t (mem_univ _)) ht)
  have hc (E : ℂ) (hE : E∈sphere c r) : (E,p0)∈D :=
    hillL2Radicand_ne_zero_on_realCutDomain q hq hr E (hillRealGapContour_sphere_subset q hq hr k hk hE)
  have hzero : (fderiv ℂ (fun p : Coeff 2 => ∮ E in C(c,r),F (E,p)) p0) X=0 := by
    apply fderiv_circleIntegral_apply_eq_zero_of_jointAnalytic F D hD hF c r
      (add_nonneg (hillRealGapContour_geometry q hq hr k hk).1 (hillRealGapContour_geometry q hq hr k hk).2.1.le) p0 X hc
    intro E hE
    have hN := (hA (E,p0) (mem_univ _)).comp
      (f := fun p : Coeff 2 => (E,p)) (analyticAt_const.prod analyticAt_id)
    have hR := (analyticOnNhd_hillL2Radicand_joint (E,p0) (mem_univ _)).comp
      (f := fun p : Coeff 2 => (E,p)) (analyticAt_const.prod analyticAt_id)
    have hz : (fderiv ℂ (fun p : Coeff 2 => logDeriv (hillL2Radicand p) E) p0) X=0 := by
      change (fderiv ℂ (fun p : Coeff 2 => deriv (hillL2Radicand p) E/hillL2Radicand p E) p0) X=0
      rw [fderiv_div_apply (fun p : Coeff 2 => deriv (hillL2Radicand p) E)
        (fun p : Coeff 2 => hillL2Radicand p E) p0 hN.differentiableAt hR.differentiableAt (hc E hE) X,
        fderiv_deriv_hillL2Radicand_of_trace_stationary p0 E V hV,
        fderiv_hillL2Radicand_of_trace_stationary p0 E V hV]
      simp
    change (fderiv ℂ (E^j • fun p : Coeff 2 => logDeriv (hillL2Radicand p) E) p0) X=0
    rw [fderiv_const_smul_field]
    change E^j*((fderiv ℂ (fun p : Coeff 2 => logDeriv (hillL2Radicand p) E) p0) X)=0
    rw [hz,mul_zero]
  change (fderiv ℂ ((2*Real.pi*I : ℂ)⁻¹ • fun p : Coeff 2 => ∮ E in C(c,r),F (E,p)) p0) X=0
  rw [fderiv_const_smul_field]
  change (2*Real.pi*I : ℂ)⁻¹*((fderiv ℂ (fun p : Coeff 2 => ∮ E in C(c,r),F (E,p)) p0) X)=0
  rw [hzero,mul_zero]

/-- The actual gap midpoint is stationary, including at a collapsed gap. -/
theorem fderiv_hillLocalGapMidpoint_of_trace_stationary
    (k : ℕ) (hk : 1≤k) (V : Coeff 2)
    (hV : ∀ E : ℂ, (fderiv ℂ (fun p : Coeff 2 => hillL2Discriminant p E) (SpectralWeight.one.toCoeff q)) V=0) :
    (fderiv ℂ (hillLocalGapMidpoint q hq hr k) (SpectralWeight.one.toCoeff q))
      (V)=0 := by
  have heq : hillLocalGapMidpoint q hq hr k=(2 : ℂ)⁻¹ • logarithmicCircleMoment
      (fun t : ℂ × Coeff 2 => hillL2Radicand t.2 t.1)
      (hillRealGapCenter q hq hr k : ℂ) (hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k) 1 := by
    funext p
    simp only [hillLocalGapMidpoint,Pi.smul_apply,smul_eq_mul,div_eq_mul_inv,mul_comm]
  rw [heq,fderiv_const_smul_field]
  change (2 : ℂ)⁻¹*((fderiv ℂ (logarithmicCircleMoment
    (fun t : ℂ × Coeff 2 => hillL2Radicand t.2 t.1) _ _ 1) _) _)=0
  rw [fderiv_hillLogarithmicCircleMoment_of_trace_stationary q hq hr k 1 hk V hV,mul_zero]

/-- The full squared gap length is stationary even when its two roots coincide. -/
theorem fderiv_hillLocalGapSquare_of_trace_stationary
    (k : ℕ) (hk : 1≤k) (V : Coeff 2)
    (hV : ∀ E : ℂ, (fderiv ℂ (fun p : Coeff 2 => hillL2Discriminant p E) (SpectralWeight.one.toCoeff q)) V=0) :
    (fderiv ℂ (hillLocalGapSquare q hq hr k) (SpectralWeight.one.toCoeff q))
      (V)=0 := by
  obtain ⟨U,hU,hqU,hpair⟩ := exists_hillComplexGapPair_neighborhood q hq hr k hk
  have hR : 0≤hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k :=
    add_nonneg (hillRealGapContour_geometry q hq hr k hk).1 (hillRealGapContour_geometry q hq hr k hk).2.1.le
  let M (j : ℕ) := logarithmicCircleMoment (fun t : ℂ × Coeff 2 => hillL2Radicand t.2 t.1)
    (hillRealGapCenter q hq hr k : ℂ) (hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k) j
  have hM (j : ℕ) : AnalyticAt ℂ (M j) (SpectralWeight.one.toCoeff q) :=
    analyticOnNhd_logarithmicCircleMoment _ analyticOnNhd_hillL2Radicand_joint _ _ hR j hU
      (fun p hp => (hpair p hp).1) _ hqU
  have hd := congrArg (fun L : Coeff 2 →L[ℂ] ℂ =>
    L (V))
    (((hM 2).differentiableAt.hasFDerivAt.const_smul (2 : ℂ)).sub
      ((hM 1).differentiableAt.hasFDerivAt.pow 2)).fderiv
  simp only [sub_apply,smul_apply,smul_eq_mul,nsmul_eq_mul] at hd
  change (fderiv ℂ (hillLocalGapSquare q hq hr k) (SpectralWeight.one.toCoeff q)) _=
    2*((fderiv ℂ (M 2) (SpectralWeight.one.toCoeff q)) _)-
      (2*(M 1 (SpectralWeight.one.toCoeff q))^(2-1))*((fderiv ℂ (M 1) (SpectralWeight.one.toCoeff q)) _) at hd
  have hz (j : ℕ) : (fderiv ℂ (M j) (SpectralWeight.one.toCoeff q))
      (V)=0 :=
    fderiv_hillLogarithmicCircleMoment_of_trace_stationary q hq hr k j hk V hV
  rw [hz 2,hz 1,mul_zero,mul_zero,sub_zero] at hd
  exact hd

end NLS.KdV
