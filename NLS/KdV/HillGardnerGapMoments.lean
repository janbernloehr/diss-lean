import NLS.KdV.HillGardnerLocalRootVariation
import NLS.KdV.HillAllGapSymmetricData
import NLS.KdV.HillOpenGapHalfLength
import NLS.ComplexAnalysis.IntegralSourceStationarity
import NLS.ComplexAnalysis.StationarySquareRoot

/-! # Actual symmetric gap data are Gardner stationary

Logarithmic moments of the actual radicand determine the midpoint and
squared gap length even at a closed gap. Their literal contour derivatives
vanish along the actual Fourier Gardner directions.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV

/-- Spectral differentiation of the actual radicand remains source stationary. -/
theorem fderiv_deriv_hillL2Radicand_gardnerDirection_eq_zero
    (q : Coeff 2) (E b : ℂ) :
    (fderiv ℂ (fun p : Coeff 2 => deriv (hillL2Radicand p) E) q)
      (hillL2DiscriminantGardnerDirection q b)=0 := by
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
  have hd := congrArg (fun L : Coeff 2 →L[ℂ] ℂ => L (hillL2DiscriminantGardnerDirection q b))
    ((hD.differentiableAt.hasFDerivAt.mul hDD.differentiableAt.hasFDerivAt).const_smul (2 : ℂ)).fderiv
  change (fderiv ℂ (fun p : Coeff 2 => 2*(hillL2Discriminant p E*deriv (hillL2Discriminant p) E)) q)
      (hillL2DiscriminantGardnerDirection q b)=
    2*(hillL2Discriminant q E*((fderiv ℂ (fun p : Coeff 2 => deriv (hillL2Discriminant p) E) q)
      (hillL2DiscriminantGardnerDirection q b))+deriv (hillL2Discriminant q) E*
      ((fderiv ℂ (fun p : Coeff 2 => hillL2Discriminant p E) q) (hillL2DiscriminantGardnerDirection q b))) at hd
  rw [fderiv_deriv_hillL2Discriminant_gardnerDirection_eq_zero,
    fderiv_hillL2Discriminant_gardnerDirection_eq_zero,mul_zero,mul_zero,add_zero,mul_zero] at hd
  exact hd

variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
  (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
  (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

/-- Every actual logarithmic gap moment is stationary, without an open-gap hypothesis. -/
theorem fderiv_hillLogarithmicCircleMoment_gardnerDirection_eq_zero
    (k j : ℕ) (hk : 1≤k) (b : ℂ) :
    (fderiv ℂ (logarithmicCircleMoment (fun t : ℂ × Coeff 2 => hillL2Radicand t.2 t.1)
      (hillRealGapCenter q hq hr k : ℂ) (hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k) j)
      (SpectralWeight.one.toCoeff q))
        (hillL2DiscriminantGardnerDirection (SpectralWeight.one.toCoeff q) b)=0 := by
  let p0 := SpectralWeight.one.toCoeff q
  let X := hillL2DiscriminantGardnerDirection p0 b
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
        fderiv_deriv_hillL2Radicand_gardnerDirection_eq_zero,
        fderiv_hillL2Radicand_gardnerDirection_eq_zero]
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
theorem fderiv_hillLocalGapMidpoint_gardnerDirection_eq_zero
    (k : ℕ) (hk : 1≤k) (b : ℂ) :
    (fderiv ℂ (hillLocalGapMidpoint q hq hr k) (SpectralWeight.one.toCoeff q))
      (hillL2DiscriminantGardnerDirection (SpectralWeight.one.toCoeff q) b)=0 := by
  have heq : hillLocalGapMidpoint q hq hr k=(2 : ℂ)⁻¹ • logarithmicCircleMoment
      (fun t : ℂ × Coeff 2 => hillL2Radicand t.2 t.1)
      (hillRealGapCenter q hq hr k : ℂ) (hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k) 1 := by
    funext p
    simp only [hillLocalGapMidpoint,Pi.smul_apply,smul_eq_mul,div_eq_mul_inv,mul_comm]
  rw [heq,fderiv_const_smul_field]
  change (2 : ℂ)⁻¹*((fderiv ℂ (logarithmicCircleMoment
    (fun t : ℂ × Coeff 2 => hillL2Radicand t.2 t.1) _ _ 1) _) _)=0
  rw [fderiv_hillLogarithmicCircleMoment_gardnerDirection_eq_zero q hq hr k 1 hk b,mul_zero]

/-- The full squared gap length is stationary even when its two roots coincide. -/
theorem fderiv_hillLocalGapSquare_gardnerDirection_eq_zero
    (k : ℕ) (hk : 1≤k) (b : ℂ) :
    (fderiv ℂ (hillLocalGapSquare q hq hr k) (SpectralWeight.one.toCoeff q))
      (hillL2DiscriminantGardnerDirection (SpectralWeight.one.toCoeff q) b)=0 := by
  obtain ⟨U,hU,hqU,hpair⟩ := exists_hillComplexGapPair_neighborhood q hq hr k hk
  have hR : 0≤hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k :=
    add_nonneg (hillRealGapContour_geometry q hq hr k hk).1 (hillRealGapContour_geometry q hq hr k hk).2.1.le
  let M (j : ℕ) := logarithmicCircleMoment (fun t : ℂ × Coeff 2 => hillL2Radicand t.2 t.1)
    (hillRealGapCenter q hq hr k : ℂ) (hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k) j
  have hM (j : ℕ) : AnalyticAt ℂ (M j) (SpectralWeight.one.toCoeff q) :=
    analyticOnNhd_logarithmicCircleMoment _ analyticOnNhd_hillL2Radicand_joint _ _ hR j hU
      (fun p hp => (hpair p hp).1) _ hqU
  have hd := congrArg (fun L : Coeff 2 →L[ℂ] ℂ =>
    L (hillL2DiscriminantGardnerDirection (SpectralWeight.one.toCoeff q) b))
    (((hM 2).differentiableAt.hasFDerivAt.const_smul (2 : ℂ)).sub
      ((hM 1).differentiableAt.hasFDerivAt.pow 2)).fderiv
  simp only [sub_apply,smul_apply,smul_eq_mul,nsmul_eq_mul] at hd
  change (fderiv ℂ (hillLocalGapSquare q hq hr k) (SpectralWeight.one.toCoeff q)) _=
    2*((fderiv ℂ (M 2) (SpectralWeight.one.toCoeff q)) _)-
      (2*(M 1 (SpectralWeight.one.toCoeff q))^(2-1))*((fderiv ℂ (M 1) (SpectralWeight.one.toCoeff q)) _) at hd
  have hz (j : ℕ) : (fderiv ℂ (M j) (SpectralWeight.one.toCoeff q))
      (hillL2DiscriminantGardnerDirection (SpectralWeight.one.toCoeff q) b)=0 :=
    fderiv_hillLogarithmicCircleMoment_gardnerDirection_eq_zero q hq hr k j hk b
  rw [hz 2,hz 1,mul_zero,mul_zero,sub_zero] at hd
  exact hd

end NLS.KdV
