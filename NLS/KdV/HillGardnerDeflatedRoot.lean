import NLS.KdV.HillGardnerGapMoments
import NLS.KdV.HillLocalDeflatedComplexRoot
import NLS.KdV.HillRealSourceJetUniqueness
import NLS.ComplexAnalysis.ImplicitRootStationarity

/-! # Actual local gap deflation and its root are Gardner stationary -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV
variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
  (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
  (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

/-- The actual quadratic gap factor is stationary at every energy. -/
theorem fderiv_hillLocalGapPolynomial_gardnerDirection_eq_zero
    (k : ℕ) (hk : 1≤k) (E b : ℂ) :
    (fderiv ℂ (fun p : Coeff 2 => hillLocalGapPolynomial q hq hr k p E) (SpectralWeight.one.toCoeff q))
      (hillL2DiscriminantGardnerDirection (SpectralWeight.one.toCoeff q) b)=0 := by
  let p0 := SpectralWeight.one.toCoeff q
  let X := hillL2DiscriminantGardnerDirection p0 b
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
  rw [fderiv_hillLocalGapMidpoint_gardnerDirection_eq_zero q hq hr k hk b,
    fderiv_hillLocalGapSquare_gardnerDirection_eq_zero q hq hr k hk b] at hd
  change (fderiv ℂ (fun p : Coeff 2 => hillLocalGapPolynomial q hq hr k p E) p0) X=
    (fderiv ℂ H _) (0 : ℂ × ℂ) at hd
  rw [map_zero] at hd
  exact hd

/-- The genuine gap polynomial is jointly analytic at every base energy. -/
theorem analyticAt_hillLocalGapPolynomial_base (k : ℕ) (hk : 1≤k) (w : ℂ) :
    AnalyticAt ℂ (fun t : ℂ × Coeff 2 => hillLocalGapPolynomial q hq hr k t.2 t.1)
      (w,SpectralWeight.one.toCoeff q) := by
  obtain ⟨U,_,hpU,hM,hS,_⟩ := exists_hillLocalGapSymmetricData_analytic_neighborhood q hq hr k hk
  have hM0 : AnalyticAt ℂ (hillLocalGapMidpoint q hq hr k) (SpectralWeight.one.toCoeff q) := hM _ hpU
  have hS0 : AnalyticAt ℂ (hillLocalGapSquare q hq hr k) (SpectralWeight.one.toCoeff q) := hS _ hpU
  have hMcomp : AnalyticAt ℂ (fun t : ℂ × Coeff 2 => hillLocalGapMidpoint q hq hr k t.2)
      (w,SpectralWeight.one.toCoeff q) :=
    hM0.comp (x := (w,SpectralWeight.one.toCoeff q)) (f := fun t : ℂ × Coeff 2 => t.2) analyticAt_snd
  have hScomp : AnalyticAt ℂ (fun t : ℂ × Coeff 2 => hillLocalGapSquare q hq hr k t.2)
      (w,SpectralWeight.one.toCoeff q) :=
    hS0.comp (x := (w,SpectralWeight.one.toCoeff q)) (f := fun t : ℂ × Coeff 2 => t.2) analyticAt_snd
  exact ((analyticAt_fst.sub hMcomp).pow 2).sub (hScomp.div_const (c := 4))

/-- The actual intrinsic circle avoids both roots of the gap polynomial. -/
theorem hillLocalGapPolynomial_ne_zero_base_circle (k : ℕ) (hk : 1≤k) (w : ℂ)
    (hw : w∈sphere (hillRealGapCenter q hq hr k : ℂ)
      (hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k)) :
    hillLocalGapPolynomial q hq hr k (SpectralWeight.one.toCoeff q) w≠0 := by
  obtain ⟨V,_,hpV,hpair⟩ := exists_hillComplexGapPair_neighborhood q hq hr k hk
  obtain ⟨hb,a,ha,d,hd,_haz,_hdz,hm⟩ := hpair _ hpV
  rw [hillLocalGapPolynomial_eq_of_pair q hq hr k hk _ hb ha hd hm]
  exact mul_ne_zero (sub_ne_zero.mpr (sphere_disjoint_ball.ne_of_mem hw ha))
    (sub_ne_zero.mpr (sphere_disjoint_ball.ne_of_mem hw hd))

/-- The actual Cauchy density has zero source variation on its contour. -/
theorem fderiv_hillLocalGapQuotient_gardnerDirection_eq_zero
    (k : ℕ) (hk : 1≤k) (w b : ℂ)
    (hw : w∈sphere (hillRealGapCenter q hq hr k : ℂ)
      (hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k)) :
    (fderiv ℂ (fun p : Coeff 2 => hillL2Radicand p w/hillLocalGapPolynomial q hq hr k p w)
      (SpectralWeight.one.toCoeff q))
        (hillL2DiscriminantGardnerDirection (SpectralWeight.one.toCoeff q) b)=0 := by
  have hR := (analyticOnNhd_hillL2Radicand_joint (w,SpectralWeight.one.toCoeff q) (mem_univ _)).comp
    (f := fun p : Coeff 2 => (w,p)) (analyticAt_const.prod analyticAt_id)
  have hP := (analyticAt_hillLocalGapPolynomial_base q hq hr k hk w).comp
    (f := fun p : Coeff 2 => (w,p)) (analyticAt_const.prod analyticAt_id)
  rw [fderiv_div_apply (fun p : Coeff 2 => hillL2Radicand p w)
    (fun p : Coeff 2 => hillLocalGapPolynomial q hq hr k p w) _ hR.differentiableAt hP.differentiableAt
      (hillLocalGapPolynomial_ne_zero_base_circle q hq hr k hk w hw),
    fderiv_hillL2Radicand_gardnerDirection_eq_zero,
    fderiv_hillLocalGapPolynomial_gardnerDirection_eq_zero q hq hr k hk w b]
  simp

/-- The literal Cauchy-deflated gap unit is stationary throughout its filled disc. -/
theorem fderiv_hillLocalGapUnit_gardnerDirection_eq_zero
    (k : ℕ) (hk : 1≤k) (E b : ℂ)
    (hE : E∈ball (hillRealGapCenter q hq hr k : ℂ)
      (hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k)) :
    (fderiv ℂ (fun p : Coeff 2 => hillLocalGapUnit q hq hr k (E,p)) (SpectralWeight.one.toCoeff q))
      (hillL2DiscriminantGardnerDirection (SpectralWeight.one.toCoeff q) b)=0 := by
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
    (fun w hw => fderiv_hillLocalGapQuotient_gardnerDirection_eq_zero q hq hr k hk w b hw)

/-- The actual nonzero deflated root is stationary, including at the original gap endpoints. -/
theorem fderiv_hillLocalDeflatedComplexRoot_gardnerDirection_eq_zero
    (k : ℕ) (hk : 1≤k) (E b : ℂ)
    (hE : E∈ball (hillRealGapCenter q hq hr k : ℂ)
      (hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k)) :
    (fderiv ℂ (fun p : Coeff 2 => hillLocalDeflatedComplexRoot q hq hr k (E,p)) (SpectralWeight.one.toCoeff q))
      (hillL2DiscriminantGardnerDirection (SpectralWeight.one.toCoeff q) b)=0 := by
  have hdom := mem_hillLocalDeflatedRootDomain_base q hq hr k hk E hE
  have hA := (analyticOnNhd_hillLocalDeflatedComplexRoot q hq hr k hk _ hdom).comp
    (f := fun p : Coeff 2 => (E,p)) (analyticAt_const.prod analyticAt_id)
  apply fderiv_apply_eq_zero_of_eventually_sq
    (fun p : Coeff 2 => hillLocalDeflatedComplexRoot q hq hr k (E,p))
    (fun p : Coeff 2 => hillLocalGapUnit q hq hr k (E,p)) _ _ hA.differentiableAt
    (hillLocalDeflatedComplexRoot_ne_zero q hq hr k hk _ hdom) _
    (fderiv_hillLocalGapUnit_gardnerDirection_eq_zero q hq hr k hk E b hE)
  have hinc : Continuous (fun p : Coeff 2 => (E,p)) := continuous_const.prodMk continuous_id
  filter_upwards [((isOpen_hillLocalDeflatedRootDomain q hq hr k hk).preimage hinc).mem_nhds hdom] with p hp
  exact hillLocalDeflatedComplexRoot_sq q hq hr k hk (E,p) hp

/-- Any actual local half-gap root has zero Gardner derivative at an open gap. -/
theorem fderiv_hillGapHalfLength_root_gardnerDirection_eq_zero
    (k : ℕ) (hk : 1≤k) (d : Coeff 2 → ℂ) (hd : DifferentiableAt ℂ d (SpectralWeight.one.toCoeff q))
    (hne : d (SpectralWeight.one.toCoeff q)≠0)
    (hsq : ∀ᶠ p in 𝓝 (SpectralWeight.one.toCoeff q), d p^2=hillLocalGapSquare q hq hr k p/4) (b : ℂ) :
    (fderiv ℂ d (SpectralWeight.one.toCoeff q))
      (hillL2DiscriminantGardnerDirection (SpectralWeight.one.toCoeff q) b)=0 := by
  apply fderiv_apply_eq_zero_of_eventually_sq d (fun p => hillLocalGapSquare q hq hr k p/4) _ _ hd hne hsq
  have heq : (fun p : Coeff 2 => hillLocalGapSquare q hq hr k p/4)=
      (4 : ℂ)⁻¹ • hillLocalGapSquare q hq hr k := by
    funext p
    simp only [Pi.smul_apply,smul_eq_mul,div_eq_mul_inv,mul_comm]
  rw [heq,fderiv_const_smul_field]
  change (4 : ℂ)⁻¹*((fderiv ℂ (hillLocalGapSquare q hq hr k) (SpectralWeight.one.toCoeff q)) _)=0
  rw [fderiv_hillLocalGapSquare_gardnerDirection_eq_zero q hq hr k hk b,mul_zero]

/-- Physical real-neighborhood agreement also determines half-gap variation. -/
theorem fderiv_hillGapHalfLength_extension_gardnerDirection_eq_zero
    (k : ℕ) (hk : 1≤k) (hgap : hillRealGapHalfLength q hq hr k≠0)
    (d : Coeff 2 → ℂ) (hd : DifferentiableAt ℂ d (SpectralWeight.one.toCoeff q))
    (hmatch : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
      d (SpectralWeight.one.toCoeff p.val)=(hillRealGapHalfLength p.val p.property.1 p.property.2 k : ℂ)) (b : ℂ) :
    (fderiv ℂ d (SpectralWeight.one.toCoeff q))
      (hillL2DiscriminantGardnerDirection (SpectralWeight.one.toCoeff q) b)=0 := by
  obtain ⟨R,hR,hR0,hsq,hreal⟩ := exists_hillGapHalfLength_analytic_extension q hq hr k hk hgap
  have he : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
      d (SpectralWeight.one.toCoeff p.val)=R (SpectralWeight.one.toCoeff p.val) := by
    filter_upwards [hmatch,hreal] with p hp hpR
    exact hp.trans hpR.symm
  rw [fderiv_eq_on_parity_of_eventuallyEq_realPotentials q hq hr d R hd hR.differentiableAt he _
    (hillL2DiscriminantGardnerDirection_mem_parity _ b)]
  exact fderiv_hillGapHalfLength_root_gardnerDirection_eq_zero q hq hr k hk R hR.differentiableAt
    (hR0 ▸ ofReal_ne_zero.mpr hgap) (hsq.mono (fun _ hp => hp.2)) b

end NLS.KdV
