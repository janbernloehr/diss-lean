import NLS.ComplexAnalysis.JointSpectralDerivativeAnalytic
import NLS.KdV.HillLocalPhysicalPeriodMatching
import NLS.KdV.HillL2RealContourMoments
import NLS.ComplexAnalysis.TraceActionVariation

/-! # Actual analytic Hill actions on a fixed physical gap contour

The local complex action is the literal Arnold contour integral on the
base potential's intrinsic circle, with its actual analytic root chart.
It agrees with the real physical action near the base, even at a closed
gap, and its source derivative is the negative unweighted trace period.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV
variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

def hillLocalContourAction (n : ℕ) (p : Coeff 2) : ℂ :=
  (Real.pi : ℂ)⁻¹ * ∮ E in C((hillRealGapCenter q hq hr n : ℂ),
    hillRealGapHalfLength q hq hr n+hillRealGapCollar q hq hr n),
    E*deriv (hillL2Discriminant p) E/hillAbelianComplexRoot q hq hr (E,p)

theorem exists_hillLocalContourAction_analytic_neighborhood (n : ℕ) (hn : 1≤n) :
    ∃ U : Set (Coeff 2), IsOpen U ∧ SpectralWeight.one.toCoeff q∈U ∧
      AnalyticOnNhd ℂ (hillLocalContourAction q hq hr n) U := by
  obtain ⟨U,hU,hqU,hcircle⟩ := exists_hillAbelianComplexRoot_contour_neighborhood q hq hr n hn
  let D := hillAbelianComplexRootDomain q hq hr
  let F : ℂ × Coeff 2 → ℂ := fun t =>
    t.1*deriv (hillL2Discriminant t.2) t.1/hillAbelianComplexRoot q hq hr t
  have hF : AnalyticOnNhd ℂ F D := by
    have hDel : AnalyticOnNhd ℂ (fun t : ℂ × Coeff 2 => hillL2Discriminant t.2 t.1) D :=
      analyticOnNhd_hillL2Discriminant_joint.mono (subset_univ _)
    intro t ht
    exact (analyticAt_fst.mul ((analyticOnNhd_spectral_deriv_of_analyticOnNhd _ D
      (isOpen_hillAbelianComplexRootDomain q hq hr) hDel) t ht)).div
      (analyticOnNhd_hillAbelianComplexRoot q hq hr t ht) (hillAbelianComplexRoot_ne_zero q hq hr t ht)
  have hR := add_nonneg (hillRealGapContour_geometry q hq hr n hn).1
    (hillRealGapContour_geometry q hq hr n hn).2.1.le
  have hA := analyticOnNhd_circleIntegral_of_jointAnalytic F
    (isOpen_hillAbelianComplexRootDomain q hq hr) hF _ _ hR hU hcircle
  exact ⟨U,hU,hqU,analyticOnNhd_const.mul hA⟩

theorem analyticAt_hillLocalContourAction (n : ℕ) (hn : 1≤n) :
    AnalyticAt ℂ (hillLocalContourAction q hq hr n) (SpectralWeight.one.toCoeff q) := by
  obtain ⟨_,_,hqU,hA⟩ := exists_hillLocalContourAction_analytic_neighborhood q hq hr n hn
  exact hA _ hqU

/-- One germ agrees with the actual action at every nearby real source;
the selected gap is allowed to collapse. -/
theorem hillLocalContourAction_eventually_eq_physical (n : ℕ) (hn : 1≤n) :
    ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
      hillLocalContourAction q hq hr n (SpectralWeight.one.toCoeff p.val)=
        (hillRealGapIntegral p.val p.property.1 p.property.2 n 0:ℂ) := by
  obtain ⟨V,hV,hqV,hroot⟩ := exists_hillAbelianComplexRoot_physical_contour_neighborhood q hq hr n hn
  obtain ⟨W,hW,hqW,hgeom⟩ := exists_hillIntrinsicContour_local_physical_geometry q hq hr n hn
  filter_upwards [hV.mem_nhds hqV,hW.mem_nhds hqW] with p hpV hpW
  have hN : AnalyticOnNhd ℂ (fun E => E*deriv (hillL2Discriminant (SpectralWeight.one.toCoeff p.val)) E) univ :=
    analyticOnNhd_id.mul (analyticOnNhd_hillL2Discriminant _).deriv
  have he := hillPhysicalContour_period_eq_base_contour q hq hr p.val p.property.1 p.property.2 n hn
    (hgeom p hpW).1 (hgeom p hpW).2 _ hN
  have hArnold := (hillL2RealContourMoment_eq_gapIntegral p.val p.property.1 p.property.2 n hn 0).symm.trans
    (hillL2RealContourMoment_arnold_energyProduct p.val p.property.1 p.property.2 n hn 0)
  simp only [Nat.cast_zero,zero_add,one_mul,pow_one] at hArnold
  rw [hillLocalContourAction,hArnold]
  congr 1
  calc
    _ = ∮ E in C((hillRealGapCenter q hq hr n : ℂ),
        hillRealGapHalfLength q hq hr n+hillRealGapCollar q hq hr n),
        E*deriv (hillL2Discriminant (SpectralWeight.one.toCoeff p.val)) E/
          hillEnergyCanonicalRootProduct p.val p.property.1 p.property.2 E := by
      apply circleIntegral.integral_congr
        (add_nonneg (hillRealGapContour_geometry q hq hr n hn).1 (hillRealGapContour_geometry q hq hr n hn).2.1.le)
      intro E hE
      dsimp only []
      rw [(hroot p hpV E hE).2.2]
    _ = _ := he

/-- The actual analytic action derivative, with the source normalization
and the chosen physical root, in every complex L2 source direction. -/
theorem fderiv_hillLocalContourAction_apply (n : ℕ) (hn : 1≤n) (h : Coeff 2) :
    (fderiv ℂ (hillLocalContourAction q hq hr n) (SpectralWeight.one.toCoeff q)) h=
      -(Real.pi : ℂ)⁻¹ * ∮ E in C((hillRealGapCenter q hq hr n : ℂ),
        hillRealGapHalfLength q hq hr n+hillRealGapCollar q hq hr n),
        (fderiv ℂ (fun p : Coeff 2 => hillL2Discriminant p E) (SpectralWeight.one.toCoeff q)) h/
          hillEnergyCanonicalRootProduct q hq hr E := by
  let D := hillAbelianComplexRootDomain q hq hr
  let Del : ℂ × Coeff 2 → ℂ := fun t => hillL2Discriminant t.2 t.1
  have hDel : AnalyticOnNhd ℂ Del D := analyticOnNhd_hillL2Discriminant_joint.mono (subset_univ _)
  have hc : ∀ E∈sphere (hillRealGapCenter q hq hr n : ℂ)
      (hillRealGapHalfLength q hq hr n+hillRealGapCollar q hq hr n),
      (E,SpectralWeight.one.toCoeff q)∈D := fun E hE =>
    mem_hillAbelianComplexRootDomain_base q hq hr E (hillRealGapContour_sphere_subset q hq hr n hn hE)
  have hR := add_nonneg (hillRealGapContour_geometry q hq hr n hn).1
    (hillRealGapContour_geometry q hq hr n hn).2.1.le
  have hvar := fderiv_arnold_trace_period_apply Del (hillAbelianComplexRoot q hq hr) D
    (isOpen_hillAbelianComplexRootDomain q hq hr) hDel (analyticOnNhd_hillAbelianComplexRoot q hq hr)
    (hillAbelianComplexRoot_ne_zero q hq hr) (fun t ht => hillAbelianComplexRoot_sq q hq hr t ht)
    _ _ hR (SpectralWeight.one.toCoeff q) h hc
  change (fderiv ℂ ((Real.pi : ℂ)⁻¹ • fun p : Coeff 2 => ∮ E in C((hillRealGapCenter q hq hr n : ℂ),
    hillRealGapHalfLength q hq hr n+hillRealGapCollar q hq hr n),
    E*deriv (hillL2Discriminant p) E/hillAbelianComplexRoot q hq hr (E,p)) (SpectralWeight.one.toCoeff q)) h=_
  rw [fderiv_const_smul_field]
  change (Real.pi : ℂ)⁻¹*((fderiv ℂ (fun p : Coeff 2 => ∮ E in C((hillRealGapCenter q hq hr n : ℂ),
    hillRealGapHalfLength q hq hr n+hillRealGapCollar q hq hr n),
    E*deriv (hillL2Discriminant p) E/hillAbelianComplexRoot q hq hr (E,p)) (SpectralWeight.one.toCoeff q)) h)=_
  rw [hvar]
  rw [neg_mul,mul_neg]
  congr 2
  apply circleIntegral.integral_congr hR
  intro E hE
  dsimp only [Del]
  rw [hillAbelianComplexRoot_base q hq hr E (hillRealGapContour_sphere_subset q hq hr n hn hE)]

end NLS.KdV
