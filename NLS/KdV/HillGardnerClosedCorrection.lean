import NLS.KdV.HillGlobalRegularAnalytic
import NLS.KdV.HillDirichletTerminalVariation
import NLS.KdV.HillGardnerAbelianIntegralVariation

/-! # Actual regular Abelian correction variations at closed gaps -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.KdV
variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

theorem hillDiscriminant_mul_deriv_eq_zero_of_halfLength_zero (k : ℕ) (hk : 1≤k)
    (hc : hillRealGapHalfLength q hq hr k=0) :
    let E : ℂ := hillDirichletEnergy q hq hr k hk
    let p := SpectralWeight.one.toCoeff q
    hillL2Discriminant p E*deriv (hillL2Discriminant p) E=0 := by
  have hmem := hillDirichletEnergy_mem_gap q hq hr k hk
  have hab : hillRealLabels q hq hr (2*k-1)=hillRealLabels q hq hr (2*k) := by
    dsimp only [hillRealGapHalfLength] at hc
    linarith
  have hcenter : hillDirichletEnergy q hq hr k hk=hillRealGapCenter q hq hr k := by
    dsimp only [hillRealGapCenter]
    linarith [hmem.1,hmem.2]
  have hball := hillRealGapSegment_subset_intrinsic_contour_ball q hq hr k hk
    (ofReal_mem_ordered_segment _ _ _ (monotone_hillRealLabels q hq hr (by omega : 2*k-1≤2*k)) hmem)
  have h := hillDeflatedEnergyCanonicalRoot_energy_factor q hq hr k hk (hillDirichletEnergy q hq hr k hk)
    (hillRealGapContour_closedBall_subset_filledDomain q hq hr k hk (ball_subset_closedBall hball))
  dsimp only at h
  simpa [hcenter,hc] using h

theorem fderiv_hillDirichletSheetRoot_moving_gardner_eq_zero_of_closed (k : ℕ) (hk : 1≤k)
    (hc : hillRealGapHalfLength q hq hr k=0) (μ : Coeff 2 → ℂ)
    (hμ : AnalyticAt ℂ μ (SpectralWeight.one.toCoeff q))
    (hμ0 : μ (SpectralWeight.one.toCoeff q)=(hillDirichletEnergy q hq hr k hk : ℂ))
    (hμzero : ∀ᶠ p in 𝓝 (SpectralWeight.one.toCoeff q), hillL2DirichletCharacteristic p (μ p)=0) (b : ℂ) :
    (fderiv ℂ (fun p : Coeff 2 => hillDirichletSheetRoot p (μ p)) (SpectralWeight.one.toCoeff q))
      (hillL2DiscriminantGardnerDirection (SpectralWeight.one.toCoeff q) b)=0 := by
  rw [hillDirichletSheetRoot_moving_gardner_eq_kernel (⟨q,hq,hr⟩ : RealPeriodOneHillPotential) k hk μ hμ hμ0 hμzero b]
  dsimp only
  rw [hμ0,hillDiscriminant_mul_deriv_eq_zero_of_halfLength_zero q hq hr k hk hc,zero_mul]

variable (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))
include h0q h0r

private theorem exists_closed_stationary_model
    (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k)
    (hc : hillRealLabels q hq hr (2*k-1) = hillRealLabels q hq hr (2*k)) :
    ∃ β : Coeff 2 → ℂ, AnalyticAt ℂ β (SpectralWeight.one.toCoeff q) ∧ β (SpectralWeight.one.toCoeff q) = 0 ∧
      (∀ b : ℂ, (fderiv ℂ β (SpectralWeight.one.toCoeff q))
        (hillL2DiscriminantGardnerDirection (SpectralWeight.one.toCoeff q) b)=0) ∧
      ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
        (β (SpectralWeight.one.toCoeff p.val)).im = 0 ∧
        (hillRealGapHalfLength p.val p.property.1 p.property.2 k = 0 → β (SpectralWeight.one.toCoeff p.val) = 0) ∧
        (hillRealGapHalfLength p.val p.property.1 p.property.2 k ≠ 0 → ∀ θ : ℝ,
          cosineGapPoint (hillRealGapCenter p.val p.property.1 p.property.2 k)
            (hillRealGapHalfLength p.val p.property.1 p.property.2 k) (θ : ℂ) =
              (hillDirichletEnergy p.val p.property.1 p.property.2 k hk : ℂ) →
          Complex.sin (θ : ℂ) = hillDirichletGapSine p.val p.property.1 p.property.2 k hk →
          β (SpectralWeight.one.toCoeff p.val) = hillAbelianCosinePrimitive p.val p.property.1 p.property.2 n hn k (θ : ℂ)-
            (if k=n then 1 else 0)*((θ : ℂ)-(Real.pi : ℂ))) := by
  let p0 : RealPeriodOneHillPotential := ⟨q,hq,hr⟩
  let P : RealPeriodOneHillPotential → Coeff 2 := fun p => SpectralWeight.one.toCoeff p.val
  have hP : Continuous P := SpectralWeight.one.toCoeff.continuous.comp continuous_subtype_val
  obtain ⟨ρ,hρ,U,hU,hqU,Q,hQ,hphysical⟩ := exists_hillRegularAbelian_closed_gap_quadratic_chart q hq hr h0q h0r n k hn hk hc
  obtain ⟨μ,hμ,hμ0,hμzero,hμmatch⟩ := exists_hillDirichletEnergy_analytic_extension p0 k hk
  obtain ⟨A,_,hqA,hM,_,_⟩ := exists_hillLocalGapSymmetricData_analytic_neighborhood q hq hr k hk
  let τ := hillLocalGapMidpoint q hq hr k
  have hτ : AnalyticAt ℂ τ (SpectralWeight.one.toCoeff q) := hM _ hqA
  have hτ0 := (hillLocalGapSymmetricData_eq_physical_of_geometry q hq hr q hq hr k hk
    (hillRealGapContour_band_bounds q hq hr k hk) (hillRealGapSegment_subset_intrinsic_contour_ball q hq hr k hk)).1
  have hhalf0 : hillRealGapHalfLength q hq hr k = 0 := by simp [hillRealGapHalfLength,hc]
  have hμmem := hillDirichletEnergy_mem_gap q hq hr k hk
  have hμleft : hillDirichletEnergy q hq hr k hk = hillRealLabels q hq hr (2*k-1) := by linarith [hμmem.1,hμmem.2]
  have hcenter : hillRealGapCenter q hq hr k = hillRealLabels q hq hr (2*k-1) := by
    dsimp only [hillRealGapCenter]
    rw [← hc]
    ring
  have hu0 : μ (SpectralWeight.one.toCoeff q)-τ (SpectralWeight.one.toCoeff q) = 0 := by
    dsimp only [τ]
    rw [hμ0,hτ0,hμleft,hcenter,sub_self]
  have hμgap : (hillDirichletEnergy q hq hr k hk : ℂ) ∈
      segment ℝ (hillRealLabels q hq hr (2*k-1) : ℂ) (hillRealLabels q hq hr (2*k) : ℂ) :=
    ofReal_mem_ordered_segment _ _ _ (monotone_hillRealLabels q hq hr (by omega : 2*k-1 ≤ 2*k)) hμmem
  have hμball := hillRealGapSegment_subset_intrinsic_contour_ball q hq hr k hk hμgap
  have hdom0 : (μ (SpectralWeight.one.toCoeff q),SpectralWeight.one.toCoeff q) ∈ hillLocalDeflatedRootDomain q hq hr k := by
    rw [hμ0]
    exact mem_hillLocalDeflatedRootDomain_base q hq hr k hk _ hμball
  let B : Coeff 2 → ℂ := fun p => hillLocalDeflatedComplexRoot q hq hr k (μ p,p)
  have hB : AnalyticAt ℂ B (SpectralWeight.one.toCoeff q) :=
    (analyticOnNhd_hillLocalDeflatedComplexRoot q hq hr k hk _ hdom0).comp
      (f := fun p : Coeff 2 => (μ p,p)) (hμ.prod analyticAt_id)
  have hBn : B (SpectralWeight.one.toCoeff q) ≠ 0 := hillLocalDeflatedComplexRoot_ne_zero q hq hr k hk _ hdom0
  have hsheet : AnalyticAt ℂ (fun p : Coeff 2 => hillDirichletSheetRoot p (μ p)) (SpectralWeight.one.toCoeff q) :=
    (analyticOnNhd_hillDirichletSheetRoot_joint _ (mem_univ _)).comp
      (f := fun p : Coeff 2 => (μ p,p)) (hμ.prod analyticAt_id)
  have hQt : AnalyticAt ℂ (fun p : Coeff 2 => Q (μ p-τ p,p)) (SpectralWeight.one.toCoeff q) :=
    (hQ (μ (SpectralWeight.one.toCoeff q)-τ (SpectralWeight.one.toCoeff q),SpectralWeight.one.toCoeff q)
      ⟨by rw [hu0];exact mem_ball_self hρ,hqU⟩).comp
      (f := fun p : Coeff 2 => (μ p-τ p,p)) ((hμ.sub hτ).prod analyticAt_id)
  let β : Coeff 2 → ℂ := fun p => I*hillDirichletSheetRoot p (μ p)/B p*Q (μ p-τ p,p)
  have hβ : AnalyticAt ℂ β (SpectralWeight.one.toCoeff q) := ((analyticAt_const.mul hsheet).div hB hBn).mul hQt
  have hβ0 : β (SpectralWeight.one.toCoeff q) = 0 := by
    dsimp only [β]
    rw [hμ0,hillDirichletSheetRoot_eq_zero_of_halfLength_zero q hq hr k hk hhalf0,mul_zero,zero_div,zero_mul]
  have hβzero : ∀ b : ℂ, (fderiv ℂ β (SpectralWeight.one.toCoeff q))
      (hillL2DiscriminantGardnerDirection (SpectralWeight.one.toCoeff q) b)=0 := by
    intro b
    let R : Coeff 2 → ℂ := fun p => hillDirichletSheetRoot p (μ p)
    let J : Coeff 2 → ℂ := fun p => I/B p*Q (μ p-τ p,p)
    have hJ : AnalyticAt ℂ J (SpectralWeight.one.toCoeff q) := (analyticAt_const.div hB hBn).mul hQt
    have hR0 : R (SpectralWeight.one.toCoeff q)=0 := by
      change hillDirichletSheetRoot (SpectralWeight.one.toCoeff q) (μ (SpectralWeight.one.toCoeff q))=0
      rw [hμ0,hillDirichletSheetRoot_eq_zero_of_halfLength_zero q hq hr k hk hhalf0]
    have hRzero : (fderiv ℂ R (SpectralWeight.one.toCoeff q))
        (hillL2DiscriminantGardnerDirection (SpectralWeight.one.toCoeff q) b)=0 :=
      fderiv_hillDirichletSheetRoot_moving_gardner_eq_zero_of_closed q hq hr k hk hhalf0 μ hμ hμ0 hμzero b
    have he : β=(fun p => R p*J p) := by
      funext p
      dsimp only [β,R,J]
      ring
    rw [he, (hsheet.differentiableAt.hasFDerivAt.fun_mul hJ.differentiableAt.hasFDerivAt).fderiv]
    change R (SpectralWeight.one.toCoeff q)*
        ((fderiv ℂ J (SpectralWeight.one.toCoeff q)) (hillL2DiscriminantGardnerDirection (SpectralWeight.one.toCoeff q) b))+
      J (SpectralWeight.one.toCoeff q)*
        ((fderiv ℂ R (SpectralWeight.one.toCoeff q)) (hillL2DiscriminantGardnerDirection (SpectralWeight.one.toCoeff q) b))=0
    rw [hR0,hRzero,zero_mul,mul_zero,add_zero]
  obtain ⟨E,W,hE,hW,hgapE,hqW,hroot⟩ := exists_hillLocalDeflatedComplexRoot_gap_physical_matching q hq hr k hk
  obtain ⟨Y,hY,hqY,hdata⟩ := exists_hillLocalGapSymmetricData_physical_neighborhood q hq hr k hk
  have hμE : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 p0, μ (P p) ∈ E := by
    have hcont : ContinuousAt (fun p : RealPeriodOneHillPotential => μ (P p)) p0 :=
      ContinuousAt.comp (f := P) hμ.continuousAt hP.continuousAt
    have hbaseE : μ (P p0) ∈ E := by change μ (SpectralWeight.one.toCoeff q) ∈ E;rw [hμ0];exact hgapE hμgap
    exact hcont.preimage_mem_nhds (hE.mem_nhds hbaseE)
  refine ⟨β,hβ,hβ0,hβzero,?_⟩
  filter_upwards [hphysical,hμmatch,hμE,hW.mem_nhds hqW,hY.mem_nhds hqY] with p hp hμp hpE hpW hpY
  have hBp : B (P p) = hillDeflatedEnergyCanonicalRoot p.val p.property.1 p.property.2 k (hillDirichletEnergy p.val p.property.1 p.property.2 k hk) := by
    dsimp only [B]
    rw [(hroot p hpW _ hpE).2.2,hμp]
  have hβp : β (P p) = I*hillDirichletSheetRoot (P p) (hillDirichletEnergy p.val p.property.1 p.property.2 k hk)/
      hillDeflatedEnergyCanonicalRoot p.val p.property.1 p.property.2 k (hillDirichletEnergy p.val p.property.1 p.property.2 k hk)*
        Q ((hillDirichletEnergy p.val p.property.1 p.property.2 k hk : ℂ)-(hillRealGapCenter p.val p.property.1 p.property.2 k : ℂ),P p) := by
    dsimp only [β,τ]
    rw [hBp,hμp,(hdata p hpY).1]
  have hzero (hc' : hillRealGapHalfLength p.val p.property.1 p.property.2 k = 0) : β (P p) = 0 := by
    rw [hβp,hillDirichletSheetRoot_eq_zero_of_halfLength_zero p.val p.property.1 p.property.2 k hk hc',mul_zero,zero_div,zero_mul]
  have hQc : AnalyticOnNhd ℂ (fun w => Q (w,P p)) (ball (0:ℂ) ρ) := by
    intro w hw
    exact (hQ (w,P p) ⟨hw,hp.1⟩).comp (f := fun w : ℂ => (w,P p)) (analyticAt_id.prod analyticAt_const)
  have hterminal (hgap' : hillRealGapHalfLength p.val p.property.1 p.property.2 k ≠ 0) (θ : ℝ)
      (hpoint : cosineGapPoint (hillRealGapCenter p.val p.property.1 p.property.2 k)
        (hillRealGapHalfLength p.val p.property.1 p.property.2 k) (θ : ℂ) =
          (hillDirichletEnergy p.val p.property.1 p.property.2 k hk : ℂ))
      (hsin : Complex.sin (θ : ℂ) = hillDirichletGapSine p.val p.property.1 p.property.2 k hk) :
      β (P p) = hillAbelianCosinePrimitive p.val p.property.1 p.property.2 n hn k (θ : ℂ)-
        (if k=n then 1 else 0)*((θ : ℂ)-(Real.pi : ℂ)) := by
    rw [hβp]
    exact hillRegularAbelian_terminal_eq_quadratic p.val p.property.1 p.property.2 n k hn hk hgap'
      (fun w => Q (w,P p)) ρ hp.2.1 hQc (fun w hw => (hp.2.2 w hw).2) θ hpoint hsin
  refine ⟨?_,hzero,hterminal⟩
  by_cases hgap' : hillRealGapHalfLength p.val p.property.1 p.property.2 k = 0
  · rw [hzero hgap',zero_im]
  · obtain ⟨e,he,hpoint,_,hsin⟩ := exists_hillDirichlet_terminal_angle p.val p.property.1 p.property.2 k hk hgap'
    have hi : e.im = 0 := im_eq_zero_of_mem_real_segment (-Real.pi) Real.pi e (by simpa only [ofReal_neg] using he)
    have hre : e = (e.re : ℂ) := by apply Complex.ext <;> simp [hi]
    rw [hre] at hpoint hsin
    rw [hterminal hgap' e.re hpoint hsin]
    have hF := hillAbelianCosinePrimitive_im_eq_zero p.val p.property.1 p.property.2 n hn k hk e.re
    by_cases hkn : k=n
    · rw [if_pos hkn,one_mul]
      simp only [sub_im,hF,ofReal_im,sub_self]
    · rw [if_neg hkn,zero_mul,sub_zero]
      exact hF

/-- Every differentiable extension agreeing with the actual regular
correction near a closed real gap has zero Gardner derivative. -/
theorem fderiv_hillRegularAbelianCorrection_closed_extension_eq_zero
    (n k : ℕ) (hn : 1≤n) (hk : 1≤k) (hc : hillRealGapHalfLength q hq hr k=0)
    (C : Coeff 2 → ℂ) (hC : DifferentiableAt ℂ C (SpectralWeight.one.toCoeff q))
    (hmatch : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
      C (SpectralWeight.one.toCoeff p.val)=hillRegularAbelianCorrection p.val p.property.1 p.property.2 n hn k hk)
    (b : ℂ) :
    (fderiv ℂ C (SpectralWeight.one.toCoeff q))
      (hillL2DiscriminantGardnerDirection (SpectralWeight.one.toCoeff q) b)=0 := by
  have hab : hillRealLabels q hq hr (2*k-1)=hillRealLabels q hq hr (2*k) := by
    dsimp only [hillRealGapHalfLength] at hc
    linarith
  obtain ⟨β,hβ,_hβ0,hβzero,hphysical⟩ := exists_closed_stationary_model q hq hr h0q h0r n k hn hk hab
  have hβmatch : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
      β (SpectralWeight.one.toCoeff p.val)=hillRegularAbelianCorrection p.val p.property.1 p.property.2 n hn k hk := by
    filter_upwards [hphysical] with p hp
    by_cases hgap : hillRealGapHalfLength p.val p.property.1 p.property.2 k=0
    · rw [hillRegularAbelianCorrection_closed p.val p.property.1 p.property.2 n hn k hk hgap]
      exact hp.2.1 hgap
    · have hs := hillDirichletSelectedRealAngle_spec p.val p.property.1 p.property.2 k hk hgap
      rw [hillRegularAbelianCorrection,dif_neg hgap]
      exact hp.2.2 hgap _ hs.2.1 hs.2.2
  have he : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
      C (SpectralWeight.one.toCoeff p.val)=β (SpectralWeight.one.toCoeff p.val) := by
    filter_upwards [hmatch,hβmatch] with p hp hpβ
    exact hp.trans hpβ.symm
  rw [fderiv_eq_on_parity_of_eventuallyEq_realPotentials q hq hr C β hC hβ.differentiableAt he _
    (hillL2DiscriminantGardnerDirection_mem_parity _ b)]
  exact hβzero b

end NLS.KdV
