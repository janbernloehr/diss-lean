import NLS.KdV.HillDeflatedRootEnergyDerivative
import NLS.KdV.HillDirichletSheetVariation
import NLS.KdV.HillDirichletAnalyticAngles
import NLS.ComplexAnalysis.QuadraticSheetTerminalVariation

/-! # Actual sheeted Dirichlet angle variation, including terminal bandedges -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV

/-- The actual Dirichlet divided difference with its filled diagonal value. -/
def hillDirichletGardnerKernel (q : RealPeriodOneHillPotential) (k : ℕ) (hk : 1≤k) (b : ℂ) : ℂ :=
  let E : ℂ := hillDirichletEnergy q.val q.property.1 q.property.2 k hk
  let p := SpectralWeight.one.toCoeff q.val
  if b=E then -1/2 else hillL2DirichletCharacteristic p b/(2*(E-b)*deriv (hillL2DirichletCharacteristic p) E)

theorem hillDirichlet_branch_gardner_eq_kernel
    (q : RealPeriodOneHillPotential) (k : ℕ) (hk : 1≤k) (a : Coeff 2 → ℂ)
    (ha : AnalyticAt ℂ a (SpectralWeight.one.toCoeff q.val))
    (ha0 : a (SpectralWeight.one.toCoeff q.val)=(hillDirichletEnergy q.val q.property.1 q.property.2 k hk : ℂ))
    (hz : ∀ᶠ p in 𝓝 (SpectralWeight.one.toCoeff q.val), hillL2DirichletCharacteristic p (a p)=0) (b : ℂ) :
    (fderiv ℂ a (SpectralWeight.one.toCoeff q.val)) (hillL2DiscriminantGardnerDirection (SpectralWeight.one.toCoeff q.val) b)=
      hillDirichletSheetRoot (SpectralWeight.one.toCoeff q.val) (a (SpectralWeight.one.toCoeff q.val))*
        hillDirichletGardnerKernel q k hk b := by
  rw [hillDirichlet_branch_fderiv_discriminantGardnerDirection q k hk a ha ha0 hz b,ha0]
  unfold hillDirichletGardnerKernel
  dsimp only
  split_ifs with hb
  · rw [hb,hillDirichletDiscriminantGardnerBracket_diagonal]
    ring
  · rw [hillDirichletDiscriminantGardnerBracket_eq_sheet_quotient q k hk b (Ne.symm hb)]
    ring

theorem hillDirichletSheetRoot_moving_gardner_eq_kernel
    (q : RealPeriodOneHillPotential) (k : ℕ) (hk : 1≤k) (a : Coeff 2 → ℂ)
    (ha : AnalyticAt ℂ a (SpectralWeight.one.toCoeff q.val))
    (ha0 : a (SpectralWeight.one.toCoeff q.val)=(hillDirichletEnergy q.val q.property.1 q.property.2 k hk : ℂ))
    (hz : ∀ᶠ p in 𝓝 (SpectralWeight.one.toCoeff q.val), hillL2DirichletCharacteristic p (a p)=0) (b : ℂ) :
    let p := SpectralWeight.one.toCoeff q.val
    let E := a p
    (fderiv ℂ (fun r : Coeff 2 => hillDirichletSheetRoot r (a r)) p) (hillL2DiscriminantGardnerDirection p b)=
      (hillL2Discriminant p E*deriv (hillL2Discriminant p) E)*hillDirichletGardnerKernel q k hk b := by
  dsimp only
  rw [ha0]
  unfold hillDirichletGardnerKernel
  dsimp only
  split_ifs with hb
  · rw [hb,hillDirichletSheetRoot_moving_gardner_diagonal q k hk a ha ha0 hz]
    ring
  · rw [hillDirichletSheetRoot_moving_gardner_off_diagonal q k hk a ha ha0 hz b hb]
    ring

private theorem terminalAngle_velocity
    (q : RealPeriodOneHillPotential) (k : ℕ) (hk : 1≤k) (a d ε : Coeff 2 → ℂ)
    (ha : AnalyticAt ℂ a (SpectralWeight.one.toCoeff q.val))
    (ha0 : a (SpectralWeight.one.toCoeff q.val)=(hillDirichletEnergy q.val q.property.1 q.property.2 k hk : ℂ))
    (haz : ∀ᶠ p in 𝓝 (SpectralWeight.one.toCoeff q.val), hillL2DirichletCharacteristic p (a p)=0)
    (hd : AnalyticAt ℂ d (SpectralWeight.one.toCoeff q.val))
    (hd0 : d (SpectralWeight.one.toCoeff q.val)=(hillRealGapHalfLength q.val q.property.1 q.property.2 k : ℂ))
    (hdne : d (SpectralWeight.one.toCoeff q.val)≠0)
    (hdsq : ∀ᶠ p in 𝓝 (SpectralWeight.one.toCoeff q.val),
      d p^2=hillLocalGapSquare q.val q.property.1 q.property.2 k p/4)
    (hε : DifferentiableAt ℂ ε (SpectralWeight.one.toCoeff q.val))
    (hpoint : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      hillLocalGapMidpoint q.val q.property.1 q.property.2 k (SpectralWeight.one.toCoeff p.val)+
        d (SpectralWeight.one.toCoeff p.val)*Complex.cos (ε (SpectralWeight.one.toCoeff p.val))=
          a (SpectralWeight.one.toCoeff p.val))
    (hsheet : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      -I*d (SpectralWeight.one.toCoeff p.val)*
        hillLocalDeflatedComplexRoot q.val q.property.1 q.property.2 k
          (a (SpectralWeight.one.toCoeff p.val),SpectralWeight.one.toCoeff p.val)*
        Complex.sin (ε (SpectralWeight.one.toCoeff p.val))=
          hillDirichletSheetRoot (SpectralWeight.one.toCoeff p.val) (a (SpectralWeight.one.toCoeff p.val))) (b : ℂ) :
    let p := SpectralWeight.one.toCoeff q.val
    (fderiv ℂ ε p) (hillL2DiscriminantGardnerDirection p b)=
      I*hillDeflatedEnergyCanonicalRoot q.val q.property.1 q.property.2 k (a p)*hillDirichletGardnerKernel q k hk b := by
  let p := SpectralWeight.one.toCoeff q.val
  let X := hillL2DiscriminantGardnerDirection p b
  let τ := hillLocalGapMidpoint q.val q.property.1 q.property.2 k
  let U := hillLocalDeflatedComplexRoot q.val q.property.1 q.property.2 k
  let B : Coeff 2 → ℂ := fun r => U (a r,r)
  let S : Coeff 2 → ℂ := fun r => hillDirichletSheetRoot r (a r)
  let v := hillDirichletGardnerKernel q k hk b
  have hball : a p∈ball (hillRealGapCenter q.val q.property.1 q.property.2 k : ℂ)
      (hillRealGapHalfLength q.val q.property.1 q.property.2 k+hillRealGapCollar q.val q.property.1 q.property.2 k) := by
    rw [ha0]
    exact hillRealGapSegment_subset_intrinsic_contour_ball q.val q.property.1 q.property.2 k hk
      (ofReal_mem_ordered_segment _ _ _ (monotone_hillRealLabels q.val q.property.1 q.property.2 (by omega : 2*k-1≤2*k))
        (hillDirichletEnergy_mem_gap q.val q.property.1 q.property.2 k hk))
  have hdom := mem_hillLocalDeflatedRootDomain_base q.val q.property.1 q.property.2 k hk (a p) hball
  have hU := analyticOnNhd_hillLocalDeflatedComplexRoot q.val q.property.1 q.property.2 k hk (a p,p) hdom
  have hB : DifferentiableAt ℂ B p := (hU.comp (f := fun r : Coeff 2 => (a r,r)) (ha.prod analyticAt_id)).differentiableAt
  have hBne : B p≠0 := hillLocalDeflatedComplexRoot_ne_zero q.val q.property.1 q.property.2 k hk (a p,p) hdom
  have hS : DifferentiableAt ℂ S p := ((analyticOnNhd_hillDirichletSheetRoot_joint (a p,p) (mem_univ _)).comp
    (f := fun r : Coeff 2 => (a r,r)) (ha.prod analyticAt_id)).differentiableAt
  obtain ⟨A,_,hqA,hM,_,_⟩ := exists_hillLocalGapSymmetricData_analytic_neighborhood q.val q.property.1 q.property.2 k hk
  have hτ : DifferentiableAt ℂ τ p := (hM p hqA).differentiableAt
  have hτzero := fderiv_hillLocalGapMidpoint_gardnerDirection_eq_zero q.val q.property.1 q.property.2 k hk b
  have hdzero := fderiv_hillGapHalfLength_root_gardnerDirection_eq_zero q.val q.property.1 q.property.2 k hk d hd.differentiableAt hdne hdsq b
  change (fderiv ℂ τ p) X=0 at hτzero
  change (fderiv ℂ d p) X=0 at hdzero
  have hμvariation : (fderiv ℂ a p) X=-(d p*Complex.sin (ε p))*(fderiv ℂ ε p) X := by
    have he := fderiv_eq_on_parity_of_eventuallyEq_realPotentials q.val q.property.1 q.property.2
      (fun r => τ r+d r*Complex.cos (ε r)) a
      (hτ.add (hd.differentiableAt.mul hε.ccos)) ha.differentiableAt hpoint X
      (hillL2DiscriminantGardnerDirection_mem_parity p b)
    rw [(hτ.hasFDerivAt.fun_add (hd.differentiableAt.hasFDerivAt.fun_mul hε.hasFDerivAt.ccos)).fderiv] at he
    simp only [add_apply,smul_apply,smul_eq_mul] at he
    change (fderiv ℂ τ p) X+(d p*(-Complex.sin (ε p)*(fderiv ℂ ε p) X)+
      Complex.cos (ε p)*(fderiv ℂ d p) X)=(fderiv ℂ a p) X at he
    rw [hτzero,hdzero] at he
    linear_combination -he
  have hSvariation : (fderiv ℂ S p) X=-I*d p*
      ((fderiv ℂ B p) X*Complex.sin (ε p)+B p*Complex.cos (ε p)*(fderiv ℂ ε p) X) := by
    have he := fderiv_eq_on_parity_of_eventuallyEq_realPotentials q.val q.property.1 q.property.2
      (fun r => -I*d r*B r*Complex.sin (ε r)) S
      (((hd.differentiableAt.const_mul (-I)).mul hB).mul hε.csin) hS hsheet X
      (hillL2DiscriminantGardnerDirection_mem_parity p b)
    have hder := ((((hasFDerivAt_const (-I) p).fun_mul hd.differentiableAt.hasFDerivAt).fun_mul hB.hasFDerivAt).fun_mul hε.hasFDerivAt.csin).fderiv
    rw [hder] at he
    simp only [add_apply,smul_apply,smul_eq_mul,zero_apply,mul_zero,add_zero] at he
    change -I*d p*B p*(Complex.cos (ε p)*(fderiv ℂ ε p) X)+
      Complex.sin (ε p)*(-I*d p*(fderiv ℂ B p) X+B p*(-I*(fderiv ℂ d p) X))=(fderiv ℂ S p) X at he
    rw [hdzero] at he
    linear_combination -he
  have hcoords : τ p+d p*Complex.cos (ε p)=a p := Filter.Eventually.self_of_nhds (x := q) hpoint
  have hSnorm : S p=-I*d p*B p*Complex.sin (ε p) := (Filter.Eventually.self_of_nhds (x := q) hsheet).symm
  have hroot : (fderiv ℂ a p) X=S p*v := hillDirichlet_branch_gardner_eq_kernel q k hk a ha ha0 haz b
  have hanti := hillDirichletSheetRoot_moving_gardner_eq_kernel q k hk a ha ha0 haz b
  have hKflow : (fderiv ℂ B p) X=
      deriv (fun z : ℂ => U (z,p)) (a p)*S p*v := by
    have he := congrArg (fun L : Coeff 2 →L[ℂ] ℂ => L X)
      (fderiv_moving_spectral_parameter U a p hU.differentiableAt ha.differentiableAt)
    change (fderiv ℂ B p) X=(fderiv ℂ (fun r => U (a p,r)) p) X+
      deriv (fun z => U (z,p)) (a p)*(fderiv ℂ a p) X at he
    rw [fderiv_hillLocalDeflatedComplexRoot_gardnerDirection_eq_zero q.val q.property.1 q.property.2 k hk (a p) b hball,
      zero_add,hroot] at he
    exact he.trans (by ring)
  have hphysical := hillLocalGapSymmetricData_eq_physical_of_geometry q.val q.property.1 q.property.2 q.val q.property.1 q.property.2 k hk
    (hillRealGapContour_band_bounds q.val q.property.1 q.property.2 k hk)
    (hillRealGapSegment_subset_intrinsic_contour_ball q.val q.property.1 q.property.2 k hk)
  have hfactor := hillDeflatedEnergyCanonicalRoot_energy_factor q.val q.property.1 q.property.2 k hk (a p)
    (hillRealGapContour_closedBall_subset_filledDomain q.val q.property.1 q.property.2 k hk (ball_subset_closedBall hball))
  have hbase : B p=hillDeflatedEnergyCanonicalRoot q.val q.property.1 q.property.2 k (a p) :=
    hillLocalDeflatedComplexRoot_base q.val q.property.1 q.property.2 k hk (a p) hball
  have henergy : deriv (fun z => U (z,p)) (a p)=deriv (hillDeflatedEnergyCanonicalRoot q.val q.property.1 q.property.2 k) (a p) :=
    deriv_hillLocalDeflatedComplexRoot_base q.val q.property.1 q.property.2 k hk (a p) hball
  have hflow : (fderiv ℂ S p) X=
      (B p*deriv (fun z => U (z,p)) (a p)*(-(d p)^2*Complex.sin (ε p)^2)+
        (B p)^2*d p*Complex.cos (ε p))*v := by
    have hc : a p-(hillRealGapCenter q.val q.property.1 q.property.2 k : ℂ)=d p*Complex.cos (ε p) := by
      have hm : τ p=(hillRealGapCenter q.val q.property.1 q.property.2 k : ℂ) := hphysical.1
      rw [← hm]
      linear_combination -hcoords
    change (fderiv ℂ S p) X=(hillL2Discriminant p (a p)*deriv (hillL2Discriminant p) (a p))*v at hanti
    rw [hfactor,← hbase,← henergy,hc,← hd0] at hanti
    change (fderiv ℂ S p) X=(d p*Complex.cos (ε p)*(B p)^2+
      ((d p*Complex.cos (ε p))^2-(d p)^2)*B p*deriv (fun z => U (z,p)) (a p))*v at hanti
    linear_combination hanti+(B p*deriv (fun z => U (z,p)) (a p)*(d p)^2*v)*Complex.sin_sq_add_cos_sq (ε p)
  have he := quadratic_cosine_angle_variation_of_flow (d p) (B p)
    (deriv (fun z => U (z,p)) (a p)) (Complex.sin (ε p)) (Complex.cos (ε p))
    ((fderiv ℂ ε p) X) v (S p) ((fderiv ℂ S p) X) ((fderiv ℂ B p) X)
    hdne hBne (Complex.sin_sq_add_cos_sq (ε p)) hSnorm
    (by rw [← hroot,hμvariation];ring) hflow hKflow hSvariation
  change (fderiv ℂ ε p) X=_
  rw [he,hbase]

/-- Every differentiable sheeted terminal-angle extension with genuine
nearby-real agreement has the actual Gardner velocity. Both trigonometric
coordinates are used, so the statement includes terminal bandedges. -/
theorem fderiv_hillDirichletTerminalAngle_gardnerDirection
    (q : RealPeriodOneHillPotential) (k : ℕ) (hk : 1≤k)
    (hgap : hillRealGapHalfLength q.val q.property.1 q.property.2 k≠0)
    (ε : Coeff 2 → ℂ) (hε : DifferentiableAt ℂ ε (SpectralWeight.one.toCoeff q.val))
    (hterminal : ∀ᶠ r : RealPeriodOneHillPotential in 𝓝 q,
      cosineGapPoint (hillRealGapCenter r.val r.property.1 r.property.2 k)
        (hillRealGapHalfLength r.val r.property.1 r.property.2 k) (ε (SpectralWeight.one.toCoeff r.val))=
          (hillDirichletEnergy r.val r.property.1 r.property.2 k hk : ℂ) ∧
      Complex.sin (ε (SpectralWeight.one.toCoeff r.val))=hillDirichletGapSine r.val r.property.1 r.property.2 k hk)
    (b : ℂ) :
    (fderiv ℂ ε (SpectralWeight.one.toCoeff q.val)) (hillL2DiscriminantGardnerDirection (SpectralWeight.one.toCoeff q.val) b)=
      I*hillDeflatedEnergyCanonicalRoot q.val q.property.1 q.property.2 k
        (hillDirichletEnergy q.val q.property.1 q.property.2 k hk)*hillDirichletGardnerKernel q k hk b := by
  let P : RealPeriodOneHillPotential → Coeff 2 := fun r => SpectralWeight.one.toCoeff r.val
  have hP : Continuous P := SpectralWeight.one.toCoeff.continuous.comp continuous_subtype_val
  obtain ⟨d,hd,hd0,hdprop,hdreal⟩ := exists_hillGapHalfLength_analytic_extension q.val q.property.1 q.property.2 k hk hgap
  obtain ⟨a,ha,ha0,haz,hareal⟩ := exists_hillDirichletEnergy_analytic_extension q k hk
  obtain ⟨E,W,hE,hW,hgapE,hqW,hrootmatch⟩ := exists_hillLocalDeflatedComplexRoot_gap_physical_matching q.val q.property.1 q.property.2 k hk
  obtain ⟨T,hT,hqT,hmidmatch⟩ := exists_hillLocalGapSymmetricData_physical_neighborhood q.val q.property.1 q.property.2 k hk
  have hμsegment : a (P q)∈segment ℝ (hillRealLabels q.val q.property.1 q.property.2 (2*k-1) : ℂ)
      (hillRealLabels q.val q.property.1 q.property.2 (2*k) : ℂ) := by
    rw [ha0]
    exact ofReal_mem_ordered_segment _ _ _ (monotone_hillRealLabels q.val q.property.1 q.property.2 (by omega : 2*k-1≤2*k))
      (hillDirichletEnergy_mem_gap q.val q.property.1 q.property.2 k hk)
  have hμE : ∀ᶠ r : RealPeriodOneHillPotential in 𝓝 q, a (P r)∈E :=
    (ha.continuousAt.comp (f := P) hP.continuousAt).preimage_mem_nhds (hE.mem_nhds (hgapE hμsegment))
  have hball := hillRealGapSegment_subset_intrinsic_contour_ball q.val q.property.1 q.property.2 k hk hμsegment
  have hdom := mem_hillLocalDeflatedRootDomain_base q.val q.property.1 q.property.2 k hk (a (P q)) hball
  let B : Coeff 2 → ℂ := fun p => hillLocalDeflatedComplexRoot q.val q.property.1 q.property.2 k (a p,p)
  have hB : AnalyticAt ℂ B (P q) :=
    (analyticOnNhd_hillLocalDeflatedComplexRoot q.val q.property.1 q.property.2 k hk _ hdom).comp
      (f := fun p : Coeff 2 => (a p,p)) (ha.prod analyticAt_id)
  have hBne : B (P q)≠0 := hillLocalDeflatedComplexRoot_ne_zero q.val q.property.1 q.property.2 k hk _ hdom
  have hBn : ∀ᶠ r : RealPeriodOneHillPotential in 𝓝 q, B (P r)≠0 :=
    hP.continuousAt.tendsto.eventually (hB.continuousAt.eventually_ne hBne)
  have hpoint : ∀ᶠ r : RealPeriodOneHillPotential in 𝓝 q,
      hillLocalGapMidpoint q.val q.property.1 q.property.2 k (P r)+d (P r)*Complex.cos (ε (P r))=a (P r) := by
    filter_upwards [hterminal,hdreal,hareal,hT.mem_nhds hqT] with r ht hdr har hrT
    rw [(hmidmatch r hrT).1,hdr,har]
    exact ht.1
  have hsheet : ∀ᶠ r : RealPeriodOneHillPotential in 𝓝 q,
      -I*d (P r)*B (P r)*Complex.sin (ε (P r))=hillDirichletSheetRoot (P r) (a (P r)) := by
    filter_upwards [hterminal,hdreal,hareal,hμE,hW.mem_nhds hqW,hBn,
      hP.continuousAt.tendsto.eventually hdprop] with r ht hdr har hrE hrW hBr hdrp
    have hroot : B (P r)=hillDeflatedEnergyCanonicalRoot r.val r.property.1 r.property.2 k (a (P r)) :=
      (hrootmatch r hrW _ hrE).2.2
    have hs : Complex.sin (ε (P r))=I*hillDirichletSheetRoot (P r) (a (P r))/(d (P r)*B (P r)) := by
      rw [ht.2,hdr,hroot,har]
      rfl
    rw [hs]
    field_simp [hdrp.1,hBr]
    simp only [I_sq]
    ring
  have hv := terminalAngle_velocity q k hk a d ε ha ha0 haz hd hd0
    (hd0 ▸ ofReal_ne_zero.mpr hgap) (hdprop.mono (fun _ hp => hp.2)) hε hpoint hsheet b
  simpa only [ha0] using hv

end NLS.KdV
