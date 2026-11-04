import NLS.KdV.HillGardnerPeriodDirections

/-! # A single-valued physical Abelian phase at every open selected gap -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.LinearVolterra NLS.ZakharovShabat NLS.ComplexAnalysis
namespace NLS.KdV
variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

/-- The terminal unit phase and the actual infinite regular correction
sum define a phase without choosing a branch of the terminal angle. -/
def hillDirichletAbelianPhase (n : ℕ) (hn : 1≤n) : ℂ :=
  -(hillDirichletGapCosine q hq hr n hn+I*hillDirichletGapSine q hq hr n hn)*
    exp (I*hillSummedRegularAbelianCorrection q hq hr n hn)

/-- Every actual sheeted terminal angle gives the same phase. -/
theorem hillDirichletAbelianPhase_eq_exp_terminal (n : ℕ) (hn : 1≤n)
    (hgap : hillRealGapHalfLength q hq hr n≠0) (e : ℂ)
    (hpoint : cosineGapPoint (hillRealGapCenter q hq hr n) (hillRealGapHalfLength q hq hr n) e=
      (hillDirichletEnergy q hq hr n hn : ℂ))
    (hsin : sin e=hillDirichletGapSine q hq hr n hn) :
    hillDirichletAbelianPhase q hq hr n hn=
      exp (I*(e-(Real.pi:ℂ)+hillSummedRegularAbelianCorrection q hq hr n hn)) := by
  have hcos : cos e=hillDirichletGapCosine q hq hr n hn := by
    apply (eq_div_iff (ofReal_ne_zero.mpr hgap)).mpr
    dsimp only [cosineGapPoint,hillDirichletGapCosine] at hpoint ⊢
    linear_combination hpoint
  have he : I*(e-(Real.pi:ℂ)+hillSummedRegularAbelianCorrection q hq hr n hn)=
      e*I+(-(Real.pi:ℂ)*I)+I*hillSummedRegularAbelianCorrection q hq hr n hn := by ring
  rw [he,exp_add,exp_add,neg_mul,exp_neg,exp_pi_mul_I]
  simp only [inv_neg,inv_one,exp_mul_I,hcos,hsin,hillDirichletAbelianPhase]
  ring

variable (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))
include h0q h0r

/-- The actual branch-independent phase has a genuine local analytic
extension with simultaneous trace- and period-direction derivative
identities. No Birkhoff-map or physical-action identification is assumed. -/
theorem exists_hillDirichletAbelianPhase_analytic_variation
    (n : ℕ) (hn : 1≤n) (hnopen : hillRealGapHalfLength q hq hr n≠0) :
    ∃ P : Coeff 2 → ℂ, AnalyticAt ℂ P (SpectralWeight.one.toCoeff q) ∧
      P (SpectralWeight.one.toCoeff q)=hillDirichletAbelianPhase q hq hr n hn ∧
      (∀ b : ℂ, (fderiv ℂ P (SpectralWeight.one.toCoeff q))
        (hillL2DiscriminantGardnerDirection (SpectralWeight.one.toCoeff q) b)=
          (-I*hillAbelianSelectedGlobalPsi q hq hr n hn b/2)*hillDirichletAbelianPhase q hq hr n hn) ∧
      (∀ m : ℕ, ∀ _ : 1≤m, (fderiv ℂ P (SpectralWeight.one.toCoeff q))
        (hillL2TracePeriodDirection q hq hr m)=
          I*(if m=n then 1 else 0)*hillDirichletAbelianPhase q hq hr n hn) ∧
      ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
        hillRealGapHalfLength p.val p.property.1 p.property.2 n≠0 ∧
        P (SpectralWeight.one.toCoeff p.val)=hillDirichletAbelianPhase p.val p.property.1 p.property.2 n hn := by
  obtain ⟨A,ε,e,hA,_hε,_hε0,_he,hDA,hphysical⟩ :=
    exists_hillDirichletAbelianAngle_gardner_variation q hq hr h0q h0r n hn hnopen
  let P : Coeff 2 → ℂ := fun p => exp (I*A p)
  have hP : AnalyticAt ℂ P (SpectralWeight.one.toCoeff q) := (analyticAt_const.mul hA).cexp
  have hmatch : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
      hillRealGapHalfLength p.val p.property.1 p.property.2 n≠0 ∧
      P (SpectralWeight.one.toCoeff p.val)=hillDirichletAbelianPhase p.val p.property.1 p.property.2 n hn := by
    filter_upwards [hphysical] with p hp
    refine ⟨hp.1,?_⟩
    dsimp only [P]
    rw [hp.2.2.2.2.1]
    exact (hillDirichletAbelianPhase_eq_exp_terminal p.val p.property.1 p.property.2 n hn hp.1 _ hp.2.2.1 hp.2.2.2.1).symm
  have hP0 := (hmatch.self_of_nhds).2
  have hDP : fderiv ℂ P (SpectralWeight.one.toCoeff q)=
      P (SpectralWeight.one.toCoeff q) • (I • fderiv ℂ A (SpectralWeight.one.toCoeff q)) :=
    (hA.differentiableAt.hasFDerivAt.const_mul I).cexp.fderiv
  refine ⟨P,hP,hP0,?_,?_,hmatch⟩
  · intro b
    rw [hDP]
    change P (SpectralWeight.one.toCoeff q)*(I*((fderiv ℂ A (SpectralWeight.one.toCoeff q)) _))=_
    rw [hDA b,hP0]
    ring
  · intro m hm
    rw [hDP]
    change P (SpectralWeight.one.toCoeff q)*(I*((fderiv ℂ A (SpectralWeight.one.toCoeff q)) _))=_
    rw [fderiv_hillAbelianAngle_tracePeriodDirection q hq hr n m hn hm A hDA,hP0]
    ring

/-- The actual physical Abelian phase lies on the unit circle. -/
theorem norm_hillDirichletAbelianPhase (n : ℕ) (hn : 1≤n)
    (hnopen : hillRealGapHalfLength q hq hr n≠0) :
    ‖hillDirichletAbelianPhase q hq hr n hn‖=1 := by
  obtain ⟨A,ε,e,_hA,_hε,_hε0,_he,_hDA,hphysical⟩ :=
    exists_hillDirichletAbelianAngle_gardner_variation q hq hr h0q h0r n hn hnopen
  have hp := hphysical.self_of_nhds
  rw [hillDirichletAbelianPhase_eq_exp_terminal q hq hr n hn hnopen _ hp.2.2.1 hp.2.2.2.1,
    ← hp.2.2.2.2.1]
  have heq : A (SpectralWeight.one.toCoeff q)=((A (SpectralWeight.one.toCoeff q)).re:ℂ) := by
    apply Complex.ext
    · rfl
    · simpa only [ofReal_im] using hp.2.2.2.2.2
  rw [heq,norm_exp_I_mul_ofReal]

/-- Any differentiable complex extension of the physical phase has the
same actual trace-direction derivative. This makes the variation
independent of the chosen local analytic angle lift. -/
theorem fderiv_hillDirichletAbelianPhase_extension
    (n : ℕ) (hn : 1≤n) (hnopen : hillRealGapHalfLength q hq hr n≠0)
    (C : Coeff 2 → ℂ) (hC : DifferentiableAt ℂ C (SpectralWeight.one.toCoeff q))
    (hmatch : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
      C (SpectralWeight.one.toCoeff p.val)=hillDirichletAbelianPhase p.val p.property.1 p.property.2 n hn)
    (b : ℂ) :
    (fderiv ℂ C (SpectralWeight.one.toCoeff q))
      (hillL2DiscriminantGardnerDirection (SpectralWeight.one.toCoeff q) b)=
      (-I*hillAbelianSelectedGlobalPsi q hq hr n hn b/2)*hillDirichletAbelianPhase q hq hr n hn := by
  obtain ⟨P,hP,_hP0,hDP,_hperiod,hphysical⟩ :=
    exists_hillDirichletAbelianPhase_analytic_variation q hq hr h0q h0r n hn hnopen
  have heq : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
      C (SpectralWeight.one.toCoeff p.val)=P (SpectralWeight.one.toCoeff p.val) := by
    filter_upwards [hmatch,hphysical] with p hp hpP
    exact hp.trans hpP.2.symm
  rw [fderiv_eq_on_parity_of_eventuallyEq_realPotentials q hq hr C P hC hP.differentiableAt heq _
    (hillL2DiscriminantGardnerDirection_mem_parity _ b)]
  exact hDP b

/-- The actual physical phase is continuous on the full open-gap locus
of real period-one L2 potentials, across all terminal branch cuts. -/
theorem continuousOn_hillDirichletAbelianPhase (n : ℕ) (hn : 1≤n) :
    ContinuousOn (fun p : RealPeriodOneHillPotential => hillDirichletAbelianPhase p.val p.property.1 p.property.2 n hn)
      {p | hillRealGapHalfLength p.val p.property.1 p.property.2 n≠0} := by
  intro p hp
  obtain ⟨P,hP,_hP0,_hDP,_hperiod,hphysical⟩ :=
    exists_hillDirichletAbelianPhase_analytic_variation p.val p.property.1 p.property.2 h0q h0r n hn hp
  have hc : Continuous (fun r : RealPeriodOneHillPotential => SpectralWeight.one.toCoeff r.val) :=
    SpectralWeight.one.toCoeff.continuous.comp continuous_subtype_val
  have hcont : ContinuousAt (fun r : RealPeriodOneHillPotential => P (SpectralWeight.one.toCoeff r.val)) p :=
    ContinuousAt.comp (f := fun r : RealPeriodOneHillPotential => SpectralWeight.one.toCoeff r.val)
      hP.continuousAt hc.continuousAt
  exact (hcont.congr_of_eventuallyEq (hphysical.mono (fun _ hr => hr.2.symm))).continuousWithinAt

end NLS.KdV
