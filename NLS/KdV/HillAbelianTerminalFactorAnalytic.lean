import NLS.KdV.HillAbelianCoordinateFactor

/-! # Analytic Dirichlet terminal factors through a collapsed own gap -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ZakharovShabat NLS.ComplexAnalysis
namespace NLS.KdV
variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

/-- The actual gap-division-free terminal factor has a complex analytic
extension at every real source. Its Gardner derivative vanishes at a
collapsed selected gap, without an angle coordinate or gap division. -/
theorem exists_hillDirichletAbelianTerminalFactor_analytic_extension
    (n : ℕ) (hn : 1≤n) :
    ∃ T : Coeff 2 → ℂ, AnalyticAt ℂ T (SpectralWeight.one.toCoeff q) ∧
      T (SpectralWeight.one.toCoeff q)=hillDirichletAbelianTerminalFactor q hq hr n hn ∧
      (hillRealGapHalfLength q hq hr n=0 → ∀ b : ℂ,
        (fderiv ℂ T (SpectralWeight.one.toCoeff q))
          (hillL2DiscriminantGardnerDirection (SpectralWeight.one.toCoeff q) b)=0) ∧
      ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
        T (SpectralWeight.one.toCoeff p.val)=hillDirichletAbelianTerminalFactor p.val p.property.1 p.property.2 n hn := by
  let p0 : RealPeriodOneHillPotential := ⟨q,hq,hr⟩
  let P : RealPeriodOneHillPotential → Coeff 2 := fun p => SpectralWeight.one.toCoeff p.val
  have hP : Continuous P := SpectralWeight.one.toCoeff.continuous.comp continuous_subtype_val
  obtain ⟨μ,hμ,hμ0,hμzero,hμmatch⟩ := exists_hillDirichletEnergy_analytic_extension p0 n hn
  obtain ⟨A,_,hqA,hM,_,_⟩ := exists_hillLocalGapSymmetricData_analytic_neighborhood q hq hr n hn
  let τ := hillLocalGapMidpoint q hq hr n
  have hτ : AnalyticAt ℂ τ (SpectralWeight.one.toCoeff q) := hM _ hqA
  have hμgap : (hillDirichletEnergy q hq hr n hn:ℂ)∈segment ℝ
      (hillRealLabels q hq hr (2*n-1):ℂ) (hillRealLabels q hq hr (2*n):ℂ) :=
    ofReal_mem_ordered_segment _ _ _ (monotone_hillRealLabels q hq hr (by omega : 2*n-1≤2*n))
      (hillDirichletEnergy_mem_gap q hq hr n hn)
  have hμball := hillRealGapSegment_subset_intrinsic_contour_ball q hq hr n hn hμgap
  have hdom0 : (μ (SpectralWeight.one.toCoeff q),SpectralWeight.one.toCoeff q)∈hillLocalDeflatedRootDomain q hq hr n := by
    rw [hμ0]
    exact mem_hillLocalDeflatedRootDomain_base q hq hr n hn _ hμball
  let B : Coeff 2 → ℂ := fun p => hillLocalDeflatedComplexRoot q hq hr n (μ p,p)
  have hB : AnalyticAt ℂ B (SpectralWeight.one.toCoeff q) :=
    (analyticOnNhd_hillLocalDeflatedComplexRoot q hq hr n hn _ hdom0).comp
      (f := fun p : Coeff 2 => (μ p,p)) (hμ.prod analyticAt_id)
  have hBn : B (SpectralWeight.one.toCoeff q)≠0 := hillLocalDeflatedComplexRoot_ne_zero q hq hr n hn _ hdom0
  let R : Coeff 2 → ℂ := fun p => hillDirichletSheetRoot p (μ p)
  have hR : AnalyticAt ℂ R (SpectralWeight.one.toCoeff q) :=
    (analyticOnNhd_hillDirichletSheetRoot_joint _ (mem_univ _)).comp
      (f := fun p : Coeff 2 => (μ p,p)) (hμ.prod analyticAt_id)
  let T : Coeff 2 → ℂ := fun p => R p/B p-(μ p-τ p)
  have hT : AnalyticAt ℂ T (SpectralWeight.one.toCoeff q) := (hR.div hB hBn).sub (hμ.sub hτ)
  obtain ⟨E,W,hE,hW,hgapE,hqW,hroot⟩ := exists_hillLocalDeflatedComplexRoot_gap_physical_matching q hq hr n hn
  obtain ⟨Y,hY,hqY,hdata⟩ := exists_hillLocalGapSymmetricData_physical_neighborhood q hq hr n hn
  have hμE : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 p0, μ (P p)∈E := by
    have hcont : ContinuousAt (fun p : RealPeriodOneHillPotential => μ (P p)) p0 :=
      ContinuousAt.comp (f := P) hμ.continuousAt hP.continuousAt
    have hb : μ (P p0)∈E := by change μ (SpectralWeight.one.toCoeff q)∈E;rw [hμ0];exact hgapE hμgap
    exact hcont.preimage_mem_nhds (hE.mem_nhds hb)
  have hmatch : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 p0,
      T (P p)=hillDirichletAbelianTerminalFactor p.val p.property.1 p.property.2 n hn := by
    filter_upwards [hμmatch,hμE,hW.mem_nhds hqW,hY.mem_nhds hqY] with p hμp hpE hpW hpY
    have hBp : B (P p)=hillDeflatedEnergyCanonicalRoot p.val p.property.1 p.property.2 n
        (hillDirichletEnergy p.val p.property.1 p.property.2 n hn) := by
      dsimp only [B]
      rw [(hroot p hpW _ hpE).2.2,hμp]
    dsimp only [T,R,τ,hillDirichletAbelianTerminalFactor]
    rw [hBp,hμp,(hdata p hpY).1]
  refine ⟨T,hT,hmatch.self_of_nhds,?_,hmatch⟩
  intro hc b
  have hR0 : R (SpectralWeight.one.toCoeff q)=0 := by
    dsimp only [R]
    rw [hμ0,hillDirichletSheetRoot_eq_zero_of_halfLength_zero q hq hr n hn hc]
  have hDR : (fderiv ℂ R (SpectralWeight.one.toCoeff q))
      (hillL2DiscriminantGardnerDirection (SpectralWeight.one.toCoeff q) b)=0 :=
    fderiv_hillDirichletSheetRoot_moving_gardner_eq_zero_of_closed q hq hr n hn hc μ hμ hμ0 hμzero b
  have hDμ : (fderiv ℂ μ (SpectralWeight.one.toCoeff q))
      (hillL2DiscriminantGardnerDirection (SpectralWeight.one.toCoeff q) b)=0 := by
    rw [hillDirichlet_branch_gardner_eq_kernel p0 n hn μ hμ hμ0 hμzero b]
    change R (SpectralWeight.one.toCoeff q)*_=0
    rw [hR0,zero_mul]
  let J : Coeff 2 → ℂ := fun p => (B p)⁻¹
  have hJ : AnalyticAt ℂ J (SpectralWeight.one.toCoeff q) := hB.inv hBn
  have hDT := ((hR.differentiableAt.hasFDerivAt.fun_mul hJ.differentiableAt.hasFDerivAt).sub
    (hμ.differentiableAt.hasFDerivAt.sub hτ.differentiableAt.hasFDerivAt)).fderiv
  have he : (fun p => R p*J p-(μ p-τ p))=T := by funext p;rfl
  change fderiv ℂ (fun p => R p*J p-(μ p-τ p)) (SpectralWeight.one.toCoeff q)=_ at hDT
  rw [he] at hDT
  rw [hDT]
  change R (SpectralWeight.one.toCoeff q)*((fderiv ℂ J _) _)+
    J (SpectralWeight.one.toCoeff q)*((fderiv ℂ R _) _)-
      ((fderiv ℂ μ _) _-(fderiv ℂ τ _) _)=0
  rw [hR0,hDR,hDμ,fderiv_hillLocalGapMidpoint_gardnerDirection_eq_zero q hq hr n hn b,
    zero_mul,mul_zero,add_zero,sub_self,sub_self]

end NLS.KdV
