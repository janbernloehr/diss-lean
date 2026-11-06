import NLS.KdV.HillFreeDirichletDifferential
import NLS.KdV.HillDirichletLenardSheetVariation
import NLS.KdV.HillTraceStationaryData
/-! # The actual free terminal coordinate has the Fourier differential -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat NLS.LinearVolterra
namespace NLS.KdV
variable
    (hq : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem exists_hillDirichletAbelianTerminalFactor_free_differential
    (n : ℕ) (hn : 1≤n) :
    ∃ T : Coeff 2 → ℂ, AnalyticAt ℂ T 0 ∧ T 0=0 ∧
      (∀ h : Coeff 2, h∈Coeff.paritySubspace 0 → h 0=0 →
        (fderiv ℂ T 0) h=h (2*(n:ℤ))) ∧
      ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨0,hq,hr⟩ : RealPeriodOneHillPotential),
        T (SpectralWeight.one.toCoeff p.val)=hillDirichletAbelianTerminalFactor p.val p.property.1 p.property.2 n hn := by
  let p0 : RealPeriodOneHillPotential := ⟨0,hq,hr⟩
  let P : RealPeriodOneHillPotential → Coeff 2 := fun p => SpectralWeight.one.toCoeff p.val
  have hP : Continuous P := SpectralWeight.one.toCoeff.continuous.comp continuous_subtype_val
  obtain ⟨μ,hμ,hμ0,hμzero,hμmatch⟩ := exists_hillDirichletEnergy_analytic_extension p0 n hn
  obtain ⟨A,_,hqA,hM,_,_⟩ := exists_hillLocalGapSymmetricData_analytic_neighborhood 0 hq hr n hn
  let τ := hillLocalGapMidpoint 0 hq hr n
  have hτ : AnalyticAt ℂ τ (SpectralWeight.one.toCoeff 0) := hM _ hqA
  have hμgap : (hillDirichletEnergy 0 hq hr n hn:ℂ)∈segment ℝ
      (hillRealLabels 0 hq hr (2*n-1):ℂ) (hillRealLabels 0 hq hr (2*n):ℂ) :=
    ofReal_mem_ordered_segment _ _ _ (monotone_hillRealLabels 0 hq hr (by omega : 2*n-1≤2*n))
      (hillDirichletEnergy_mem_gap 0 hq hr n hn)
  have hμball := hillRealGapSegment_subset_intrinsic_contour_ball 0 hq hr n hn hμgap
  have hdom0 : (μ (SpectralWeight.one.toCoeff 0),SpectralWeight.one.toCoeff 0)∈hillLocalDeflatedRootDomain 0 hq hr n := by
    rw [hμ0]
    exact mem_hillLocalDeflatedRootDomain_base 0 hq hr n hn _ hμball
  let B : Coeff 2 → ℂ := fun p => hillLocalDeflatedComplexRoot 0 hq hr n (μ p,p)
  have hB : AnalyticAt ℂ B (SpectralWeight.one.toCoeff 0) :=
    (analyticOnNhd_hillLocalDeflatedComplexRoot 0 hq hr n hn _ hdom0).comp
      (f := fun p : Coeff 2 => (μ p,p)) (hμ.prod analyticAt_id)
  have hBn : B (SpectralWeight.one.toCoeff 0)≠0 := hillLocalDeflatedComplexRoot_ne_zero 0 hq hr n hn _ hdom0
  let R : Coeff 2 → ℂ := fun p => hillDirichletSheetRoot p (μ p)
  have hR : AnalyticAt ℂ R (SpectralWeight.one.toCoeff 0) :=
    (analyticOnNhd_hillDirichletSheetRoot_joint _ (mem_univ _)).comp
      (f := fun p : Coeff 2 => (μ p,p)) (hμ.prod analyticAt_id)
  let T : Coeff 2 → ℂ := fun p => R p/B p-(μ p-τ p)
  have hT : AnalyticAt ℂ T (SpectralWeight.one.toCoeff 0) := (hR.div hB hBn).sub (hμ.sub hτ)
  obtain ⟨E,W,hE,hW,hgapE,hqW,hroot⟩ := exists_hillLocalDeflatedComplexRoot_gap_physical_matching 0 hq hr n hn
  obtain ⟨Y,hY,hqY,hdata⟩ := exists_hillLocalGapSymmetricData_physical_neighborhood 0 hq hr n hn
  have hμE : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 p0, μ (P p)∈E := by
    have hcont : ContinuousAt (fun p : RealPeriodOneHillPotential => μ (P p)) p0 :=
      ContinuousAt.comp (f := P) hμ.continuousAt hP.continuousAt
    have hb : μ (P p0)∈E := by change μ (SpectralWeight.one.toCoeff 0)∈E;rw [hμ0];exact hgapE hμgap
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
  have hμa : AnalyticAt ℂ μ 0 := by simpa only [p0,map_zero] using hμ
  have hRa : AnalyticAt ℂ R 0 := by simpa only [map_zero] using hR
  have hBa : AnalyticAt ℂ B 0 := by simpa only [map_zero] using hB
  have hτa : AnalyticAt ℂ τ 0 := by simpa only [map_zero] using hτ
  have hBna : B 0≠0 := by simpa only [map_zero] using hBn
  have hμfree : μ 0=(freeHillValue n:ℂ) := by
    simpa only [p0,map_zero,hillDirichletEnergy_zero_potential hq hr n hn] using hμ0
  have hμz : ∀ᶠ p in 𝓝 (0:Coeff 2),hillL2DirichletCharacteristic p (μ p)=0 := by
    simpa only [p0,map_zero] using hμzero
  have hR0 : R 0=0 := by dsimp only [R];exact hillDirichletSheetRoot_free _
  have hT0 : T 0=0 := by
    have hc : hillRealGapHalfLength 0 hq hr n=0 := by
      dsimp only [hillRealGapHalfLength]
      rw [(hillFreeGapEndpoints hq hr n hn).1,(hillFreeGapEndpoints hq hr n hn).2]
      simp
    simpa only [P,p0,map_zero,hillDirichletAbelianTerminalFactor_closed 0 hq hr n hn hc] using hmatch.self_of_nhds
  have hBbase : B (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2))=
      hillDeflatedEnergyCanonicalRoot 0 hq hr n (hillDirichletEnergy 0 hq hr n hn) := by
    dsimp only [B]
    rw [hμ0]
    exact hillLocalDeflatedComplexRoot_base 0 hq hr n hn _ hμball
  have hBfree : B 0=I*(-1:ℂ)^n/((n:ℂ)*Real.pi) := by
    simpa only [p0,map_zero,hillDirichletEnergy_zero_potential hq hr n hn,
      hillDeflatedEnergyCanonicalRoot_free_center hq hr n hn] using hBbase
  refine ⟨T,by simpa only [map_zero] using hT,hT0,?_,hmatch⟩
  intro h hh hm
  have hmean := integral_hillPhysicalDirection_eq_zero_of_even h hh hm
  have htrace (E : ℂ) : (fderiv ℂ (fun p : Coeff 2 => hillL2Discriminant p E) 0) h=0 :=
    fderiv_hillL2Discriminant_free_of_mean_zero h hmean E
  have hτzero : (fderiv ℂ τ 0) h=0 := by
    simpa only [map_zero] using
      fderiv_hillLocalGapMidpoint_of_trace_stationary 0 hq hr n hn h (by simpa only [map_zero] using htrace)
  have hDR : (fderiv ℂ R 0) h=
      2*((fderiv ℂ (fun p : Coeff 2 => hillL2DirichletSlope p (freeHillValue n)) 0) h) := by
    let F : ℂ × Coeff 2 → ℂ := fun t => hillDirichletSheetRoot t.2 t.1
    have hF : AnalyticAt ℂ F (μ 0,0) := analyticOnNhd_hillDirichletSheetRoot_joint _ (mem_univ _)
    have hd := fderiv_moving_spectral_parameter F μ 0 hF.differentiableAt hμa.differentiableAt
    have hFzero : (fun E => F (E,0))=fun _ => (0:ℂ) := funext hillDirichletSheetRoot_free
    have hEzero : deriv (fun E => F (E,0)) (μ 0)=0 := by rw [hFzero];simp
    dsimp only [R]
    rw [hd]
    simp only [add_apply,smul_apply,smul_eq_mul,hEzero,zero_mul,add_zero]
    dsimp only [F]
    rw [hμfree]
    exact fderiv_hillDirichletSheetRoot_of_trace_zero 0 _ h (htrace _)
  have hDμ := hillDirichlet_branch_fderiv_free_integral n hn μ hμa hμfree hμz h
  let J : Coeff 2 → ℂ := fun p => (B p)⁻¹
  have hJa : AnalyticAt ℂ J 0 := hBa.inv hBna
  have hDT := ((hRa.differentiableAt.hasFDerivAt.fun_mul hJa.differentiableAt.hasFDerivAt).sub
    (hμa.differentiableAt.hasFDerivAt.sub hτa.differentiableAt.hasFDerivAt)).fderiv
  have he : (fun p => R p*J p-(μ p-τ p))=T := by funext p;rfl
  change fderiv ℂ (fun p => R p*J p-(μ p-τ p)) 0=_ at hDT
  rw [he] at hDT
  rw [hDT]
  change R 0*((fderiv ℂ J 0) h)+J 0*((fderiv ℂ R 0) h)-
    ((fderiv ℂ μ 0) h-(fderiv ℂ τ 0) h)=_
  rw [hR0,zero_mul,zero_add,hDR,hDμ,hτzero,sub_zero,
    fderiv_hillL2DirichletSlope_free_integral n hn h]
  dsimp only [J]
  rw [hBfree]
  have hn0 : (n:ℂ)≠0 := by exact_mod_cast (by omega : n≠0)
  have hpi : (Real.pi:ℂ)≠0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hs : (-1:ℂ)^n≠0 := pow_ne_zero _ (by norm_num)
  have hscalar (A : ℂ) : (I*(-1:ℂ)^n/((n:ℂ)*Real.pi))⁻¹*
      (2*((-1:ℂ)^n/((n:ℂ)*Real.pi)*A))= -2*I*A := by
    field_simp [hn0,hpi,hs]
    ring_nf
    simp only [I_sq]
    ring
  rw [hscalar]
  exact hillFreeDirichlet_fourier_pairing n h hh hm
end NLS.KdV
