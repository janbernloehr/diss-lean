import NLS.KdV.HillOwnGapFactor
import NLS.KdV.HillDirichletAnalyticLabels
import NLS.KdV.HillDeflatedGapPhysicalMatching

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV



variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

theorem exists_hillOwnGapFactor_analytic_extension (n : ℕ) (hn : 1 ≤ n) :
    ∃ F : Coeff 2 → ℂ, AnalyticAt ℂ F (SpectralWeight.one.toCoeff q) ∧
      ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
        F (SpectralWeight.one.toCoeff p.val) = hillOwnGapFactor p.val p.property.1 p.property.2 n hn := by
  let p0 : RealPeriodOneHillPotential := ⟨q,hq,hr⟩
  let P : RealPeriodOneHillPotential → Coeff 2 := fun p => SpectralWeight.one.toCoeff p.val
  have hP : Continuous P := SpectralWeight.one.toCoeff.continuous.comp continuous_subtype_val
  obtain ⟨μ,hμ,hμ0,_,hμmatch⟩ := exists_hillDirichletEnergy_analytic_extension p0 n hn
  obtain ⟨A,_,hqA,hM,_,_⟩ := exists_hillLocalGapSymmetricData_analytic_neighborhood q hq hr n hn
  have hμbase : (hillDirichletEnergy q hq hr n hn : ℂ) ∈
      segment ℝ (hillRealLabels q hq hr (2*n-1) : ℂ) (hillRealLabels q hq hr (2*n) : ℂ) :=
    ofReal_mem_ordered_segment _ _ _ (monotone_hillRealLabels q hq hr (by omega)) (hillDirichletEnergy_mem_gap q hq hr n hn)
  have hdom0 : (μ (SpectralWeight.one.toCoeff q),SpectralWeight.one.toCoeff q) ∈ hillLocalDeflatedRootDomain q hq hr n := by
    rw [hμ0]
    exact mem_hillLocalDeflatedRootDomain_base q hq hr n hn _ (hillRealGapSegment_subset_intrinsic_contour_ball q hq hr n hn hμbase)
  let B : Coeff 2 → ℂ := fun p => hillLocalDeflatedComplexRoot q hq hr n (μ p,p)
  have hB : AnalyticAt ℂ B (SpectralWeight.one.toCoeff q) :=
    (analyticOnNhd_hillLocalDeflatedComplexRoot q hq hr n hn _ hdom0).comp
      (f := fun p : Coeff 2 => (μ p,p)) (hμ.prod analyticAt_id)
  have hBn : B (SpectralWeight.one.toCoeff q) ≠ 0 := hillLocalDeflatedComplexRoot_ne_zero q hq hr n hn _ hdom0
  have hsheet : AnalyticAt ℂ (fun p : Coeff 2 => hillDirichletSheetRoot p (μ p)) (SpectralWeight.one.toCoeff q) :=
    (analyticOnNhd_hillDirichletSheetRoot_joint _ (mem_univ _)).comp
      (f := fun p : Coeff 2 => (μ p,p)) (hμ.prod analyticAt_id)
  let F : Coeff 2 → ℂ := fun p => hillLocalGapMidpoint q hq hr n p-μ p+hillDirichletSheetRoot p (μ p)/B p
  have hF : AnalyticAt ℂ F (SpectralWeight.one.toCoeff q) := ((hM _ hqA).sub hμ).add (hsheet.div hB hBn)
  refine ⟨F,hF,?_⟩
  obtain ⟨E,W,hE,hW,hgapE,hqW,hrootmatch⟩ := exists_hillLocalDeflatedComplexRoot_gap_physical_matching q hq hr n hn
  obtain ⟨T,hT,hqT,hmidmatch⟩ := exists_hillLocalGapSymmetricData_physical_neighborhood q hq hr n hn
  have hμE : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 p0, μ (P p) ∈ E := by
    have hc : ContinuousAt (fun p : RealPeriodOneHillPotential => μ (P p)) p0 :=
      ContinuousAt.comp (f := P) hμ.continuousAt hP.continuousAt
    apply hc.preimage_mem_nhds (hE.mem_nhds ?_)
    rw [hμ0]
    exact hgapE hμbase
  filter_upwards [hμmatch,hμE,hW.mem_nhds hqW,hT.mem_nhds hqT] with p hμp hpE hpW hpT
  have hroot : B (P p) = hillDeflatedEnergyCanonicalRoot p.val p.property.1 p.property.2 n (μ (P p)) :=
    (hrootmatch p hpW _ hpE).2.2
  change hillLocalGapMidpoint q hq hr n (P p)-μ (P p)+hillDirichletSheetRoot (P p) (μ (P p))/B (P p) = _
  rw [(hmidmatch p hpT).1,hroot,hμp]
  rfl

end NLS.KdV
