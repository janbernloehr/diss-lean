import NLS.KdV.HillOpenGapHalfLength
import NLS.KdV.HillDeflatedGapPhysicalMatching
import NLS.KdV.HillDirichletAnalyticLabels
import NLS.KdV.HillDirichletTerminalAngle

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV



variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

theorem exists_hillDirichlet_analytic_circle_data (k : ℕ) (hk : 1 ≤ k)
    (hgap : hillRealGapHalfLength q hq hr k ≠ 0) :
    ∃ d μ S : Coeff 2 → ℂ,
      AnalyticAt ℂ d (SpectralWeight.one.toCoeff q) ∧
      AnalyticAt ℂ μ (SpectralWeight.one.toCoeff q) ∧
      AnalyticAt ℂ S (SpectralWeight.one.toCoeff q) ∧
      d (SpectralWeight.one.toCoeff q) = (hillRealGapHalfLength q hq hr k : ℂ) ∧
      μ (SpectralWeight.one.toCoeff q) = (hillDirichletEnergy q hq hr k hk : ℂ) ∧
      S (SpectralWeight.one.toCoeff q) = hillDirichletGapSine q hq hr k hk ∧
      (∀ᶠ p : Coeff 2 in 𝓝 (SpectralWeight.one.toCoeff q),
        (S p)^2+((μ p-hillLocalGapMidpoint q hq hr k p)/d p)^2 = 1) ∧
      ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
        hillRealGapHalfLength p.val p.property.1 p.property.2 k ≠ 0 ∧
        d (SpectralWeight.one.toCoeff p.val) = (hillRealGapHalfLength p.val p.property.1 p.property.2 k : ℂ) ∧
        μ (SpectralWeight.one.toCoeff p.val) = (hillDirichletEnergy p.val p.property.1 p.property.2 k hk : ℂ) ∧
        S (SpectralWeight.one.toCoeff p.val) = hillDirichletGapSine p.val p.property.1 p.property.2 k hk ∧
        hillLocalGapMidpoint q hq hr k (SpectralWeight.one.toCoeff p.val) =
          (hillRealGapCenter p.val p.property.1 p.property.2 k : ℂ) := by
  let p0 : RealPeriodOneHillPotential := ⟨q,hq,hr⟩
  let P : RealPeriodOneHillPotential → Coeff 2 := fun p => SpectralWeight.one.toCoeff p.val
  have hP : Continuous P := SpectralWeight.one.toCoeff.continuous.comp continuous_subtype_val
  obtain ⟨d,hd,hd0,hdprop,hdmatch⟩ := exists_hillGapHalfLength_analytic_extension q hq hr k hk hgap
  obtain ⟨μ,hμ,hμ0,hμzero,hμmatch⟩ := exists_hillDirichletEnergy_analytic_extension p0 k hk
  have hμbase : (hillDirichletEnergy q hq hr k hk : ℂ) ∈
      segment ℝ (hillRealLabels q hq hr (2*k-1) : ℂ) (hillRealLabels q hq hr (2*k) : ℂ) :=
    ofReal_mem_ordered_segment _ _ _ (monotone_hillRealLabels q hq hr (by omega : 2*k-1 ≤ 2*k))
      (hillDirichletEnergy_mem_gap q hq hr k hk)
  have hμball := hillRealGapSegment_subset_intrinsic_contour_ball q hq hr k hk hμbase
  have hdom0 : (μ (SpectralWeight.one.toCoeff q),SpectralWeight.one.toCoeff q) ∈
      hillLocalDeflatedRootDomain q hq hr k := by
    rw [hμ0]
    exact mem_hillLocalDeflatedRootDomain_base q hq hr k hk _ hμball
  let B : Coeff 2 → ℂ := fun p => hillLocalDeflatedComplexRoot q hq hr k (μ p,p)
  have hB : AnalyticAt ℂ B (SpectralWeight.one.toCoeff q) :=
    (analyticOnNhd_hillLocalDeflatedComplexRoot q hq hr k hk _ hdom0).comp
      (f := fun p : Coeff 2 => (μ p,p)) (hμ.prod analyticAt_id)
  have hBn : B (SpectralWeight.one.toCoeff q) ≠ 0 :=
    hillLocalDeflatedComplexRoot_ne_zero q hq hr k hk _ hdom0
  let S : Coeff 2 → ℂ := fun p => I*hillDirichletSheetRoot p (μ p)/(d p*B p)
  have hS : AnalyticAt ℂ S (SpectralWeight.one.toCoeff q) := by
    have hsheet := (analyticOnNhd_hillDirichletSheetRoot_joint _ (mem_univ _)).comp
      (f := fun p : Coeff 2 => (μ p,p)) (hμ.prod analyticAt_id)
    exact (analyticAt_const.mul hsheet).div (hd.mul hB)
      (mul_ne_zero (hd0 ▸ ofReal_ne_zero.mpr hgap) hBn)
  have hS0 : S (SpectralWeight.one.toCoeff q) = hillDirichletGapSine q hq hr k hk := by
    dsimp only [S,B]
    rw [hd0,hμ0,hillLocalDeflatedComplexRoot_base q hq hr k hk _ hμball]
    rfl
  have hgraph : ContinuousAt (fun p : Coeff 2 => (μ p,p)) (SpectralWeight.one.toCoeff q) :=
    hμ.continuousAt.prodMk continuousAt_id
  have hdom : ∀ᶠ p : Coeff 2 in 𝓝 (SpectralWeight.one.toCoeff q),
      (μ p,p) ∈ hillLocalDeflatedRootDomain q hq hr k :=
    hgraph.preimage_mem_nhds ((isOpen_hillLocalDeflatedRootDomain q hq hr k hk).mem_nhds hdom0)
  obtain ⟨A,hA,hqA,hfactor⟩ := exists_hillLocalGapUnit_factorization_neighborhood q hq hr k hk
  have hcircle : ∀ᶠ p : Coeff 2 in 𝓝 (SpectralWeight.one.toCoeff q),
      (S p)^2+((μ p-hillLocalGapMidpoint q hq hr k p)/d p)^2 = 1 := by
    filter_upwards [hdprop,hμzero,hdom,hA.mem_nhds hqA] with p hdp hμp hdomp hpA
    have hBnp : B p ≠ 0 := hillLocalDeflatedComplexRoot_ne_zero q hq hr k hk _ hdomp
    have hsquare : hillDirichletSheetRoot p (μ p)^2 =
        ((μ p-hillLocalGapMidpoint q hq hr k p)^2-(d p)^2)*(B p)^2 := by
      calc
        _ = hillL2Radicand p (μ p) := hillDirichletSheetRoot_sq_of_characteristic_zero _ _ hμp
        _ = hillLocalGapPolynomial q hq hr k p (μ p)*hillLocalGapUnit q hq hr k (μ p,p) :=
          (hfactor p hpA (μ p) hdomp.1.2.1).1
        _ = _ := by
          rw [hillLocalGapPolynomial,← hdp.2]
          rw [show (B p)^2 = hillLocalGapUnit q hq hr k (μ p,p) from
            hillLocalDeflatedComplexRoot_sq q hq hr k hk _ hdomp]
    change (I*hillDirichletSheetRoot p (μ p)/(d p*B p))^2+((μ p-hillLocalGapMidpoint q hq hr k p)/d p)^2 = 1
    rw [div_pow,mul_pow,I_sq,neg_one_mul,hsquare]
    field_simp [hdp.1,hBnp]
    ring
  refine ⟨d,μ,S,hd,hμ,hS,hd0,hμ0,hS0,hcircle,?_⟩
  obtain ⟨E,W,hE,hW,hgapE,hqW,hrootmatch⟩ := exists_hillLocalDeflatedComplexRoot_gap_physical_matching q hq hr k hk
  obtain ⟨T,hT,hqT,hmidmatch⟩ := exists_hillLocalGapSymmetricData_physical_neighborhood q hq hr k hk
  have hμE : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 p0, μ (P p) ∈ E := by
    have hc : ContinuousAt (fun p : RealPeriodOneHillPotential => μ (P p)) p0 :=
      ContinuousAt.comp (f := P) hμ.continuousAt hP.continuousAt
    apply hc.preimage_mem_nhds (hE.mem_nhds ?_)
    rw [hμ0]
    exact hgapE hμbase
  filter_upwards [hdmatch,hμmatch,hμE,hW.mem_nhds hqW,hT.mem_nhds hqT,
    hP.continuousAt.tendsto.eventually hdprop] with p hdp hμp hpE hpW hpT hdpc
  have hhalfne : (hillRealGapHalfLength p.val p.property.1 p.property.2 k : ℂ) ≠ 0 := hdp ▸ hdpc.1
  refine ⟨ofReal_ne_zero.mp hhalfne,hdp,hμp,?_,(hmidmatch p hpT).1⟩
  change I*hillDirichletSheetRoot (P p) (μ (P p))/(d (P p)*B (P p)) = _
  have hroot : B (P p) = hillDeflatedEnergyCanonicalRoot p.val p.property.1 p.property.2 k (μ (P p)) :=
    (hrootmatch p hpW _ hpE).2.2
  rw [hdp,hroot,hμp]
  rfl

end NLS.KdV
