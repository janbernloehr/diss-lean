import NLS.KdV.HillDirichletAnalyticLabels
import NLS.KdV.HillLocalGapPhysicalMatching

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

/-- Centered midpoint, squared gap and Dirichlet data near any original
collapsed gap, with actual physical matching on a real neighborhood. -/
theorem exists_hillClosedGap_centered_Dirichlet_data
    (k : ℕ) (hk : 1≤k) (hgap : hillRealGapHalfLength q hq hr k=0) (r : ℝ) (hradius : 0<r) :
    ∃ δ : ℝ, ∃ μ : Coeff 2 → ℂ, ∃ V : Set RealPeriodOneHillPotential,
      0<δ ∧ IsOpen V ∧ (⟨q,hq,hr⟩ : RealPeriodOneHillPotential)∈V ∧
      (∀ p∈V, SpectralWeight.one.toCoeff p.val∈ball (SpectralWeight.one.toCoeff q) δ) ∧
      AnalyticOnNhd ℂ μ (ball (SpectralWeight.one.toCoeff q) δ) ∧
      AnalyticOnNhd ℂ (hillLocalGapMidpoint q hq hr k) (ball (SpectralWeight.one.toCoeff q) δ) ∧
      AnalyticOnNhd ℂ (fun p => hillLocalGapSquare q hq hr k p/4) (ball (SpectralWeight.one.toCoeff q) δ) ∧
      (∀ p∈ball (SpectralWeight.one.toCoeff q) δ,
        ‖hillLocalGapMidpoint q hq hr k p-(hillRealGapCenter q hq hr k : ℂ)‖<r/32 ∧
        ‖hillLocalGapSquare q hq hr k p/4‖<(r/64)^2 ∧
        ‖μ p-hillLocalGapMidpoint q hq hr k p‖<r/8 ∧ hillL2DirichletCharacteristic p (μ p)=0) ∧
      ∀ p∈V, μ (SpectralWeight.one.toCoeff p.val)=(hillDirichletEnergy p.val p.property.1 p.property.2 k hk : ℂ) ∧
        hillLocalGapMidpoint q hq hr k (SpectralWeight.one.toCoeff p.val)=(hillRealGapCenter p.val p.property.1 p.property.2 k : ℂ) ∧
        hillLocalGapSquare q hq hr k (SpectralWeight.one.toCoeff p.val)=(2*(hillRealGapHalfLength p.val p.property.1 p.property.2 k : ℂ))^2 := by
  let q0 : RealPeriodOneHillPotential := ⟨q,hq,hr⟩
  let p0 := SpectralWeight.one.toCoeff q
  let c : ℂ := hillRealGapCenter q hq hr k
  let τ := hillLocalGapMidpoint q hq hr k
  let s : Coeff 2 → ℂ := fun p => hillLocalGapSquare q hq hr k p/4
  obtain ⟨μ,hμa,hμ0,hzeros,hmatch⟩ := exists_hillDirichletEnergy_analytic_extension q0 k hk
  obtain ⟨U,hU,hqU,hτa,hSa,_⟩ := exists_hillLocalGapSymmetricData_analytic_neighborhood q hq hr k hk
  have hbase := hillLocalGapSymmetricData_eq_physical_of_geometry q hq hr q hq hr k hk
    (hillRealGapContour_band_bounds q hq hr k hk) (hillRealGapSegment_subset_intrinsic_contour_ball q hq hr k hk)
  have hτ0 : τ p0=c := hbase.1
  have hs0 : s p0=0 := by
    have hh := hbase.2
    rw [hgap] at hh
    simp only [ofReal_zero,mul_zero,zero_pow (by norm_num : (2 : ℕ)≠0)] at hh
    change hillLocalGapSquare q hq hr k p0/4=0
    rw [hh,zero_div]
  have hab : hillRealLabels q hq hr (2*k-1)=hillRealLabels q hq hr (2*k) := by
    dsimp only [hillRealGapHalfLength] at hgap
    linarith
  have hμc : hillDirichletEnergy q hq hr k hk=hillRealGapCenter q hq hr k := by
    have hh := hillDirichletEnergy_mem_gap q hq hr k hk
    dsimp only [hillRealGapCenter]
    linarith [hh.1,hh.2]
  have hμbase : μ p0=c := by change μ (SpectralWeight.one.toCoeff q)=_;rw [hμ0,hμc]
  have hτcont : ContinuousAt τ p0 := (hτa p0 hqU).continuousAt
  have hscont : ContinuousAt s p0 := ((hSa p0 hqU).div_const).continuousAt
  have hτlim : Tendsto (fun p => ‖τ p-c‖) (𝓝 p0) (𝓝 0) := by
    have hh : ContinuousAt (fun p : Coeff 2 => τ p-c) p0 := hτcont.sub continuousAt_const
    simpa only [hτ0,sub_self,norm_zero] using hh.norm.tendsto
  have hslim : Tendsto (fun p => ‖s p‖) (𝓝 p0) (𝓝 0) := by
    simpa only [hs0,norm_zero] using hscont.norm.tendsto
  have hμlim : Tendsto (fun p => ‖μ p-τ p‖) (𝓝 p0) (𝓝 0) := by
    have hh : ContinuousAt (fun p : Coeff 2 => μ p-τ p) p0 := hμa.continuousAt.sub hτcont
    simpa only [hμbase,hτ0,sub_self,norm_zero] using hh.norm.tendsto
  have hsrc : {p : Coeff 2 | AnalyticAt ℂ μ p ∧ p∈U ∧ ‖τ p-c‖<r/32 ∧
      ‖s p‖<(r/64)^2 ∧ ‖μ p-τ p‖<r/8 ∧ hillL2DirichletCharacteristic p (μ p)=0}∈𝓝 p0 := by
    filter_upwards [(isOpen_analyticAt ℂ μ).mem_nhds hμa,hU.mem_nhds hqU,
      hτlim.eventually (isOpen_Iio.mem_nhds (by positivity : (0 : ℝ)<r/32)),
      hslim.eventually (isOpen_Iio.mem_nhds (by positivity : (0 : ℝ)<(r/64)^2)),
      hμlim.eventually (isOpen_Iio.mem_nhds (by positivity : (0 : ℝ)<r/8)),hzeros] with p hpa hpU ht hs hm hz
    exact ⟨hpa,hpU,ht,hs,hm,hz⟩
  obtain ⟨δ,hδ,hδsrc⟩ := Metric.mem_nhds_iff.mp hsrc
  obtain ⟨W,hW,hqW,hphysical⟩ := exists_hillLocalGapSymmetricData_physical_neighborhood q hq hr k hk
  obtain ⟨T,hTsub,hT,hqT⟩ := _root_.mem_nhds_iff.mp hmatch
  let P : RealPeriodOneHillPotential → Coeff 2 := fun p => SpectralWeight.one.toCoeff p.val
  have hP : Continuous P := SpectralWeight.one.toCoeff.continuous.comp continuous_subtype_val
  let V := (W∩T)∩P ⁻¹' ball p0 δ
  have hV : IsOpen V := (hW.inter hT).inter (isOpen_ball.preimage hP)
  have hqV : q0∈V := by
    refine ⟨⟨hqW,hqT⟩,?_⟩
    change p0∈ball p0 δ
    exact mem_ball_self hδ
  refine ⟨δ,μ,V,hδ,hV,hqV,(fun p hp => hp.2),(fun p hp => (hδsrc hp).1),?_,?_,?_,?_⟩
  · intro p hp
    exact hτa p (hδsrc hp).2.1
  · intro p hp
    exact (hSa p (hδsrc hp).2.1).div_const
  · intro p hp
    exact (hδsrc hp).2.2
  · intro p hp
    exact ⟨hTsub hp.1.2,hphysical p hp.1.1⟩

end NLS.KdV
