import NLS.KdV.HillDirichletAnalyticLabels
import NLS.KdV.HillLocalGapPhysicalMatching
import NLS.KdV.HillFreeGapContourGeometry

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

/-- Original midpoint, squared gap and Dirichlet energy data near a
fixed free collapsed gap, on one common complex and real source ball. -/
theorem exists_hillFixedGap_centered_Dirichlet_data (k : ℕ) (hk : 1≤k) (r : ℝ) (hr : 0<r) :
    ∃ δ : ℝ, ∃ μ : Coeff 2 → ℂ, 0<δ ∧
      AnalyticOnNhd ℂ μ (ball 0 δ) ∧
      AnalyticOnNhd ℂ (hillLocalGapMidpoint 0 h0q h0r k) (ball 0 δ) ∧
      AnalyticOnNhd ℂ (fun p => hillLocalGapSquare 0 h0q h0r k p/4) (ball 0 δ) ∧
      (∀ p∈ball 0 δ,
        ‖hillLocalGapMidpoint 0 h0q h0r k p-(hillRealGapCenter 0 h0q h0r k : ℂ)‖<r/32 ∧
        ‖hillLocalGapSquare 0 h0q h0r k p/4‖<(r/64)^2 ∧
        ‖μ p-hillLocalGapMidpoint 0 h0q h0r k p‖<r/8 ∧
        hillL2DirichletCharacteristic p (μ p)=0) ∧
      ∀ q : RealPeriodOneHillPotential, ‖q.val‖<δ →
        μ (SpectralWeight.one.toCoeff q.val)=(hillDirichletEnergy q.val q.property.1 q.property.2 k hk : ℂ) ∧
        hillLocalGapMidpoint 0 h0q h0r k (SpectralWeight.one.toCoeff q.val)=
          (hillRealGapCenter q.val q.property.1 q.property.2 k : ℂ) ∧
        hillLocalGapSquare 0 h0q h0r k (SpectralWeight.one.toCoeff q.val)=
          (2*(hillRealGapHalfLength q.val q.property.1 q.property.2 k : ℂ))^2 := by
  let q0 : RealPeriodOneHillPotential := ⟨0,h0q,h0r⟩
  let c : ℂ := hillRealGapCenter 0 h0q h0r k
  let τ := hillLocalGapMidpoint 0 h0q h0r k
  let s : Coeff 2 → ℂ := fun p => hillLocalGapSquare 0 h0q h0r k p/4
  obtain ⟨μ,hμa,hμ0,hzeros,hmatch⟩ := exists_hillDirichletEnergy_analytic_extension q0 k hk
  simp only [q0,map_zero] at hμa hμ0 hzeros
  obtain ⟨V,hV,h0V,hτa,hSa,_⟩ := exists_hillLocalGapSymmetricData_analytic_neighborhood 0 h0q h0r k hk
  have h0V' : (0 : Coeff 2)∈V := by simpa only [map_zero] using h0V
  have hbase := hillLocalGapSymmetricData_eq_physical_of_geometry 0 h0q h0r 0 h0q h0r k hk
    (hillRealGapContour_band_bounds 0 h0q h0r k hk) (hillRealGapSegment_subset_intrinsic_contour_ball 0 h0q h0r k hk)
  have hτ0 : τ 0=c := by simpa only [map_zero] using hbase.1
  have hs0 : s 0=0 := by
    have hh := hbase.2
    rw [map_zero,hillFreeGapHalfLength h0q h0r k hk] at hh
    simp only [ofReal_zero,mul_zero,zero_pow (by norm_num : (2:ℕ)≠0)] at hh
    change hillLocalGapSquare 0 h0q h0r k 0/4=0
    rw [hh,zero_div]
  have hfreeμ : hillDirichletEnergy 0 h0q h0r k hk=freeHillValue k := by
    have hh := hillDirichletEnergy_mem_gap 0 h0q h0r k hk
    rw [(hillFreeGapEndpoints h0q h0r k hk).1,(hillFreeGapEndpoints h0q h0r k hk).2] at hh
    exact le_antisymm hh.2 hh.1
  have hμbase : μ (0 : Coeff 2)=c := by
    rw [hfreeμ] at hμ0
    simpa only [c,hillFreeGapCenter h0q h0r k hk] using hμ0
  have hτcont : ContinuousAt τ (0 : Coeff 2) := (hτa 0 h0V').continuousAt
  have hscont : ContinuousAt s (0 : Coeff 2) := ((hSa 0 h0V').div_const).continuousAt
  have hτlim : Tendsto (fun p => ‖τ p-c‖) (𝓝 (0 : Coeff 2)) (𝓝 0) := by
    have hh : ContinuousAt (fun p : Coeff 2 => τ p-c) 0 := hτcont.sub continuousAt_const
    simpa only [hτ0,sub_self,norm_zero] using hh.norm.tendsto
  have hslim : Tendsto (fun p => ‖s p‖) (𝓝 (0 : Coeff 2)) (𝓝 0) := by
    simpa only [hs0,norm_zero] using hscont.norm.tendsto
  have hμlim : Tendsto (fun p => ‖μ p-τ p‖) (𝓝 (0 : Coeff 2)) (𝓝 0) := by
    have hh : ContinuousAt (fun p : Coeff 2 => μ p-τ p) 0 := hμa.continuousAt.sub hτcont
    simpa only [hμbase,hτ0,sub_self,norm_zero] using hh.norm.tendsto
  have hsource : {p : Coeff 2 | AnalyticAt ℂ μ p ∧ p∈V ∧ ‖τ p-c‖<r/32 ∧
      ‖s p‖<(r/64)^2 ∧ ‖μ p-τ p‖<r/8 ∧ hillL2DirichletCharacteristic p (μ p)=0}∈𝓝 (0 : Coeff 2) := by
    filter_upwards [(isOpen_analyticAt ℂ μ).mem_nhds hμa,hV.mem_nhds h0V',
      hτlim.eventually (isOpen_Iio.mem_nhds (by positivity : (0:ℝ)<r/32)),
      hslim.eventually (isOpen_Iio.mem_nhds (by positivity : (0:ℝ)<(r/64)^2)),
      hμlim.eventually (isOpen_Iio.mem_nhds (by positivity : (0:ℝ)<r/8)),hzeros] with p hpa hpV ht hs hm hz
    exact ⟨hpa,hpV,ht,hs,hm,hz⟩
  obtain ⟨ε,hε,hεsource⟩ := Metric.mem_nhds_iff.mp hsource
  obtain ⟨W,hW,h0W,hphysical⟩ := exists_hillLocalGapSymmetricData_physical_neighborhood 0 h0q h0r k hk
  have hreal : {q : RealPeriodOneHillPotential | μ (SpectralWeight.one.toCoeff q.val)=
      (hillDirichletEnergy q.val q.property.1 q.property.2 k hk : ℂ) ∧
      τ (SpectralWeight.one.toCoeff q.val)=(hillRealGapCenter q.val q.property.1 q.property.2 k : ℂ) ∧
      hillLocalGapSquare 0 h0q h0r k (SpectralWeight.one.toCoeff q.val)=
        (2*(hillRealGapHalfLength q.val q.property.1 q.property.2 k : ℂ))^2}∈𝓝 q0 := by
    filter_upwards [hmatch,hW.mem_nhds h0W] with q hm hqW
    exact ⟨hm,hphysical q hqW⟩
  obtain ⟨εr,hεr,hεreal⟩ := Metric.mem_nhds_iff.mp hreal
  let δ := min ε εr
  have hδ : 0<δ := lt_min hε hεr
  have hsrc (p : Coeff 2) (hp : p∈ball 0 δ) := hεsource (ball_subset_ball (min_le_left _ _) hp)
  refine ⟨δ,μ,hδ,(fun p hp => (hsrc p hp).1),?_,?_,?_,?_⟩
  · intro p hp
    exact hτa p (hsrc p hp).2.1
  · intro p hp
    exact (hSa p (hsrc p hp).2.1).div_const
  · intro p hp
    exact (hsrc p hp).2.2
  · intro q hq
    apply hεreal
    rw [mem_ball]
    change dist q.val (0 : WeightedCoeff SpectralWeight.one.toWeight 2)<εr
    rw [dist_zero_right]
    exact hq.trans_le (min_le_right _ _)

end NLS.KdV
