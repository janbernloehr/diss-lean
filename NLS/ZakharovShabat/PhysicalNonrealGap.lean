import NLS.ZakharovShabat.PhysicalPeriodicMidpointGap
import NLS.ZakharovShabat.SourcePeriodicLabelDiscontinuity

/-! # Nonreal physical gaps arbitrarily close to the zero potential -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Every physical L2 neighborhood of zero contains a constant potential
whose actual central endpoints are the distinct imaginary pair (-ir,ir). -/
theorem exists_physical_nonreal_central_pair (V : Set IntervalPairL2)
    (hV : V ∈ 𝓝 (0 : IntervalPairL2)) :
    ∃ r : ℝ, 0 < r ∧ sourcePhysicalL2 (sourceConstantPotential (p := 2) (r : ℂ) (-r)) ∈ V ∧
      physicalPeriodicLeft (sourcePhysicalL2 (sourceConstantPotential (p := 2) (r : ℂ) (-r))) 0 = -(I*r) ∧
      physicalPeriodicRight (sourcePhysicalL2 (sourceConstantPotential (p := 2) (r : ℂ) (-r))) 0 = I*r := by
  obtain ⟨ε,hε,U,hU,h0,hpair⟩ :=
    exists_sourceConstant_central_pair_neighborhood (p := 2) (by simp) (by norm_num)
  let f : ℝ → CoeffPair 2 := fun r => sourceConstantPotential (r : ℂ) (-r)
  have hf : Continuous f := by
    change Continuous ((fun v : ℂ × ℂ => sourceConstantPotential (p := 2) v.1 v.2) ∘
      (fun r : ℝ => ((r : ℂ), -(r : ℂ))))
    exact continuous_sourceConstantPotential.comp
      (Complex.continuous_ofReal.prodMk Complex.continuous_ofReal.neg)
  have hf0 : f 0 = 0 := by
    simp only [f,Complex.ofReal_zero,neg_zero]
    rw [← sourceConstantPotentialCLM_apply]
    exact map_zero (sourceConstantPotentialCLM (p := 2))
  have hV' : sourcePhysicalL2Equiv ⁻¹' V ∈ 𝓝 (0 : CoeffPair 2) := by
    apply sourcePhysicalL2Equiv.continuous.continuousAt.preimage_mem_nhds
    simpa only [map_zero] using hV
  have hUV : U ∩ sourcePhysicalL2Equiv ⁻¹' V ∈ 𝓝 (f 0) := by
    rw [hf0]
    exact inter_mem (hU.mem_nhds h0) hV'
  obtain ⟨δ,hδ,hδsub⟩ := Metric.mem_nhds_iff.mp (hf.continuousAt.preimage_mem_nhds hUV)
  let r : ℝ := min δ ε/2
  have hr : 0 < r := by dsimp [r]; positivity
  have hrδ : r < δ := by have := min_le_left δ ε; dsimp [r]; linarith
  have hrε : r < ε := by have := min_le_right δ ε; dsimp [r]; linarith
  have hbase : f r ∈ U ∩ sourcePhysicalL2Equiv ⁻¹' V :=
    hδsub (by simpa [mem_ball,Real.dist_eq,abs_of_pos hr] using hrδ)
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hz : I*(r : ℂ) ≠ 0 := mul_ne_zero I_ne_zero hr'
  have hsq : (I*(r : ℂ))^2 = (r : ℂ)*(-r) := by
    simp [mul_pow,I_sq]
    ring
  have hn : ‖I*(r : ℂ)‖ < ε := by simpa [norm_mul,abs_of_pos hr] using hrε
  have hp := hpair (r : ℂ) (-r) (I*r) hr' hz hsq hbase.1 hn
  have ho := orderedEndpoint_vertical_crossing_zero r hr
  refine ⟨r,hr,?_,?_,?_⟩
  · simpa only [mem_preimage,sourcePhysicalL2Equiv_apply] using hbase.2
  · rw [(physicalPeriodicEndpoints_eq_source _).1]
    simp only [← sourcePhysicalL2Equiv_apply,LinearIsometryEquiv.symm_apply_apply]
    exact hp.1.trans ho.1
  · rw [(physicalPeriodicEndpoints_eq_source _).2]
    simp only [← sourcePhysicalL2Equiv_apply,LinearIsometryEquiv.symm_apply_apply]
    exact hp.2.trans ho.2

/-- The printed complex-gap assertion has actual physical witnesses in every
neighborhood of zero; the gap equals 2ir and its midpoint is zero. -/
theorem exists_physical_nonreal_gap (V : Set IntervalPairL2)
    (hV : V ∈ 𝓝 (0 : IntervalPairL2)) :
    ∃ u ∈ V, ∃ r : ℝ, 0 < r ∧ physicalPeriodicGap u 0 = 2*I*r ∧
      physicalPeriodicMidpoint u 0 = 0 ∧ (physicalPeriodicGap u 0).im ≠ 0 := by
  obtain ⟨r,hr,hv,hl,hrr⟩ := exists_physical_nonreal_central_pair V hV
  refine ⟨_,hv,r,hr,?_,?_,?_⟩
  · rw [physicalPeriodicGap,hl,hrr]
    ring
  · rw [physicalPeriodicMidpoint,hl,hrr]
    ring
  · rw [physicalPeriodicGap,hl,hrr]
    simp
    linarith

end NLS.ZakharovShabat
