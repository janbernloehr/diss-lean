import NLS.ZakharovShabat.SourceConstantCentralPair
import NLS.ZakharovShabat.SourceAbelianPrimitiveProperties

/-! # The filled fixed-source primitive domain is not a source neighborhood

At the free collapsed central gap, lambda=0 is in the filled spectral domain.
Arbitrarily small diagonal constant sources put that same lambda inside an
open cut. The filled fixed-source domain therefore cannot be silently used
as an open source domain for an ordinary Frechet gradient.
-/
noncomputable section
open Set Complex Metric Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem source_filled_primitive_zero_slice_not_nhds (hp : p ≠ ⊤) (hp1 : 1 < p) :
    {φ : CoeffPair p | (0:ℂ) ∈ sourceOpenGapComplement hp hp1 φ} ∉ 𝓝 (0 : CoeffPair p) := by
  intro hN
  obtain ⟨ε,hε,U,hU,h0,hpair⟩ := exists_sourceConstant_central_pair_neighborhood hp hp1
  let f : ℝ → CoeffPair p := fun r => sourceConstantPotential (p := p) (r:ℂ) (r:ℂ)
  have hf : Continuous f := by
    change Continuous ((fun v : ℂ × ℂ => sourceConstantPotential (p := p) v.1 v.2) ∘
      (fun r : ℝ => ((r:ℂ),(r:ℂ))))
    apply (continuous_sourceConstantPotential (p := p)).comp
    exact Complex.continuous_ofReal.prodMk Complex.continuous_ofReal
  have hf0 : f 0 = 0 := by
    simp only [f,Complex.ofReal_zero]
    rw [← sourceConstantPotentialCLM_apply]
    exact map_zero (sourceConstantPotentialCLM (p := p))
  have hUN : U ∩ {φ : CoeffPair p | (0:ℂ) ∈ sourceOpenGapComplement hp hp1 φ} ∈ 𝓝 (f 0) := by
    rw [hf0]
    exact inter_mem (hU.mem_nhds h0) hN
  obtain ⟨δ,hδ,hδsub⟩ := Metric.mem_nhds_iff.mp (hf.continuousAt.preimage_mem_nhds hUN)
  let r : ℝ := min δ ε/2
  have hr : 0 < r := by dsimp [r]; positivity
  have hrδ : r < δ := by have := min_le_left δ ε; dsimp [r]; linarith
  have hrε : r < ε := by have := min_le_right δ ε; dsimp [r]; linarith
  have hbase : f r ∈ U ∩ {φ : CoeffPair p | (0:ℂ) ∈ sourceOpenGapComplement hp hp1 φ} :=
    hδsub (by simpa [mem_ball,Real.dist_eq,abs_of_pos hr] using hrδ)
  have hr' : (r:ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  obtain ⟨hl,hR⟩ := hpair (r:ℂ) (r:ℂ) (r:ℂ) hr' hr' (by ring) hbase.1
    (by simpa [norm_real,Real.norm_eq_abs,abs_of_pos hr] using hrε)
  have hgap : canonicalPeriodicGap hp hp1 (periodOnePotential (f r)) (periodOnePotential_mem _) 0 ≠ 0 := by
    intro he
    dsimp only [f] at he
    unfold canonicalPeriodicGap at he
    rw [hl,hR] at he
    unfold orderedEndpointLeft orderedEndpointRight at he
    split_ifs at he <;> have hh := congrArg Complex.re he <;> simp at hh <;> linarith
  have hseg : (0:ℂ) ∈ sourcePeriodicSegment hp hp1 (f r) 0 := by
    dsimp only [sourcePeriodicSegment,f]
    rw [hl,hR]
    unfold orderedEndpointLeft orderedEndpointRight
    split_ifs
    · simpa using midpoint_mem_segment (𝕜 := ℝ) (r:ℂ) (-(r:ℂ))
    · simpa using midpoint_mem_segment (𝕜 := ℝ) (-(r:ℂ)) (r:ℂ)
  exact hbase.2 0 hgap hseg

theorem source_filled_primitive_zero_slice_contains_zero (hp : p ≠ ⊤) (hp1 : 1 < p) :
    (0:ℂ) ∈ sourceOpenGapComplement hp hp1 (0 : CoeffPair p) := by simp

end NLS.ZakharovShabat
