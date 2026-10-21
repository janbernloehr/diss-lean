import NLS.ZakharovShabat.SourceConstantCentralPair

noncomputable section
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A continuous original-source curve whose two central roots cross a vertical line. -/
def sourceConstantCrossing (r time : ℝ) : CoeffPair p :=
  sourceConstantPotential (r : ℂ) (((time : ℂ)+I*r)^2/(r : ℂ))

theorem continuous_sourceConstantCrossing (r : ℝ) :
    Continuous (sourceConstantCrossing (p := p) r) := by
  change Continuous ((fun v : ℂ × ℂ => sourceConstantPotential (p := p) v.1 v.2) ∘
    (fun time : ℝ => ((r : ℂ), ((time : ℂ)+I*r)^2/(r : ℂ))))
  apply (continuous_sourceConstantPotential (p := p)).comp
  exact continuous_const.prodMk
    ((Complex.continuous_ofReal.add continuous_const).pow 2 |>.div_const _)

theorem sourceConstantCrossing_zero (r : ℝ) (hr : r ≠ 0) :
    sourceConstantCrossing (p := p) r 0 = sourceConstantPotential (r : ℂ) (-r) := by
  unfold sourceConstantCrossing
  congr 1
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  field_simp
  simp [mul_pow, I_sq]

/-- On the negative side, lexicographic order selects the upper root first. -/
theorem orderedEndpoint_vertical_crossing_neg (r time : ℝ) (ht : time < 0) :
    orderedEndpointLeft ((time : ℂ)+I*r) (-((time : ℂ)+I*r)) = (time : ℂ)+I*r ∧
    orderedEndpointRight ((time : ℂ)+I*r) (-((time : ℂ)+I*r)) = -((time : ℂ)+I*r) := by
  have h : complexLexLE ((time : ℂ)+I*r) (-((time : ℂ)+I*r)) := by
    apply complexLexLE_of_re_lt
    simp
    linarith
  simp only [orderedEndpointLeft, orderedEndpointRight, if_pos h, and_self]

/-- At the vertical pair, the imaginary part reverses the selected order. -/
theorem orderedEndpoint_vertical_crossing_zero (r : ℝ) (hr : 0 < r) :
    orderedEndpointLeft (I*r) (-(I*r)) = -(I*r) ∧
    orderedEndpointRight (I*r) (-(I*r)) = I*r := by
  have h : ¬complexLexLE (I*r) (-(I*r)) := by
    simp [complexLexLE_iff]
    linarith
  simp only [orderedEndpointLeft, orderedEndpointRight, if_neg h, and_self]

set_option maxHeartbeats 800000 in
/-- Both actual canonical central endpoint labels are discontinuous at some arbitrarily small
constant complex source. The witness may be chosen inside any neighborhood of zero. -/
theorem exists_sourcePeriodicLabels_not_continuousAt (hp : p ≠ ⊤) (hp1 : 1 < p)
    (V : Set (CoeffPair p)) (hV : V ∈ 𝓝 (0 : CoeffPair p)) :
    ∃ r : ℝ, 0 < r ∧ sourceConstantPotential (p := p) (r : ℂ) (-r) ∈ V ∧
      ¬ContinuousAt (fun ψ : CoeffPair p =>
        canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) 0)
        (sourceConstantPotential (p := p) (r : ℂ) (-r)) ∧
      ¬ContinuousAt (fun ψ : CoeffPair p =>
        canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) 0)
        (sourceConstantPotential (p := p) (r : ℂ) (-r)) := by
  obtain ⟨ε,hε,U,hU,h0,hpair⟩ := exists_sourceConstant_central_pair_neighborhood hp hp1
  let f : ℝ → CoeffPair p := fun r => sourceConstantPotential (p := p) (r : ℂ) (-r)
  have hf : Continuous f := by
    change Continuous ((fun v : ℂ × ℂ => sourceConstantPotential (p := p) v.1 v.2) ∘
      (fun r : ℝ => ((r : ℂ), -(r : ℂ))))
    apply (continuous_sourceConstantPotential (p := p)).comp
    exact Complex.continuous_ofReal.prodMk Complex.continuous_ofReal.neg
  have hf0 : f 0 = 0 := by
    simp only [f, Complex.ofReal_zero, neg_zero]
    rw [←sourceConstantPotentialCLM_apply]
    exact map_zero (sourceConstantPotentialCLM (p := p))
  have hUV : U ∩ V ∈ 𝓝 (f 0) := by
    rw [hf0]
    exact inter_mem (hU.mem_nhds h0) hV
  obtain ⟨δ,hδ,hδsub⟩ := Metric.mem_nhds_iff.mp (hf.continuousAt.preimage_mem_nhds hUV)
  let r : ℝ := min δ ε / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hrδ : r < δ := by have := min_le_left δ ε; dsimp [r]; linarith
  have hrε : r < ε := by have := min_le_right δ ε; dsimp [r]; linarith
  have hbase : f r ∈ U ∩ V := hδsub (by simpa [mem_ball, Real.dist_eq, abs_of_pos hr] using hrδ)
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  let ζ : ℝ → ℂ := fun time => (time : ℂ)+I*r
  let γ : ℝ → CoeffPair p := sourceConstantCrossing (p := p) r
  let L : CoeffPair p → ℂ := fun ψ =>
    canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) 0
  let R : CoeffPair p → ℂ := fun ψ =>
    canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) 0
  have hζ : Continuous ζ := Complex.continuous_ofReal.add continuous_const
  have hγ : Continuous γ := continuous_sourceConstantCrossing (p := p) r
  have hγ0 : γ 0 = f r := sourceConstantCrossing_zero (p := p) r hr.ne'
  have hz0 : ζ 0 = I*r := by simp [ζ]
  have hnorm0 : ‖ζ 0‖ < ε := by simpa [ζ, norm_mul, abs_of_pos hr] using hrε
  have hsource : ∀ᶠ time in 𝓝 (0 : ℝ), γ time ∈ U :=
    hγ.continuousAt.preimage_mem_nhds (hU.mem_nhds (hγ0.symm ▸ hbase.1))
  have hnorm : ∀ᶠ time in 𝓝 (0 : ℝ), ‖ζ time‖ < ε :=
    (isOpen_lt hζ.norm continuous_const).mem_nhds hnorm0
  have hlabels : ∀ᶠ time in 𝓝 (0 : ℝ),
      L (γ time) = orderedEndpointLeft (ζ time) (-(ζ time)) ∧
      R (γ time) = orderedEndpointRight (ζ time) (-(ζ time)) := by
    filter_upwards [hsource,hnorm] with time ht hn
    apply hpair (r : ℂ) ((ζ time)^2/(r : ℂ)) (ζ time) hr' _ _ ht hn
    · intro he
      have hi := congrArg Complex.im he
      simp [ζ] at hi
      linarith
    · field_simp
  have hnegative : ∀ᶠ time in 𝓝[<] (0 : ℝ),
      L (γ time) = ζ time ∧ R (γ time) = -(ζ time) := by
    filter_upwards [hlabels.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with time ht hn
    have ho := orderedEndpoint_vertical_crossing_neg r time hn
    exact ⟨ht.1.trans ho.1, ht.2.trans ho.2⟩
  have hvalue : L (γ 0) = -(I*r) ∧ R (γ 0) = I*r := by
    have hh := hlabels.self_of_nhds
    rw [hz0] at hh
    have ho := orderedEndpoint_vertical_crossing_zero r hr
    exact ⟨hh.1.trans ho.1,hh.2.trans ho.2⟩
  have hlimL : Tendsto (fun time => L (γ time)) (𝓝[<] (0 : ℝ)) (𝓝 (I*r)) := by
    have ht : Tendsto ζ (𝓝[<] (0 : ℝ)) (𝓝 (I*r)) := by
      simpa only [hz0] using (hζ.continuousAt (x := 0)).tendsto.mono_left
        (nhdsWithin_le_nhds (s := Iio (0 : ℝ)))
    exact ht.congr' (hnegative.mono (fun _ h => h.1.symm))
  have hlimR : Tendsto (fun time => R (γ time)) (𝓝[<] (0 : ℝ)) (𝓝 (-(I*r))) := by
    have ht : Tendsto (fun time => -(ζ time)) (𝓝[<] (0 : ℝ)) (𝓝 (-(I*r))) := by
      simpa only [Pi.neg_apply, hz0] using! (hζ.neg.continuousAt (x := 0)).tendsto.mono_left
        (nhdsWithin_le_nhds (s := Iio (0 : ℝ)))
    exact ht.congr' (hnegative.mono (fun _ h => h.2.symm))
  refine ⟨r,hr,hbase.2,?_,?_⟩
  · intro hc
    have hc' : ContinuousAt L (γ 0) := by simpa only [hγ0] using hc
    have he := tendsto_nhds_unique ((hc'.comp hγ.continuousAt).tendsto.mono_left
      (nhdsWithin_le_nhds (s := Iio (0 : ℝ)))) hlimL
    rw [Function.comp_apply, hvalue.1] at he
    have hi := congrArg Complex.im he
    simp at hi
    linarith
  · intro hc
    have hc' : ContinuousAt R (γ 0) := by simpa only [hγ0] using hc
    have he := tendsto_nhds_unique ((hc'.comp hγ.continuousAt).tendsto.mono_left
      (nhdsWithin_le_nhds (s := Iio (0 : ℝ)))) hlimR
    rw [Function.comp_apply, hvalue.2] at he
    have hi := congrArg Complex.im he
    simp at hi
    linarith

end NLS.ZakharovShabat
