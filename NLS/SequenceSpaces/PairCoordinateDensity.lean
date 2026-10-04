import NLS.SequenceSpaces.TailSquareDescentCoordinateAnalytic

/-! # Removing two nonvanishing-coordinate restrictions by continuity

Perturb both selected entries by a common scalar. On a punctured
neighborhood of zero both are eventually nonzero, even if either entry
originally vanishes. This lets a continuous identity extend to zero modes.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.Coeff
variable {q : ℝ≥0∞} [Fact (1 ≤ q)]
variable {F : Type*} [TopologicalSpace F] [T2Space F]

/-- An identity valid when both selected entries are nonzero extends to
the entire open sequence-pair domain by continuity. -/
theorem eq_const_of_pair_coordinate_ne
    (g : (Coeff q × Coeff q) → F) (U : Set (Coeff q × Coeff q))
    (hU : IsOpen U) (hg : ContinuousOn g U) (k : ℤ) (c : F)
    (he : ∀ b ∈ U, b.1 k ≠ 0 → b.2 k ≠ 0 → g b = c)
    (b : Coeff q × Coeff q) (hb : b ∈ U) : g b = c := by
  let γ : ℂ → Coeff q × Coeff q := fun t => b+pairSingleCLM q false k t+pairSingleCLM q true k t
  have hγ0 : γ 0 = b := by simp [γ]
  have hγ : Tendsto γ (𝓝[≠] (0 : ℂ)) (𝓝 b) := by
    have hc : Continuous γ := by dsimp [γ]; fun_prop
    simpa only [hγ0] using (hc.tendsto (0 : ℂ)).mono_left nhdsWithin_le_nhds
  have hcoord (a : ℂ) : ∀ᶠ t : ℂ in 𝓝[≠] 0, a+t ≠ 0 := by
    by_cases ha : a = 0
    · subst a
      filter_upwards [self_mem_nhdsWithin] with t ht
      simpa only [zero_add,Set.mem_compl_iff,Set.mem_singleton_iff] using ht
    · have ht : Tendsto (fun t : ℂ => a+t) (𝓝[≠] 0) (𝓝 a) := by
        have hc : Continuous (fun t : ℂ => a+t) := continuous_const.add continuous_id
        simpa only [add_zero] using (hc.tendsto (0 : ℂ)).mono_left nhdsWithin_le_nhds
      exact ht (isOpen_ne.mem_nhds ha)
  have hstay : ∀ᶠ t in 𝓝[≠] (0 : ℂ), γ t ∈ U := hγ (hU.mem_nhds hb)
  have hevent : ∀ᶠ t in 𝓝[≠] (0 : ℂ), g (γ t) = c := by
    filter_upwards [hstay,hcoord (b.1 k),hcoord (b.2 k)] with t ht h1 h2
    apply he (γ t) ht
    · simpa [γ,pairSingleCLM,lp.single_apply] using h1
    · simpa [γ,pairSingleCLM,lp.single_apply] using h2
  have hlim := ((hg b hb).continuousAt (hU.mem_nhds hb)).tendsto.comp hγ
  exact tendsto_nhds_unique hlim (tendsto_nhds_of_eventually_eq hevent)

end NLS.Coeff
