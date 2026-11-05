import NLS.FunctionalAnalysis.FiniteIntervalBoxFixedPoint

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal ComplexConjugate

namespace NLS.FunctionalAnalysis



theorem exists_fixed_point_countableIntervalBox
    (l u : ℕ → ℝ) (hle : ∀ j, l j ≤ u j)
    (f : countableIntervalBox l u → countableIntervalBox l u) (hf : Continuous f) :
    ∃ x : countableIntervalBox l u, f x = x := by
  choose xs hxs using (fun N => exists_finite_coordinate_fixed_point l u hle f hf N)
  have hmem (N : ℕ) : (xs N).val ∈ countableIntervalBox l u := (xs N).property
  obtain ⟨x,hx,φ,hφ,hlim⟩ := (isCompact_countableIntervalBox l u).isSeqCompact hmem
  let a : countableIntervalBox l u := ⟨x,hx⟩
  have hsub : Tendsto (xs ∘ φ) atTop (𝓝 a) := tendsto_subtype_rng.mpr hlim
  refine ⟨a,?_⟩
  apply Subtype.ext
  funext j
  have hc : Continuous (fun x : countableIntervalBox l u => (f x).val j) :=
    (continuous_apply j).comp (continuous_subtype_val.comp hf)
  have hd : Continuous (fun x : countableIntervalBox l u => x.val j) :=
    (continuous_apply j).comp continuous_subtype_val
  have hevent : ∀ᶠ N : ℕ in atTop, (f (xs (φ N))).val j = (xs (φ N)).val j := by
    filter_upwards [eventually_ge_atTop (j+1)] with N hN
    have hφN : N ≤ φ N := hφ.id_le N
    exact hxs (φ N) j (lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_succ_self j) hN) hφN)
  have hleft := (hc.tendsto a).comp hsub
  have hright := (hd.tendsto a).comp hsub
  exact tendsto_nhds_unique hleft (hright.congr' (hevent.mono fun _ h => h.symm))

end NLS.FunctionalAnalysis
