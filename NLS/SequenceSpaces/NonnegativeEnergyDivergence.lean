import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! # Divergence forced by nonsummable coordinatewise limits

A finite partial sum of a nonnegative nonsummable limiting energy can be
made arbitrarily large. Coordinatewise convergence then transfers that
bound to any approximating total energies dominating their partial sums.
-/

noncomputable section
set_option autoImplicit false
open Filter Topology
namespace NLS

theorem tendsto_atTop_of_nonsummable_coordinate_limit
    {α ι : Type*} {l : Filter ι} (f : α → ℝ) (hf : ∀ n, 0 ≤ f n)
    (hnot : ¬ Summable f) (g : ι → α → ℝ) (energy : ι → ℝ)
    (hlim : ∀ n, Tendsto (fun i => g i n) l (𝓝 (f n)))
    (hbound : ∀ i (S : Finset α), ∑ n ∈ S, g i n ≤ energy i) :
    Tendsto energy l atTop := by
  apply tendsto_atTop.mpr
  intro b
  have hex : ∃ S : Finset α, b < ∑ n ∈ S, f n := by
    by_contra h
    push Not at h
    exact hnot (summable_of_sum_le hf h)
  obtain ⟨S, hS⟩ := hex
  have hsum := tendsto_finsetSum S (fun n _ => hlim n)
  filter_upwards [hsum.eventually (lt_mem_nhds hS)] with i hi
  exact hi.le.trans (hbound i S)

end NLS
