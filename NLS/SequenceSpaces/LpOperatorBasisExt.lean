import NLS.SequenceSpaces.Basic

/-! Continuous linear maps on finite-exponent scalar lp over ANY index
set are determined by their literal unit coordinate vectors. -/
noncomputable section
open Filter Topology
open scoped ENNReal
namespace NLS.LpSequence

theorem continuousLinearMap_eq_of_single
    {ι E : Type*} [DecidableEq ι] {p : ℝ≥0∞} [Fact (1 ≤ p)] [NormedAddCommGroup E] [NormedSpace ℂ E]
    (hp : p ≠ ⊤) (A B : lp (fun _ : ι => ℂ) p →L[ℂ] E)
    (he : ∀ m : ι, A (lp.single p m 1) = B (lp.single p m 1)) : A = B := by
  apply ContinuousLinearMap.ext
  intro a
  have hs (m : ι) : A (lp.single p m (a m)) = B (lp.single p m (a m)) := by
    have hi : (lp.single p m (a m) : lp (fun _ : ι => ℂ) p) = a m • lp.single p m 1 := by
      ext k
      by_cases hk : k = m <;> simp [hk,lp.single_apply]
    rw [hi,map_smul,map_smul,he]
  have hfinite (s : Finset ι) : A (∑ m ∈ s, lp.single p m (a m)) = B (∑ m ∈ s, lp.single p m (a m)) := by
    rw [map_sum,map_sum]
    exact Finset.sum_congr rfl (fun m _ => hs m)
  have hA := (A.continuous.tendsto a).comp (lp.hasSum_single hp a)
  have hB := (B.continuous.tendsto a).comp (lp.hasSum_single hp a)
  exact tendsto_nhds_unique hA (hB.congr (fun s => (hfinite s).symm))

end NLS.LpSequence
