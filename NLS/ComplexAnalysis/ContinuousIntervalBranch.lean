import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith

/-! # Fixing a continuous real branch between its endpoint levels -/

open Set
namespace NLS.ComplexAnalysis

theorem mem_Ioo_of_continuous_avoiding_endpoint_levels (f : ℝ → ℝ) (a b L U : ℝ)
    (hf : ContinuousOn f (Icc a b)) (ha : f a = L) (hb : f b = U) (hLU : L < U)
    (havoid : ∀ x ∈ Ioo a b, f x ≠ L ∧ f x ≠ U)
    (x : ℝ) (hx : x ∈ Ioo a b) : f x ∈ Ioo L U := by
  constructor
  · by_contra hn
    have hfx : f x < L := lt_of_le_of_ne (not_lt.mp hn) (havoid x hx).1
    obtain ⟨y, hy, he⟩ := intermediate_value_Icc hx.2.le
      (hf.mono (Icc_subset_Icc hx.1.le le_rfl))
      (show L ∈ Icc (f x) (f b) by rw [hb]; exact ⟨hfx.le, hLU.le⟩)
    have hyb : y < b := lt_of_le_of_ne hy.2 (by intro heq; rw [heq, hb] at he; exact hLU.ne he.symm)
    exact (havoid y ⟨hx.1.trans_le hy.1, hyb⟩).1 he
  · by_contra hn
    have hfx : U < f x := lt_of_le_of_ne (not_lt.mp hn) (Ne.symm (havoid x hx).2)
    obtain ⟨y, hy, he⟩ := intermediate_value_Icc hx.1.le
      (hf.mono (Icc_subset_Icc le_rfl hx.2.le))
      (show U ∈ Icc (f a) (f x) by rw [ha]; exact ⟨hLU.le, hfx.le⟩)
    have hay : a < y := lt_of_le_of_ne hy.1 (by intro heq; rw [← heq, ha] at he; exact hLU.ne he)
    exact (havoid y ⟨hay, hy.2.trans_lt hx.2⟩).2 he

end NLS.ComplexAnalysis
