import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-! # Continuity of a series from finite sums and locally small tails

Coordinate continuity and a small summed tail on a neighborhood suffice
for continuity of the total series. The neighborhood and cutoff may depend
on the tolerance, without one global summable majorant.
-/

noncomputable section
open Filter Topology Metric
namespace NLS

theorem continuousAt_tsum_of_locally_small_nat_tails
    {X E : Type*} [TopologicalSpace X] [NormedAddCommGroup E]
    (f : X → ℕ → E) (x : X)
    (hs : ∀ y, Summable (f y))
    (hc : ∀ n, ContinuousAt (fun y => f y n) x)
    (ht : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ,
      ∀ᶠ y in 𝓝 x, ‖∑' k : ℕ, f y (k+N)‖ ≤ ε) :
    ContinuousAt (fun y => ∑' k : ℕ, f y k) x := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨N, htail⟩ := ht (ε/4) (by positivity)
  have hx : ‖∑' k : ℕ, f x (k+N)‖ ≤ ε/4 := htail.self_of_nhds
  have hfin : ContinuousAt (fun y => ∑ k ∈ Finset.range N, f y k) x := by
    clear htail hx
    induction N with
    | zero => simpa using (continuousAt_const : ContinuousAt (fun _ : X => (0 : E)) x)
    | succ M ih =>
      simp only [Finset.sum_range_succ]
      exact ih.add (hc M)
  have hnear : ∀ᶠ y in 𝓝 x,
      dist (∑ k ∈ Finset.range N, f y k) (∑ k ∈ Finset.range N, f x k) < ε/2 :=
    hfin.eventually (Metric.ball_mem_nhds _ (by positivity))
  filter_upwards [htail, hnear] with y hy hn
  rw [dist_eq_norm] at hn ⊢
  rw [← (hs y).sum_add_tsum_nat_add N, ← (hs x).sum_add_tsum_nat_add N]
  have he : (∑ k ∈ Finset.range N, f y k) + (∑' k : ℕ, f y (k+N)) -
      ((∑ k ∈ Finset.range N, f x k) + (∑' k : ℕ, f x (k+N))) =
      ((∑ k ∈ Finset.range N, f y k) - (∑ k ∈ Finset.range N, f x k)) +
        (∑' k : ℕ, f y (k+N)) - (∑' k : ℕ, f x (k+N)) := by abel
  rw [he]
  have htri := norm_sub_le (((∑ k ∈ Finset.range N, f y k) -
    (∑ k ∈ Finset.range N, f x k)) + (∑' k : ℕ, f y (k+N))) (∑' k : ℕ, f x (k+N))
  have htri' := norm_add_le ((∑ k ∈ Finset.range N, f y k) -
    (∑ k ∈ Finset.range N, f x k)) (∑' k : ℕ, f y (k+N))
  linarith

theorem exists_local_nat_property_pullback
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (m : ℕ) (f : X → Y) (hf : Continuous f) (P : Y → ℕ → Prop) (Q : X → ℕ → Prop)
    (he : ∀ x n, Q x n = P (f x) n) (x : X)
    (h : ∃ N : ℕ, ∃ V : Set Y, m ≤ N ∧ IsOpen V ∧ f x ∈ V ∧
      ∀ y ∈ V, ∀ n : ℕ, N ≤ n → P y n) :
    ∃ N : ℕ, ∃ U : Set X, m ≤ N ∧ IsOpen U ∧ x ∈ U ∧
      ∀ y ∈ U, ∀ n : ℕ, N ≤ n → Q y n := by
  obtain ⟨N, V, hN, hV, hx, hbound⟩ := h
  refine ⟨N, f ⁻¹' V, hN, hV.preimage hf, hx, ?_⟩
  intro y hy n hn
  rw [he]
  exact hbound (f y) hy n hn

end NLS
