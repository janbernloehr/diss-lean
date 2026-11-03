import NLS.SequenceSpaces.NonzeroFiniteCenter

/-! # Finite centers retaining prescribed linear head parameters

A sufficiently close finite truncation has a smaller concentric ball
containing the original point. Prescribed head indices are retained, and
all other retained pairs can be chosen nonzero.
-/
noncomputable section
open Set Metric Filter Topology
open scoped ENNReal
namespace NLS.Coeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

omit [Fact (1 ≤ p)] in
theorem truncatePair_activeHead_union (T H : Finset ℤ) (hH : H ⊆ T) (z : Coeff p × Coeff p) :
    truncatePair (activeHead T z ∪ H) z = truncatePair T z := by
  classical
  apply Prod.ext <;> ext k
  · by_cases hk : k ∈ T
    · by_cases hx : z.1 k = 0 <;> by_cases hy : z.2 k = 0 <;>
        simp [truncatePair,activeHead,hk,hx,hy]
    · have hh : k ∉ H := fun h => hk (hH h)
      simp [truncatePair,activeHead,hk,hh]
  · by_cases hk : k ∈ T
    · by_cases hx : z.1 k = 0 <;> by_cases hy : z.2 k = 0 <;>
        simp [truncatePair,activeHead,hk,hx,hy]
    · have hh : k ∉ H := fun h => hk (hH h)
      simp [truncatePair,activeHead,hk,hh]

/-- An open neighborhood admits a head-supported center whose half-radius
ball contains the basepoint, retaining arbitrary prescribed linear head
indices while all other retained pairs are nonzero. -/
theorem exists_finiteHead_centered_ball (hp : p ≠ ⊤) (H : Finset ℤ)
    (U : Set (Coeff p × Coeff p)) (hU : IsOpen U) (z : Coeff p × Coeff p) (hz : z ∈ U) :
    ∃ S : Finset ℤ, ∃ R : ℝ, 0 < R ∧ H ⊆ S ∧ z ∈ ball (truncatePair S z) (R/2) ∧
      ball (truncatePair S z) R ⊆ U ∧ ∀ k ∈ S, k ∉ H → z.1 k ≠ 0 ∨ z.2 k ≠ 0 := by
  classical
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp hU z hz
  have ht := (tendsto_truncatePair hp z).eventually (ball_mem_nhds z (by linarith : 0 < r/8))
  obtain ⟨T,hT,hHT⟩ := (ht.and (Filter.eventually_ge_atTop H)).exists
  let S := activeHead T z ∪ H
  have hc : truncatePair S z = truncatePair T z := truncatePair_activeHead_union T H hHT z
  have hdist : dist (truncatePair S z) z < r/8 := by rw [hc]; exact hT
  refine ⟨S,r/2,by linarith,Finset.subset_union_right,?_,?_,?_⟩
  · change dist z (truncatePair S z) < (r/2)/2
    rw [dist_comm]
    linarith
  · intro w hw
    apply hball
    have hw' : dist w (truncatePair S z) < r/2 := hw
    change dist w z < r
    linarith [dist_triangle w (truncatePair S z) z]
  · intro k hk hkh
    exact (mem_activeHead T z k).mp ((Finset.mem_union.mp hk).resolve_right hkh) |>.2

end NLS.Coeff
