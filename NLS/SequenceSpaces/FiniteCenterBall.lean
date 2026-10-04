import NLS.SequenceSpaces.SignChange

/-! # Complex neighborhoods centered on finite coordinate blocks

Every neighborhood of a finite-exponent sequence pair contains a ball
centered on a finite truncation and containing the original point. All
sign changes outside that finite block preserve the ball.
-/
noncomputable section
open Set Metric Filter Topology
open scoped ENNReal
namespace NLS.Coeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Truncate both complex coordinate sequences at the same finite block. -/
def truncatePair (S : Finset ℤ) (z : Coeff p × Coeff p) : Coeff p × Coeff p :=
  (truncate S z.1,truncate S z.2)

theorem tendsto_truncatePair (hp : p ≠ ⊤) (z : Coeff p × Coeff p) :
    Tendsto (fun S : Finset ℤ => truncatePair S z) atTop (𝓝 z) :=
  (tendsto_truncate hp z.1).prodMk_nhds (tendsto_truncate hp z.2)

omit [Fact (1 ≤ p)] in
theorem truncatePair_mem_realPairLocus (S : Finset ℤ) (z : Coeff p × Coeff p)
    (hz : z ∈ realPairLocus p) : truncatePair S z ∈ realPairLocus p := by
  constructor <;> intro n
  · change (truncate S z.1 n).im = 0
    by_cases hn : n ∈ S <;> simp [hn,hz.1 n]
  · change (truncate S z.2 n).im = 0
    by_cases hn : n ∈ S <;> simp [hn,hz.2 n]

/-- All signs outside a finite block fix the truncated center. -/
theorem pairSignChange_truncatePair (S : Finset ℤ) (z : Coeff p × Coeff p)
    (e d : ℤ → Bool) (he : ∀ n ∈ S, e n = false) (hd : ∀ n ∈ S, d n = false) :
    pairSignChange e d (truncatePair S z) = truncatePair S z := by
  apply Prod.ext <;> ext n
  · change signChange e (truncate S z.1) n = truncate S z.1 n
    by_cases hn : n ∈ S <;> simp [hn,he]
  · change signChange d (truncate S z.2) n = truncate S z.2 n
    by_cases hn : n ∈ S <;> simp [hn,hd]

/-- A nearby finite-support center has a ball containing the original
point and still lying inside the prescribed open set. -/
theorem exists_finiteCenter_ball (hp : p ≠ ⊤) (U : Set (Coeff p × Coeff p))
    (hU : IsOpen U) (z : Coeff p × Coeff p) (hz : z ∈ U) :
    ∃ S : Finset ℤ, ∃ R : ℝ, 0 < R ∧ z ∈ ball (truncatePair S z) R ∧
      ball (truncatePair S z) R ⊆ U := by
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp hU z hz
  have ht := (tendsto_truncatePair hp z).eventually (ball_mem_nhds z (by linarith : 0 < r/4))
  obtain ⟨S,hS⟩ := ht.exists
  have hdist : dist (truncatePair S z) z < r/4 := hS
  refine ⟨S,r/2,by linarith,?_,?_⟩
  · change dist z (truncatePair S z) < r/2
    rw [dist_comm]
    linarith
  · intro w hw
    apply hball
    have hw' : dist w (truncatePair S z) < r/2 := hw
    change dist w z < r
    linarith [dist_triangle w (truncatePair S z) z]

end NLS.Coeff
