import NLS.ZakharovShabat.SourceDoubleResolvent
import NLS.ZakharovShabat.FrequencyLocalization

/-! # The quantified source statement of Lemma 3.4

One constant depending only on p works for every period-two potential,
every permitted radius, and every punctured strip. The original-norm
sandwich tends to zero uniformly over strips as the absolute index grows.
-/
noncomputable section
open Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Lemma 3.4 on the entire source space, with a single positive constant
for the exponent. Strip membership itself guarantees that the inverse exists. -/
theorem sourceLemma3_4 (hp : p ≠ ⊤) :
    ∃ C : ℝ, 0 < C ∧ ∀ (φ : CoeffPair p) (n : ℤ) (r : ℝ),
      ∀ (hr : 0 < r) (hrπ : r ≤ Real.pi/4) (z : ℂ) (hz : z ∈ verticalStrip n r),
      ‖sourceDoubleResolvent hp φ z (notMem_freeLattice_of_mem_verticalStrip hr hrπ hz)‖ ≤
        (C/r^2)*(‖φ‖/|(n : ℝ)|^(1/p.toReal)+‖sourceFourierTail n.natAbs φ‖) := by
  have hpp : 0 < p.toReal := ENNReal.toReal_pos
    (zero_lt_one.trans_le (show 1 ≤ p from Fact.out)).ne' hp
  refine ⟨64*p.toReal^2, by positivity, ?_⟩
  intro φ n r hr hrπ z hz
  exact norm_sourceDoubleResolvent_le_verticalStrip hp φ z _ hr hrπ hz

/-- The numerical bound tends to zero in the original potential norm. -/
theorem tendsto_sourceDoubleResolventBound_zero (hp : p ≠ ⊤) (φ : CoeffPair p) (r : ℝ) :
    Tendsto (fun N : ℕ => (64*p.toReal^2/r^2)*
      (‖φ‖/(N : ℝ)^(1/p.toReal)+‖sourceFourierTail N φ‖)) atTop (𝓝 0) := by
  have ht := (tendsto_sourceFourierTail hp φ).norm
  simp only [norm_zero] at ht
  simpa only [zero_add, mul_zero] using
    ((tendsto_frequency_reciprocal_zero hp ‖φ‖).add ht).const_mul (64*p.toReal^2/r^2)

/-- The actual original-norm sandwich is uniformly small on both families
of high-frequency punctured strips, for any fixed positive radius. -/
theorem exists_sourceDoubleResolvent_small (hp : p ≠ ⊤) (φ : CoeffPair p)
    {r : ℝ} (hr : 0 < r) (hrπ : r ≤ Real.pi/4) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℤ, N ≤ n.natAbs → ∀ z : ℂ, ∀ hz : z ∈ verticalStrip n r,
      ‖sourceDoubleResolvent hp φ z (notMem_freeLattice_of_mem_verticalStrip hr hrπ hz)‖ < ε := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    ((tendsto_sourceDoubleResolventBound_zero hp φ r).eventually_lt_const hε)
  refine ⟨N, ?_⟩
  intro n hn z hz
  have h := norm_sourceDoubleResolvent_le_verticalStrip hp φ z
    (notMem_freeLattice_of_mem_verticalStrip hr hrπ hz) hr hrπ hz
  have he : |(n : ℝ)| = (n.natAbs : ℝ) := by simp only [Nat.cast_natAbs, Int.cast_abs]
  rw [he] at h
  exact h.trans_lt (hN n.natAbs hn)

end NLS.ZakharovShabat
