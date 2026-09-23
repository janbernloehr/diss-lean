import NLS.ZakharovShabat.SourceStandardRootJointAnalytic

/-!
# Norm control of standard roots on different isolating discs

The norm squared of a standard root is exactly the product of its two
endpoint distances. This transfers quantitative endpoint bounds to the
root and proves nonvanishing on a different isolating disc.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Exact modulus identity for the canonical periodic standard root. -/
theorem sourceStandardRoot_norm_sq
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (n : ℤ) (z : ℂ)
    (hz : z ∉ sourcePeriodicSegment hp hp1 ψ n) :
    ‖sourceStandardRoot hp hp1 ψ n z‖^2 =
      ‖canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n-z‖ *
        ‖canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n-z‖ := by
  rw [← norm_pow, sourceStandardRoot_sq_of_not_mem_segment hp hp1 ψ n z hz, norm_mul]

/-- Equal lower and upper bounds on both endpoint distances give the same
bounds on the standard-root norm. -/
theorem sourceStandardRoot_norm_bounds_of_endpoint_bounds
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (n : ℤ) (z : ℂ)
    (hz : z ∉ sourcePeriodicSegment hp hp1 ψ n)
    (lo hi : ℝ) (hlo : 0 ≤ lo) (hhi : 0 ≤ hi)
    (hLlo : lo ≤ ‖canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n-z‖)
    (hRlo : lo ≤ ‖canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n-z‖)
    (hLhi : ‖canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n-z‖ ≤ hi)
    (hRhi : ‖canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n-z‖ ≤ hi) :
    lo ≤ ‖sourceStandardRoot hp hp1 ψ n z‖ ∧
      ‖sourceStandardRoot hp hp1 ψ n z‖ ≤ hi := by
  have hsq := sourceStandardRoot_norm_sq hp hp1 ψ n z hz
  constructor
  · have hmul : lo*lo ≤
        ‖canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n-z‖ *
          ‖canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n-z‖ :=
      mul_le_mul hLlo hRlo hlo (norm_nonneg _)
    nlinarith [norm_nonneg (sourceStandardRoot hp hp1 ψ n z)]
  · have hmul :
        ‖canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n-z‖ *
          ‖canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n-z‖ ≤ hi*hi :=
      mul_le_mul hLhi hRhi (norm_nonneg _) hhi
    nlinarith [norm_nonneg (sourceStandardRoot hp hp1 ψ n z)]

/-- The modulus identity holds throughout any distinct isolating disc. -/
theorem sourceStandardRoot_norm_sq_on_distinct_isolatingDisc
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ ψ : CoeffPair p)
    (N : ℕ) (ε : ℝ) (m n : ℤ) (z : ℂ)
    (hcluster : sourceSpectralCluster hp hp1 ψ n ⊆
      sourceIsolatingDisc hp hp1 φ N ε n)
    (hdisjoint : Disjoint (sourceIsolatingDisc hp hp1 φ N ε m)
      (sourceIsolatingDisc hp hp1 φ N ε n))
    (hz : z ∈ sourceIsolatingDisc hp hp1 φ N ε m) :
    ‖sourceStandardRoot hp hp1 ψ n z‖^2 =
      ‖canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n-z‖ *
        ‖canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n-z‖ := by
  have hsegment := sourcePeriodicSegment_subset_isolatingDisc hp hp1 φ ψ N ε n hcluster
  have hznot : z ∉ sourcePeriodicSegment hp hp1 ψ n := by
    intro hzin
    exact (Set.disjoint_left.mp hdisjoint hz) (hsegment hzin)
  exact sourceStandardRoot_norm_sq hp hp1 ψ n z hznot

/-- A standard root for index `n` never vanishes on a disjoint assigned
isolating disc. -/
theorem sourceStandardRoot_ne_zero_on_distinct_isolatingDisc
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ ψ : CoeffPair p)
    (N : ℕ) (ε : ℝ) (m n : ℤ) (z : ℂ)
    (hcluster : sourceSpectralCluster hp hp1 ψ n ⊆
      sourceIsolatingDisc hp hp1 φ N ε n)
    (hdisjoint : Disjoint (sourceIsolatingDisc hp hp1 φ N ε m)
      (sourceIsolatingDisc hp hp1 φ N ε n))
    (hz : z ∈ sourceIsolatingDisc hp hp1 φ N ε m) :
    sourceStandardRoot hp hp1 ψ n z ≠ 0 := by
  have hL : canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n ≠ z := by
    intro he
    exact (Set.disjoint_left.mp hdisjoint hz) (by
      simpa only [he] using hcluster (Or.inl rfl))
  have hR : canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n ≠ z := by
    intro he
    exact (Set.disjoint_left.mp hdisjoint hz) (by
      simpa only [he] using hcluster (Or.inr (Or.inl rfl)))
  have hsq := sourceStandardRoot_norm_sq_on_distinct_isolatingDisc
    hp hp1 φ ψ N ε m n z hcluster hdisjoint hz
  intro he
  simp [he] at hsq
  rcases hsq with h | h
  · exact hL (sub_eq_zero.mp h)
  · exact hR (sub_eq_zero.mp h)

end NLS.ZakharovShabat
