import NLS.ZakharovShabat.SourceStandardRootCentralBounds

/-!
# Positive-tail standard-root separation from central discs

The outer central endpoint lies strictly inside its free quarter-π disc.
That strict localization leaves at least a quarter-π between any central
disc and a positive tail endpoint. The exact root norm identity transfers
this separation in both spectral-index orientations.
-/

noncomputable section
open Set Metric Complex
open NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The real part of a point in a free quarter-π disc lies strictly
below the right edge of its real quarter-π strip. -/
theorem refinedResonantDisk_re_upper_strict
    {n : ℤ} {z : ℂ} (hz : z ∈ refinedResonantDisk n) :
    z.re < Real.pi*(n:ℝ)+Real.pi/4 := by
  have hnorm : ‖z-(Real.pi:ℂ)*n‖ < Real.pi/4 := by
    simpa only [refinedResonantDisk, mem_ball, dist_eq_norm] using hz
  have hreal := Complex.abs_re_le_norm (z-(Real.pi:ℂ)*n)
  have hdiff : (z-(Real.pi:ℂ)*n).re = z.re-Real.pi*(n:ℝ) := by simp
  rw [hdiff] at hreal
  have hupper := (abs_le.mp hreal).2
  linarith

private theorem source_right_le_right_of_le
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    {i j : ℤ} (hij : i ≤ j) :
    (canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) i).re ≤
      (canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) j).re := by
  rcases hij.lt_or_eq with hij | rfl
  · have hgap := canonicalPeriodicRight_re_lt_left_of_lt hp hp1
      (periodOnePotential φ) (periodOnePotential_mem φ)
      (isRealType_periodOnePotential φ hφ) hij
    have hwithin := re_le_of_complexLexLE
      ((canonicalPeriodicEndpoints_spec hp hp1 (periodOnePotential φ)
        (periodOnePotential_mem φ)).2.1 j)
    exact hgap.le.trans hwithin
  · rfl

/-- A central midpoint disc and a positive tail free disc have a
uniform pointwise distance of at least π/4. -/
theorem sourceClusterDisc_refinedDisk_positive_pointwise
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (N : ℕ) (ε : ℝ) (hε : 0 ≤ ε) (hεmax : ε ≤ Real.pi/4)
    (houter : canonicalPeriodicRight hp hp1 (periodOnePotential φ)
      (periodOnePotential_mem φ) (N : ℤ) ∈ refinedResonantDisk (N : ℤ))
    {i j : ℤ} (hi : i ≤ (N : ℤ)) (hj : (N : ℤ) < j)
    {z w : ℂ} (hz : z ∈ sourceClusterDisc hp hp1 φ (fun _ => ε) i)
    (hw : w ∈ refinedResonantDisk j) :
    Real.pi/4 ≤ dist z w := by
  have hwithin := re_le_of_complexLexLE
    ((canonicalPeriodicEndpoints_spec hp hp1 (periodOnePotential φ)
      (periodOnePotential_mem φ)).2.1 i)
  have hRi := source_right_le_right_of_le hp hp1 φ hφ hi
  have hRN := refinedResonantDisk_re_upper_strict houter
  have hjreal : ((N : ℤ) : ℝ)+1 ≤ (j : ℝ) := by
    exact_mod_cast (show (N : ℤ)+1 ≤ j by omega)
  have hmul := mul_le_mul_of_nonneg_left hjreal Real.pi_pos.le
  have hgap : Real.pi/4 + ε + Real.pi/4 ≤
      Real.pi*(j:ℝ) -
        (canonicalPeriodicRight hp hp1 (periodOnePotential φ)
          (periodOnePotential_mem φ) i).re := by
    nlinarith
  apply NLS.ComplexAnalysis.midpoint_discs_pointwise_separation
    (l₂ := Real.pi*(j:ℝ)) (r₂ := Real.pi*(j:ℝ))
    (ε₁ := ε) (ε₂ := Real.pi/4) (δ := Real.pi/4)
    hwithin le_rfl (by positivity) hε (by positivity) hgap
  · simpa only [sourceClusterDisc] using hz
  · simpa only [refinedResonantDisk, Complex.ofReal_mul,
      Complex.ofReal_intCast, add_self_div_two, sub_self, zero_div,
      zero_add] using hw

private theorem sourceRoot_norm_lower_from_endpoints
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (n : ℤ) (z : ℂ)
    (hz : z ∉ sourcePeriodicSegment hp hp1 ψ n)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hL : δ ≤ ‖canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n-z‖)
    (hR : δ ≤ ‖canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n-z‖) :
    δ ≤ ‖sourceStandardRoot hp hp1 ψ n z‖ := by
  have hsq := sourceStandardRoot_norm_sq hp hp1 ψ n z hz
  have hmul : δ*δ ≤
      ‖canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n-z‖ *
        ‖canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n-z‖ :=
    mul_le_mul hL hR hδ (norm_nonneg _)
  nlinarith [norm_nonneg (sourceStandardRoot hp hp1 ψ n z)]

/-- A positive-tail standard root has norm at least π/4 on every
central disc. -/
theorem sourceStandardRoot_central_positive_tail_lower
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ ψ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ))
    (N : ℕ) (ε : ℝ) (hε : 0 ≤ ε) (hεmax : ε ≤ Real.pi/4)
    (houter : canonicalPeriodicRight hp hp1 (periodOnePotential φ)
      (periodOnePotential_mem φ) (N : ℤ) ∈ refinedResonantDisk (N : ℤ))
    {i j : ℤ} (hi : i ≤ (N : ℤ)) (hj : (N : ℤ) < j)
    (hcluster : sourceSpectralCluster hp hp1 ψ j ⊆ refinedResonantDisk j)
    {z : ℂ} (hz : z ∈ sourceClusterDisc hp hp1 φ (fun _ => ε) i) :
    Real.pi/4 ≤ ‖sourceStandardRoot hp hp1 ψ j z‖ := by
  have hdisjoint := sourceClusterDisc_disjoint_positive_tail hp hp1 φ hφ N ε
    hε hεmax houter hi hj
  have hseg : sourcePeriodicSegment hp hp1 ψ j ⊆ refinedResonantDisk j := by
    have hconv : Convex ℝ (refinedResonantDisk j) := convex_ball _ _
    exact hconv.segment_subset (hcluster (Or.inl rfl))
      (hcluster (Or.inr (Or.inl rfl)))
  have hznot : z ∉ sourcePeriodicSegment hp hp1 ψ j := by
    intro hzin
    exact (Set.disjoint_left.mp hdisjoint hz) (hseg hzin)
  apply sourceRoot_norm_lower_from_endpoints hp hp1 ψ j z hznot
    (Real.pi/4) (by positivity)
  · simpa only [dist_eq_norm, norm_sub_rev] using
      sourceClusterDisc_refinedDisk_positive_pointwise hp hp1 φ hφ N ε hε
        hεmax houter hi hj hz (hcluster (Or.inl rfl))
  · simpa only [dist_eq_norm, norm_sub_rev] using
      sourceClusterDisc_refinedDisk_positive_pointwise hp hp1 φ hφ N ε hε
        hεmax houter hi hj hz (hcluster (Or.inr (Or.inl rfl)))

/-- A central standard root has norm at least π/4 on every positive
tail free disc. -/
theorem sourceStandardRoot_positive_tail_central_lower
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ ψ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ))
    (N : ℕ) (ε : ℝ) (hε : 0 ≤ ε) (hεmax : ε ≤ Real.pi/4)
    (houter : canonicalPeriodicRight hp hp1 (periodOnePotential φ)
      (periodOnePotential_mem φ) (N : ℤ) ∈ refinedResonantDisk (N : ℤ))
    {i j : ℤ} (hi : i ≤ (N : ℤ)) (hj : (N : ℤ) < j)
    (hcluster : sourceSpectralCluster hp hp1 ψ i ⊆
      sourceClusterDisc hp hp1 φ (fun _ => ε) i)
    {z : ℂ} (hz : z ∈ refinedResonantDisk j) :
    Real.pi/4 ≤ ‖sourceStandardRoot hp hp1 ψ i z‖ := by
  have hdisjoint := sourceClusterDisc_disjoint_positive_tail hp hp1 φ hφ N ε
    hε hεmax houter hi hj
  have hseg : sourcePeriodicSegment hp hp1 ψ i ⊆
      sourceClusterDisc hp hp1 φ (fun _ => ε) i := by
    have hconv : Convex ℝ (sourceClusterDisc hp hp1 φ (fun _ => ε) i) :=
      convex_ball _ _
    exact hconv.segment_subset (hcluster (Or.inl rfl))
      (hcluster (Or.inr (Or.inl rfl)))
  have hznot : z ∉ sourcePeriodicSegment hp hp1 ψ i := by
    intro hzin
    exact (Set.disjoint_left.mp hdisjoint.symm hz) (hseg hzin)
  apply sourceRoot_norm_lower_from_endpoints hp hp1 ψ i z hznot
    (Real.pi/4) (by positivity)
  · simpa only [dist_eq_norm] using
      sourceClusterDisc_refinedDisk_positive_pointwise hp hp1 φ hφ N ε hε
        hεmax houter hi hj (hcluster (Or.inl rfl)) hz
  · simpa only [dist_eq_norm] using
      sourceClusterDisc_refinedDisk_positive_pointwise hp hp1 φ hφ N ε hε
        hεmax houter hi hj (hcluster (Or.inr (Or.inl rfl))) hz

end NLS.ZakharovShabat
