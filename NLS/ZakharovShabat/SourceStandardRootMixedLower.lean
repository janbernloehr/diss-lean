import NLS.ZakharovShabat.SourceStandardRootMixedUpper

/-!
# Index-scale lower bounds for mixed central and tail roots

The fixed quarter-π separation between a central point and tail endpoints,
combined with their lattice-center separation, bounds the index gap by each
endpoint distance. The exact standard-root norm formula transfers this to
both central/tail orientations with one constant for the finite central block.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

theorem central_tail_pointwise_lattice_lower
    (i j : ℤ) (R : ℝ)
    {z w : ℂ}
    (hz : ‖z-(Real.pi:ℂ)*i‖ ≤ R)
    (hw : w ∈ refinedResonantDisk j) :
    Real.pi*|((i-j : ℤ) : ℝ)| ≤ dist z w+R+Real.pi/4 := by
  let d : ℝ := |((i-j : ℤ) : ℝ)|
  have hw' : dist w ((Real.pi:ℂ)*j) < Real.pi/4 := by
    simpa only [refinedResonantDisk, mem_ball] using hw
  have hcenter : dist ((Real.pi:ℂ)*i) ((Real.pi:ℂ)*j) = Real.pi*d := by
    simpa only [dist_eq_norm, d] using norm_free_center_sub i j
  have htri := dist_triangle4 ((Real.pi:ℂ)*i) z w ((Real.pi:ℂ)*j)
  rw [hcenter] at htri
  have hz' : dist ((Real.pi:ℂ)*i) z ≤ R := by
    simpa only [dist_eq_norm, norm_sub_rev] using hz
  dsimp [d] at *
  linarith

theorem central_tail_pointwise_index_lower
    (i j : ℤ) (R : ℝ) (hR : 0 ≤ R)
    {z w : ℂ}
    (hz : ‖z-(Real.pi:ℂ)*i‖ ≤ R)
    (hw : w ∈ refinedResonantDisk j)
    (hsep : Real.pi/4 ≤ dist z w) :
    |((i-j : ℤ) : ℝ)| ≤ (1+4*R+Real.pi)*dist z w := by
  let d : ℝ := |((i-j : ℤ) : ℝ)|
  let X : ℝ := dist z w
  let A : ℝ := R+Real.pi/4
  have hlin : Real.pi*d ≤ X+A := by
    have h := central_tail_pointwise_lattice_lower i j R hz hw
    dsimp [d, X, A]
    linarith
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hX : 1 ≤ 4*X := by
    dsimp [X] at *
    nlinarith [Real.pi_gt_three]
  have hmul := mul_nonneg hA (sub_nonneg.mpr hX)
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hpi : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
  have hpid := mul_nonneg (sub_nonneg.mpr hpi) hd
  dsimp [d, X, A] at *
  nlinarith

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

private theorem sourceRoot_index_lower_from_endpoint_index_lower
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (n : ℤ) (z : ℂ)
    (hz : z ∉ sourcePeriodicSegment hp hp1 ψ n)
    (d B : ℝ) (hd : 0 ≤ d) (hB : 0 < B)
    (hL : d ≤ B*‖canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n-z‖)
    (hR : d ≤ B*‖canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n-z‖) :
    B⁻¹*d ≤ ‖sourceStandardRoot hp hp1 ψ n z‖ := by
  apply sourceRoot_norm_lower_from_endpoints hp hp1 ψ n z hz
    (B⁻¹*d) (by positivity)
  · rw [show B⁻¹*d = d/B by ring]
    exact (div_le_iff₀ hB).2 (by simpa only [mul_comm] using hL)
  · rw [show B⁻¹*d = d/B by ring]
    exact (div_le_iff₀ hB).2 (by simpa only [mul_comm] using hR)

theorem exists_source_central_tail_root_index_lower
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (N : ℕ) (ε : ℝ) :
    ∃ B : ℝ, 1 ≤ B ∧
      (∀ (ψ : CoeffPair p) (i j : ℤ), i.natAbs ≤ N → N < j.natAbs →
        ∀ z ∈ sourceClusterDisc hp hp1 φ (fun _ => ε) i,
          ∀ _hL : canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
            (periodOnePotential_mem ψ) j ∈ refinedResonantDisk j,
          ∀ _hR : canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
            (periodOnePotential_mem ψ) j ∈ refinedResonantDisk j,
          Real.pi/4 ≤ dist z
            (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
              (periodOnePotential_mem ψ) j) →
          Real.pi/4 ≤ dist z
            (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
              (periodOnePotential_mem ψ) j) →
          z ∉ sourcePeriodicSegment hp hp1 ψ j →
            B⁻¹*|((i-j : ℤ) : ℝ)| ≤ ‖sourceStandardRoot hp hp1 ψ j z‖) ∧
      (∀ (ψ : CoeffPair p) (i j : ℤ), i.natAbs ≤ N → N < j.natAbs →
        ∀ z ∈ refinedResonantDisk j,
          ∀ _hL : canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
            (periodOnePotential_mem ψ) i ∈ sourceClusterDisc hp hp1 φ (fun _ => ε) i,
          ∀ _hR : canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
            (periodOnePotential_mem ψ) i ∈ sourceClusterDisc hp hp1 φ (fun _ => ε) i,
          Real.pi/4 ≤ dist
            (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
              (periodOnePotential_mem ψ) i) z →
          Real.pi/4 ≤ dist
            (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
              (periodOnePotential_mem ψ) i) z →
          z ∉ sourcePeriodicSegment hp hp1 ψ i →
            B⁻¹*|((i-j : ℤ) : ℝ)| ≤ ‖sourceStandardRoot hp hp1 ψ i z‖) := by
  obtain ⟨R, hR, hcenter⟩ :=
    exists_central_disc_lattice_offset_bound hp hp1 φ N ε
  let B : ℝ := 1+4*R+Real.pi
  have hB : 0 < B := by dsimp [B]; positivity
  have hB1 : 1 ≤ B := by dsimp [B]; linarith [Real.pi_pos]
  refine ⟨B, hB1, ?_, ?_⟩
  · intro ψ i j hi hj z hz hL hR' hsepL hsepR hznot
    have hLd : |((i-j : ℤ) : ℝ)| ≤
        B*‖canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
          (periodOnePotential_mem ψ) j-z‖ := by
      simpa only [dist_eq_norm, norm_sub_rev] using
        central_tail_pointwise_index_lower i j R hR
          (hcenter i hi z hz) hL hsepL
    have hRd : |((i-j : ℤ) : ℝ)| ≤
        B*‖canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
          (periodOnePotential_mem ψ) j-z‖ := by
      simpa only [dist_eq_norm, norm_sub_rev] using
        central_tail_pointwise_index_lower i j R hR
          (hcenter i hi z hz) hR' hsepR
    exact sourceRoot_index_lower_from_endpoint_index_lower hp hp1 ψ j z hznot
      _ B (by positivity) hB hLd hRd
  · intro ψ i j hi hj z hz hL hR' hsepL hsepR hznot
    have hLd : |((i-j : ℤ) : ℝ)| ≤
        B*‖canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
          (periodOnePotential_mem ψ) i-z‖ := by
      simpa only [dist_eq_norm] using
        central_tail_pointwise_index_lower i j R hR
          (hcenter i hi _ hL) hz hsepL
    have hRd : |((i-j : ℤ) : ℝ)| ≤
        B*‖canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
          (periodOnePotential_mem ψ) i-z‖ := by
      simpa only [dist_eq_norm] using
        central_tail_pointwise_index_lower i j R hR
          (hcenter i hi _ hR') hz hsepR
    exact sourceRoot_index_lower_from_endpoint_index_lower hp hp1 ψ i z hznot
      _ B (by positivity) hB hLd hRd

end NLS.ZakharovShabat
