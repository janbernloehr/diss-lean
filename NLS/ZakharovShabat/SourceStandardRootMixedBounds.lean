import NLS.ZakharovShabat.SourceStandardRootMixedLower

/-!
# Two-sided mixed central-tail standard-root bounds

The lower and upper index-scale estimates share one constant. Positive
and negative tail geometry supplies their pointwise separation, while
cluster containment in the isolating discs excludes the gap segments.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- One constant controls both sides of the mixed root estimate whenever
pointwise separation and gap-segment exclusion are available. -/
theorem exists_source_central_tail_root_bounds_of_pointwise_gap
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (N : ℕ) (ε : ℝ) :
    ∃ c : ℝ, 1 ≤ c ∧
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
            c⁻¹*|((i-j : ℤ) : ℝ)| ≤ ‖sourceStandardRoot hp hp1 ψ j z‖ ∧
            ‖sourceStandardRoot hp hp1 ψ j z‖ ≤ c*|((i-j : ℤ) : ℝ)|) ∧
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
            c⁻¹*|((i-j : ℤ) : ℝ)| ≤ ‖sourceStandardRoot hp hp1 ψ i z‖ ∧
            ‖sourceStandardRoot hp hp1 ψ i z‖ ≤ c*|((i-j : ℤ) : ℝ)|) := by
  obtain ⟨B, hB, hlow1, hlow2⟩ :=
    exists_source_central_tail_root_index_lower hp hp1 φ N ε
  obtain ⟨C, hC, hupp1, hupp2⟩ :=
    exists_source_central_tail_root_upper hp hp1 φ N ε
  let c := max B C
  have hc : 1 ≤ c := hB.trans (le_max_left _ _)
  have hBc : B ≤ c := le_max_left _ _
  have hCc : C ≤ c := le_max_right _ _
  have hinv : c⁻¹ ≤ B⁻¹ := inv_anti₀ (by linarith) hBc
  refine ⟨c, hc, ?_, ?_⟩
  · intro ψ i j hi hj z hz hL hR hsepL hsepR hznot
    have hd : 0 ≤ |((i-j : ℤ) : ℝ)| := abs_nonneg _
    constructor
    · exact (mul_le_mul_of_nonneg_right hinv hd).trans
        (hlow1 ψ i j hi hj z hz hL hR hsepL hsepR hznot)
    · exact (hupp1 ψ i j hi hj z hz hL hR hznot).trans
        (mul_le_mul_of_nonneg_right hCc hd)
  · intro ψ i j hi hj z hz hL hR hsepL hsepR hznot
    have hd : 0 ≤ |((i-j : ℤ) : ℝ)| := abs_nonneg _
    constructor
    · exact (mul_le_mul_of_nonneg_right hinv hd).trans
        (hlow2 ψ i j hi hj z hz hL hR hsepL hsepR hznot)
    · exact (hupp2 ψ i j hi hj z hz hL hR hznot).trans
        (mul_le_mul_of_nonneg_right hCc hd)



/-- Every central disc and tail disc are disjoint and pointwise separated
by a quarter-π under the strict outer-endpoint localization. -/
theorem source_central_tail_pointwise_geometry
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (N : ℕ) (ε : ℝ) (hε : 0 ≤ ε) (hεmax : ε ≤ Real.pi/4)
    (houterL : canonicalPeriodicLeft hp hp1 (periodOnePotential φ)
      (periodOnePotential_mem φ) (-(N : ℤ)) ∈ refinedResonantDisk (-(N : ℤ)))
    (houterR : canonicalPeriodicRight hp hp1 (periodOnePotential φ)
      (periodOnePotential_mem φ) (N : ℤ) ∈ refinedResonantDisk (N : ℤ))
    (i j : ℤ) (hi : i.natAbs ≤ N) (hj : N < j.natAbs) :
    Disjoint (sourceClusterDisc hp hp1 φ (fun _ => ε) i)
      (refinedResonantDisk j) ∧
      ∀ z ∈ sourceClusterDisc hp hp1 φ (fun _ => ε) i,
        ∀ w ∈ refinedResonantDisk j, Real.pi/4 ≤ dist z w := by
  have hside : j < -(N : ℤ) ∨ (N : ℤ) < j := by omega
  rcases hside with hleft | hright
  · refine ⟨sourceClusterDisc_disjoint_negative_tail hp hp1 φ hφ N ε
      hε hεmax houterL (by omega) hleft, ?_⟩
    intro z hz w hw
    exact sourceClusterDisc_refinedDisk_negative_pointwise hp hp1 φ hφ N ε
      hε hεmax houterL (by omega) hleft hz hw
  · refine ⟨sourceClusterDisc_disjoint_positive_tail hp hp1 φ hφ N ε
      hε hεmax houterR (by omega) hright, ?_⟩
    intro z hz w hw
    exact sourceClusterDisc_refinedDisk_positive_pointwise hp hp1 φ hφ N ε
      hε hεmax houterR (by omega) hright hz hw


/-- Equation (2.10) for every central/tail pair, once the same isolating
disc family contains the nearby periodic clusters. -/
theorem exists_source_central_tail_root_bounds
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (N : ℕ) (ε : ℝ) (hε : 0 ≤ ε) (hεmax : ε ≤ Real.pi/4)
    (houterL : canonicalPeriodicLeft hp hp1 (periodOnePotential φ)
      (periodOnePotential_mem φ) (-(N : ℤ)) ∈ refinedResonantDisk (-(N : ℤ)))
    (houterR : canonicalPeriodicRight hp hp1 (periodOnePotential φ)
      (periodOnePotential_mem φ) (N : ℤ) ∈ refinedResonantDisk (N : ℤ)) :
    ∃ c : ℝ, 1 ≤ c ∧
      ∀ (ψ : CoeffPair p),
        (∀ n : ℤ, sourceSpectralCluster hp hp1 ψ n ⊆
          sourceIsolatingDisc hp hp1 φ N ε n) →
        ∀ (i j : ℤ), i.natAbs ≤ N → N < j.natAbs →
          (∀ z ∈ sourceClusterDisc hp hp1 φ (fun _ => ε) i,
            c⁻¹*|((i-j : ℤ) : ℝ)| ≤ ‖sourceStandardRoot hp hp1 ψ j z‖ ∧
            ‖sourceStandardRoot hp hp1 ψ j z‖ ≤ c*|((i-j : ℤ) : ℝ)|) ∧
          (∀ z ∈ refinedResonantDisk j,
            c⁻¹*|((i-j : ℤ) : ℝ)| ≤ ‖sourceStandardRoot hp hp1 ψ i z‖ ∧
            ‖sourceStandardRoot hp hp1 ψ i z‖ ≤ c*|((i-j : ℤ) : ℝ)|) := by
  obtain ⟨c, hc, hbound1, hbound2⟩ :=
    exists_source_central_tail_root_bounds_of_pointwise_gap hp hp1 φ N ε
  refine ⟨c, hc, ?_⟩
  intro ψ hcluster i j hi hj
  obtain ⟨hdisjoint, hpoint⟩ := source_central_tail_pointwise_geometry
    hp hp1 φ hφ N ε hε hεmax houterL houterR i j hi hj
  have hnj : ¬ j.natAbs ≤ N := by omega
  have hcentral : sourceSpectralCluster hp hp1 ψ i ⊆
      sourceClusterDisc hp hp1 φ (fun _ => ε) i := by
    simpa only [sourceIsolatingDisc, if_pos hi] using hcluster i
  have htail : sourceSpectralCluster hp hp1 ψ j ⊆
      refinedResonantDisk j := by
    simpa only [sourceIsolatingDisc, if_neg hnj] using hcluster j
  have hLi : canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) i ∈
      sourceClusterDisc hp hp1 φ (fun _ => ε) i := hcentral (Or.inl rfl)
  have hRi : canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) i ∈
      sourceClusterDisc hp hp1 φ (fun _ => ε) i :=
    hcentral (Or.inr (Or.inl rfl))
  have hLj : canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) j ∈ refinedResonantDisk j := htail (Or.inl rfl)
  have hRj : canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) j ∈ refinedResonantDisk j :=
    htail (Or.inr (Or.inl rfl))
  have hsegj : sourcePeriodicSegment hp hp1 ψ j ⊆ refinedResonantDisk j := by
    have h := sourcePeriodicSegment_subset_isolatingDisc hp hp1 φ ψ N ε j (hcluster j)
    simpa only [sourceIsolatingDisc, if_neg hnj] using h
  have hsegi : sourcePeriodicSegment hp hp1 ψ i ⊆
      sourceClusterDisc hp hp1 φ (fun _ => ε) i := by
    have h := sourcePeriodicSegment_subset_isolatingDisc hp hp1 φ ψ N ε i (hcluster i)
    simpa only [sourceIsolatingDisc, if_pos hi] using h
  constructor
  · intro z hz
    have hznot : z ∉ sourcePeriodicSegment hp hp1 ψ j := by
      intro hzin
      exact (Set.disjoint_left.mp hdisjoint hz) (hsegj hzin)
    exact hbound1 ψ i j hi hj z hz hLj hRj
      (hpoint z hz _ hLj) (hpoint z hz _ hRj) hznot
  · intro z hz
    have hznot : z ∉ sourcePeriodicSegment hp hp1 ψ i := by
      intro hzin
      exact (Set.disjoint_left.mp hdisjoint.symm hz) (hsegi hzin)
    exact hbound2 ψ i j hi hj z hz hLi hRi
      (hpoint _ hLi z hz) (hpoint _ hRi z hz) hznot

end NLS.ZakharovShabat
