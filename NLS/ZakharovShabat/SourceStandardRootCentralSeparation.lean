import NLS.ZakharovShabat.SourceStandardRootTailSeparation
import NLS.ComplexAnalysis.MidpointDiscSeparation

/-!
# Positive standard-root separation across a finite central block

The base-point periodic gaps admit a shared positive margin on every finite
index block. Continuity keeps nearby endpoints inside smaller midpoint
discs, yielding a uniform positive lower bound for the standard root
throughout every other full central disc.
-/

noncomputable section
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- A point in an earlier full central disc stays away from a point in
a later half-margin disc. -/
theorem sourceCentralDisc_pointwise_separation
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (ε : ℝ) (hε : 0 < ε) {i j : ℤ}
    (hgap : 2*ε ≤
      (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) j).re -
        (canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) i).re)
    {z w : ℂ}
    (hz : z ∈ sourceClusterDisc hp hp1 φ (fun _ => ε) i)
    (hw : w ∈ sourceClusterDisc hp hp1 φ (fun _ => ε/2) j) :
    ε/2 ≤ dist z w := by
  have hi : (canonicalPeriodicLeft hp hp1 (periodOnePotential φ)
      (periodOnePotential_mem φ) i).re ≤
      (canonicalPeriodicRight hp hp1 (periodOnePotential φ)
        (periodOnePotential_mem φ) i).re :=
    re_le_of_complexLexLE
      ((canonicalPeriodicEndpoints_spec hp hp1 (periodOnePotential φ)
        (periodOnePotential_mem φ)).2.1 i)
  have hj : (canonicalPeriodicLeft hp hp1 (periodOnePotential φ)
      (periodOnePotential_mem φ) j).re ≤
      (canonicalPeriodicRight hp hp1 (periodOnePotential φ)
        (periodOnePotential_mem φ) j).re :=
    re_le_of_complexLexLE
      ((canonicalPeriodicEndpoints_spec hp hp1 (periodOnePotential φ)
        (periodOnePotential_mem φ)).2.1 j)
  apply NLS.ComplexAnalysis.midpoint_discs_pointwise_separation
    (ε₁ := ε) (ε₂ := ε/2) (δ := ε/2) hi hj
    (by positivity) hε.le (by positivity) (by linarith [hgap])
  · simpa only [sourceClusterDisc] using hz
  · simpa only [sourceClusterDisc] using hw

/-- The same positive separation with the later point in the full disc. -/
theorem sourceCentralDisc_pointwise_separation_rev
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (ε : ℝ) (hε : 0 < ε) {i j : ℤ}
    (hgap : 2*ε ≤
      (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) j).re -
        (canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) i).re)
    {z w : ℂ}
    (hz : z ∈ sourceClusterDisc hp hp1 φ (fun _ => ε) j)
    (hw : w ∈ sourceClusterDisc hp hp1 φ (fun _ => ε/2) i) :
    ε/2 ≤ dist z w := by
  have hi : (canonicalPeriodicLeft hp hp1 (periodOnePotential φ)
      (periodOnePotential_mem φ) i).re ≤
      (canonicalPeriodicRight hp hp1 (periodOnePotential φ)
        (periodOnePotential_mem φ) i).re :=
    re_le_of_complexLexLE
      ((canonicalPeriodicEndpoints_spec hp hp1 (periodOnePotential φ)
        (periodOnePotential_mem φ)).2.1 i)
  have hj : (canonicalPeriodicLeft hp hp1 (periodOnePotential φ)
      (periodOnePotential_mem φ) j).re ≤
      (canonicalPeriodicRight hp hp1 (periodOnePotential φ)
        (periodOnePotential_mem φ) j).re :=
    re_le_of_complexLexLE
      ((canonicalPeriodicEndpoints_spec hp hp1 (periodOnePotential φ)
        (periodOnePotential_mem φ)).2.1 j)
  have h : ε/2 ≤ dist w z := by
    apply NLS.ComplexAnalysis.midpoint_discs_pointwise_separation
      (ε₁ := ε/2) (ε₂ := ε) (δ := ε/2) hi hj
      (by positivity) (by positivity) hε.le (by linarith [hgap])
    · simpa only [sourceClusterDisc] using hw
    · simpa only [sourceClusterDisc] using hz
  simpa only [dist_comm] using h

/-- A half-margin endpoint gap gives a positive root bound from an
earlier central disc to a later periodic pair. -/
theorem sourceStandardRoot_central_disc_norm_lower
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ ψ : CoeffPair p)
    (ε : ℝ) (hε : 0 < ε) {i j : ℤ}
    (hgap : 2*ε ≤
      (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) j).re -
        (canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) i).re)
    (hcluster : sourceSpectralCluster hp hp1 ψ j ⊆
      sourceClusterDisc hp hp1 φ (fun _ => ε) j)
    (hLsmall : canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) j ∈ sourceClusterDisc hp hp1 φ (fun _ => ε/2) j)
    (hRsmall : canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) j ∈ sourceClusterDisc hp hp1 φ (fun _ => ε/2) j)
    {z : ℂ} (hz : z ∈ sourceClusterDisc hp hp1 φ (fun _ => ε) i) :
    ε/2 ≤ ‖sourceStandardRoot hp hp1 ψ j z‖ := by
  have hdisjoint : Disjoint
      (sourceClusterDisc hp hp1 φ (fun _ => ε) i)
      (sourceClusterDisc hp hp1 φ (fun _ => ε) j) :=
    sourceClusterDiscs_disjoint_of_gap hp hp1 φ (fun _ => ε) hε.le hε.le
      (by simpa only [two_mul] using hgap)
  have hseg : sourcePeriodicSegment hp hp1 ψ j ⊆
      sourceClusterDisc hp hp1 φ (fun _ => ε) j := by
    have hconv : Convex ℝ (sourceClusterDisc hp hp1 φ (fun _ => ε) j) :=
      convex_ball _ _
    exact hconv.segment_subset (hcluster (Or.inl rfl))
      (hcluster (Or.inr (Or.inl rfl)))
  have hznot : z ∉ sourcePeriodicSegment hp hp1 ψ j := by
    intro hzin
    exact (Set.disjoint_left.mp hdisjoint hz) (hseg hzin)
  have hLdist : ε/2 ≤ ‖canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) j-z‖ := by
    simpa only [dist_eq_norm, norm_sub_rev] using
      sourceCentralDisc_pointwise_separation hp hp1 φ ε hε hgap hz hLsmall
  have hRdist : ε/2 ≤ ‖canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) j-z‖ := by
    simpa only [dist_eq_norm, norm_sub_rev] using
      sourceCentralDisc_pointwise_separation hp hp1 φ ε hε hgap hz hRsmall
  have hsq := sourceStandardRoot_norm_sq hp hp1 ψ j z hznot
  have hmul : (ε/2)*(ε/2) ≤
      ‖canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) j-z‖ *
        ‖canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) j-z‖ :=
    mul_le_mul hLdist hRdist (by positivity) (norm_nonneg _)
  nlinarith [norm_nonneg (sourceStandardRoot hp hp1 ψ j z)]

/-- The corresponding root bound from a later central disc to an
earlier periodic pair. -/
theorem sourceStandardRoot_central_disc_norm_lower_rev
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ ψ : CoeffPair p)
    (ε : ℝ) (hε : 0 < ε) {i j : ℤ}
    (hgap : 2*ε ≤
      (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) j).re -
        (canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) i).re)
    (hcluster : sourceSpectralCluster hp hp1 ψ i ⊆
      sourceClusterDisc hp hp1 φ (fun _ => ε) i)
    (hLsmall : canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) i ∈ sourceClusterDisc hp hp1 φ (fun _ => ε/2) i)
    (hRsmall : canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) i ∈ sourceClusterDisc hp hp1 φ (fun _ => ε/2) i)
    {z : ℂ} (hz : z ∈ sourceClusterDisc hp hp1 φ (fun _ => ε) j) :
    ε/2 ≤ ‖sourceStandardRoot hp hp1 ψ i z‖ := by
  have hdisjoint : Disjoint
      (sourceClusterDisc hp hp1 φ (fun _ => ε) i)
      (sourceClusterDisc hp hp1 φ (fun _ => ε) j) :=
    sourceClusterDiscs_disjoint_of_gap hp hp1 φ (fun _ => ε) hε.le hε.le
      (by simpa only [two_mul] using hgap)
  have hseg : sourcePeriodicSegment hp hp1 ψ i ⊆
      sourceClusterDisc hp hp1 φ (fun _ => ε) i := by
    have hconv : Convex ℝ (sourceClusterDisc hp hp1 φ (fun _ => ε) i) :=
      convex_ball _ _
    exact hconv.segment_subset (hcluster (Or.inl rfl))
      (hcluster (Or.inr (Or.inl rfl)))
  have hznot : z ∉ sourcePeriodicSegment hp hp1 ψ i := by
    intro hzin
    exact (Set.disjoint_left.mp hdisjoint.symm hz) (hseg hzin)
  have hLdist : ε/2 ≤ ‖canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) i-z‖ := by
    simpa only [dist_eq_norm, norm_sub_rev] using
      sourceCentralDisc_pointwise_separation_rev hp hp1 φ ε hε hgap hz hLsmall
  have hRdist : ε/2 ≤ ‖canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) i-z‖ := by
    simpa only [dist_eq_norm, norm_sub_rev] using
      sourceCentralDisc_pointwise_separation_rev hp hp1 φ ε hε hgap hz hRsmall
  have hsq := sourceStandardRoot_norm_sq hp hp1 ψ i z hznot
  have hmul : (ε/2)*(ε/2) ≤
      ‖canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) i-z‖ *
        ‖canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) i-z‖ :=
    mul_le_mul hLdist hRdist (by positivity) (norm_nonneg _)
  nlinarith [norm_nonneg (sourceStandardRoot hp hp1 ψ i z)]

/-- Every finite central index block admits one open source neighborhood
and one positive standard-root lower bound for all distinct indices. -/
theorem exists_local_source_central_root_lower
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (s : Finset ℤ) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∀ ψ ∈ V, ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
        ∀ z ∈ sourceClusterDisc hp hp1 φ (fun _ => ε) i,
          ε/2 ≤ ‖sourceStandardRoot hp hp1 ψ j z‖ := by
  let g : ℤ → ℤ → ℝ := fun i j =>
    (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) j).re -
      (canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) i).re
  have hg : ∀ i ∈ s, ∀ j ∈ s, i < j → 0 < g i j := by
    intro i hi j hj hij
    exact sub_pos.mpr (canonicalPeriodicRight_re_lt_left_of_lt hp hp1
      (periodOnePotential φ) (periodOnePotential_mem φ)
      (isRealType_periodOnePotential φ hφ) hij)
  obtain ⟨ε, hε, hgap⟩ :=
    NLS.ComplexAnalysis.exists_positive_margin_for_finite_pairs s g hg
  have hevent : ∀ᶠ ψ : CoeffPair p in 𝓝 φ, ∀ n ∈ s,
      sourceSpectralCluster hp hp1 ψ n ⊆ sourceClusterDisc hp hp1 φ (fun _ => ε) n ∧
      sourceSpectralCluster hp hp1 ψ n ⊆ sourceClusterDisc hp hp1 φ (fun _ => ε/2) n := by
    rw [Finset.eventually_all]
    intro n hn
    have hbaseBig := sourceSpectralCluster_subset_disc hp hp1 φ hφ (fun _ => ε) n hε
    have hbaseSmall := sourceSpectralCluster_subset_disc hp hp1 φ hφ
      (fun _ => ε/2) n (by positivity)
    exact (eventually_sourceSpectralCluster_subset_open hp hp1 φ hφ n _
      Metric.isOpen_ball hbaseBig).and
      (eventually_sourceSpectralCluster_subset_open hp hp1 φ hφ n _
        Metric.isOpen_ball hbaseSmall)
  obtain ⟨V, hVsub, hVopen, hφV⟩ := _root_.mem_nhds_iff.mp hevent
  refine ⟨ε, hε, V, hVopen, hφV, ?_⟩
  intro ψ hψ i hi j hj hij z hz
  have hboth := hVsub hψ j hj
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact sourceStandardRoot_central_disc_norm_lower hp hp1 φ ψ ε hε
      (hgap i hi j hj hlt) hboth.1 (hboth.2 (Or.inl rfl))
        (hboth.2 (Or.inr (Or.inl rfl))) hz
  · exact sourceStandardRoot_central_disc_norm_lower_rev hp hp1 φ ψ ε hε
      (hgap j hj i hi hgt) hboth.1 (hboth.2 (Or.inl rfl))
        (hboth.2 (Or.inr (Or.inl rfl))) hz

end NLS.ZakharovShabat
