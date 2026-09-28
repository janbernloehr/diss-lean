import NLS.ZakharovShabat.SourceCriticalRootRatioEnclosingCircle

/-!
# A fixed enclosing circle for nearby source potentials

The selected periodic gap remains inside one circle on a neighborhood
of a real-type source. Its filled disc stays free of every other gap.
Thus the same integration contour is valid while the source varies
through nearby complex potentials.
-/

noncomputable section
open Set Metric Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Fixing one family of pairwise disjoint isolating discs, a selected
gap has a real-centered contour whose entire closed disc remains inside
its assigned isolating disc throughout a smaller source neighborhood. -/
theorem exists_local_sourceCriticalRootRatio_uniformRealCenteredEnclosingCircle_of_isolatingDiscs
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (N : ℕ) (ε : ℝ) (U : Set (CoeffPair p))
    (hUopen : IsOpen U) (hφU : φ ∈ U)
    (hcluster : ∀ ψ ∈ U, ∀ j : ℤ,
      sourceSpectralCluster hp hp1 ψ j ⊆
        sourceIsolatingDisc hp hp1 φ N ε j)
    (hdisjoint : ∀ i j : ℤ, i ≠ j →
      Disjoint (sourceIsolatingDisc hp hp1 φ N ε i)
        (sourceIsolatingDisc hp hp1 φ N ε j))
    (n : ℤ) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧ V ⊆ U ∧
      ∃ c : ℂ, ∃ R : ℝ, c.im = 0 ∧ 0 < R ∧
        closedBall c R ⊆ sourceIsolatingDisc hp hp1 φ N ε n ∧
        ∀ ψ ∈ V,
          sourcePeriodicSegment hp hp1 ψ n ⊆ ball c R ∧
          closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 ψ n ∧
          sphere c R ⊆ sourceCanonicalRootDomain hp hp1 ψ := by
  obtain ⟨c, R, hcReal, hRpos, hbase, hfilled⟩ :=
    exists_sourcePeriodicSegment_realCenteredEnclosingCircle_within_isolatingDisc
      hp hp1 φ φ N ε n (hcluster φ hφU n)
  have hLbase : canonicalPeriodicLeft hp hp1 (periodOnePotential φ)
      (periodOnePotential_mem φ) n ∈ ball c R :=
    hbase (left_mem_segment ℝ _ _)
  have hRbase : canonicalPeriodicRight hp hp1 (periodOnePotential φ)
      (periodOnePotential_mem φ) n ∈ ball c R :=
    hbase (right_mem_segment ℝ _ _)
  have hLnear : ∀ᶠ ψ : CoeffPair p in 𝓝 φ,
      canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n ∈ ball c R :=
    (continuousAt_canonicalPeriodicLeft_periodOne_of_realType
      hp hp1 φ hφ n).eventually (isOpen_ball.mem_nhds hLbase)
  have hRnear : ∀ᶠ ψ : CoeffPair p in 𝓝 φ,
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n ∈ ball c R :=
    (continuousAt_canonicalPeriodicRight_periodOne_of_realType
      hp hp1 φ hφ n).eventually (isOpen_ball.mem_nhds hRbase)
  have hnear : ∀ᶠ ψ : CoeffPair p in 𝓝 φ,
      ψ ∈ U ∧
        canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
          (periodOnePotential_mem ψ) n ∈ ball c R ∧
        canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
          (periodOnePotential_mem ψ) n ∈ ball c R := by
    filter_upwards [hUopen.mem_nhds hφU, hLnear, hRnear] with ψ hψU hL hR
    exact ⟨hψU, hL, hR⟩
  obtain ⟨V, hVsub, hVopen, hφV⟩ := _root_.mem_nhds_iff.mp hnear
  refine ⟨V, hVopen, hφV, (fun ψ hψ => (hVsub hψ).1),
    c, R, hcReal, hRpos, hfilled, ?_⟩
  intro ψ hψV
  obtain ⟨hψU, hL, hR⟩ := hVsub hψV
  have hseg : sourcePeriodicSegment hp hp1 ψ n ⊆ ball c R := by
    change segment ℝ
      (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n)
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n) ⊆ ball c R
    exact (convex_ball c R).segment_subset hL hR
  have hother : closedBall c R ⊆
      sourceStandardRootOmittedDomain hp hp1 ψ n :=
    hfilled.trans (sourceIsolatingDisc_subset_omittedDomain
      hp hp1 φ ψ N ε (hcluster ψ hψU) hdisjoint n)
  exact ⟨hseg, hother,
    sourceCanonicalRootDomain_of_enclosingCircle hp hp1 ψ n c R hseg hother⟩

/-- A real-type source and a selected gap admit one fixed real-centered
circular contour that encloses that gap and avoids all other gaps
throughout an open source neighborhood. -/
theorem exists_local_sourceCriticalRootRatio_uniformRealCenteredEnclosingCircle
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (n : ℤ) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∃ c : ℂ, ∃ R : ℝ, c.im = 0 ∧ 0 < R ∧
        ∀ ψ ∈ V,
          sourcePeriodicSegment hp hp1 ψ n ⊆ ball c R ∧
          closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 ψ n ∧
          sphere c R ⊆ sourceCanonicalRootDomain hp hp1 ψ := by
  obtain ⟨N, ε, _, _, U, hUopen, _, hφU, hcluster, hdisjoint⟩ :=
    exists_local_source_connected_isolating_discs hp hp1 φ hφ
  obtain ⟨V, hVopen, hφV, _, c, R, hcReal, hRpos, _, hdata⟩ :=
    exists_local_sourceCriticalRootRatio_uniformRealCenteredEnclosingCircle_of_isolatingDiscs
      hp hp1 φ hφ N ε U hUopen hφU hcluster hdisjoint n
  exact ⟨V, hVopen, hφV, c, R, hcReal, hRpos, hdata⟩

/-- The selected gap has a fixed enclosing contour throughout a
source neighborhood. -/
theorem exists_local_sourceCriticalRootRatio_uniformEnclosingCircle
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (n : ℤ) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∃ c : ℂ, ∃ R : ℝ, 0 < R ∧
        ∀ ψ ∈ V,
          sourcePeriodicSegment hp hp1 ψ n ⊆ ball c R ∧
          closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 ψ n ∧
          sphere c R ⊆ sourceCanonicalRootDomain hp hp1 ψ := by
  obtain ⟨V,hVopen,hφV,c,R,_,hR,hdata⟩ :=
    exists_local_sourceCriticalRootRatio_uniformRealCenteredEnclosingCircle
      hp hp1 φ hφ n
  exact ⟨V,hVopen,hφV,c,R,hR,hdata⟩

end NLS.ZakharovShabat
