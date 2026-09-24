import NLS.ZakharovShabat.SourceCriticalGapQuotientContinuity
import NLS.ZakharovShabat.SourceCriticalRootRatioContourHomotopy

/-!
# A gap-enclosing circle inside an isolating disc

An assigned isolating disc contains the entire selected periodic gap.
There is a smaller concentric closed disc that still contains that gap
in its interior. The smaller circle avoids every periodic gap segment,
so it is a valid contour for the full canonical-root quotient.
-/

noncomputable section
open Set Metric
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- There is a smaller concentric closed disc inside an assigned
isolating disc that still contains the selected gap in its interior. -/
theorem exists_sourcePeriodicSegment_enclosingCircle_within_isolatingDisc
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ ψ : CoeffPair p) (N : ℕ) (ε : ℝ)
    (n : ℤ)
    (hcluster : sourceSpectralCluster hp hp1 ψ n ⊆
      sourceIsolatingDisc hp hp1 φ N ε n) :
    ∃ c : ℂ, ∃ R : ℝ, 0 < R ∧
      sourcePeriodicSegment hp hp1 ψ n ⊆ ball c R ∧
      closedBall c R ⊆ sourceIsolatingDisc hp hp1 φ N ε n := by
  let c := sourceIsolatingCenter hp hp1 φ N n
  let R₀ := sourceIsolatingRadius hp hp1 φ N ε n
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  have hl : dist l c < R₀ := by
    have hmem := hcluster (show l ∈ sourceSpectralCluster hp hp1 ψ n from Or.inl rfl)
    rw [sourceIsolatingDisc_eq_ball] at hmem
    exact mem_ball.mp hmem
  have hr : dist r c < R₀ := by
    have hmem := hcluster
      (show r ∈ sourceSpectralCluster hp hp1 ψ n from Or.inr (Or.inl rfl))
    rw [sourceIsolatingDisc_eq_ball] at hmem
    exact mem_ball.mp hmem
  let d := max (dist l c) (dist r c)
  have hd : d < R₀ := max_lt hl hr
  let R := (d + R₀) / 2
  have hdR : d < R := by dsimp [R]; linarith
  have hRR₀ : R < R₀ := by dsimp [R]; linarith
  have hRpos : 0 < R := by
    have : 0 ≤ d := le_trans dist_nonneg (le_max_left _ _)
    linarith
  have hseg : sourcePeriodicSegment hp hp1 ψ n ⊆ ball c R := by
    change segment ℝ l r ⊆ ball c R
    apply (convex_ball c R).segment_subset
    · exact mem_ball.mpr (lt_of_le_of_lt (le_max_left _ _) hdR)
    · exact mem_ball.mpr (lt_of_le_of_lt (le_max_right _ _) hdR)
  refine ⟨c, R, hRpos, hseg, ?_⟩
  rw [sourceIsolatingDisc_eq_ball]
  exact closedBall_subset_ball hRR₀

/-- An enclosing circle avoids the selected gap by its inner-ball
condition and all other gaps by its filled-disc condition. -/
theorem sourceCanonicalRootDomain_of_enclosingCircle
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (n : ℤ)
    (c : ℂ) (R : ℝ)
    (hseg : sourcePeriodicSegment hp hp1 ψ n ⊆ ball c R)
    (hother : closedBall c R ⊆
      sourceStandardRootOmittedDomain hp hp1 ψ n) :
    sphere c R ⊆ sourceCanonicalRootDomain hp hp1 ψ := by
  intro z hz m
  by_cases hm : m = n
  · subst m
    intro hmem
    have hzball := hseg hmem
    have hzsphere := mem_sphere.mp hz
    have hzlt := mem_ball.mp hzball
    exact (ne_of_lt hzlt) hzsphere
  · exact (hother (sphere_subset_closedBall hz)) m hm

/-- An isolating disc supplies a genuine circular contour around its
selected gap, with a filled disc avoiding every other gap. -/
theorem exists_sourceCriticalRootRatio_enclosingCircle_of_isolating
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ ψ : CoeffPair p) (N : ℕ) (ε : ℝ)
    (hcluster : ∀ m : ℤ, sourceSpectralCluster hp hp1 ψ m ⊆
      sourceIsolatingDisc hp hp1 φ N ε m)
    (hdisjoint : ∀ i j : ℤ, i ≠ j →
      Disjoint (sourceIsolatingDisc hp hp1 φ N ε i)
        (sourceIsolatingDisc hp hp1 φ N ε j))
    (n : ℤ) :
    ∃ c : ℂ, ∃ R : ℝ, 0 < R ∧
      sourcePeriodicSegment hp hp1 ψ n ⊆ ball c R ∧
      closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 ψ n ∧
      sphere c R ⊆ sourceCanonicalRootDomain hp hp1 ψ := by
  obtain ⟨c, R, hRpos, hseg, hfilled⟩ :=
    exists_sourcePeriodicSegment_enclosingCircle_within_isolatingDisc
      hp hp1 φ ψ N ε n (hcluster n)
  have hother : closedBall c R ⊆
      sourceStandardRootOmittedDomain hp hp1 ψ n :=
    hfilled.trans (sourceIsolatingDisc_subset_omittedDomain
      hp hp1 φ ψ N ε hcluster hdisjoint n)
  exact ⟨c, R, hRpos, hseg, hother,
    sourceCanonicalRootDomain_of_enclosingCircle hp hp1 ψ n c R hseg hother⟩

/-- At any real-type source, every selected gap admits such a circle. -/
theorem exists_sourceCriticalRootRatio_enclosingCircle_of_realType
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ) :
    ∃ c : ℂ, ∃ R : ℝ, 0 < R ∧
      sourcePeriodicSegment hp hp1 ψ n ⊆ ball c R ∧
      closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 ψ n ∧
      sphere c R ⊆ sourceCanonicalRootDomain hp hp1 ψ := by
  obtain ⟨N, ε, _, _, U, _, _, hψU, hcluster, hdisjoint⟩ :=
    exists_local_source_connected_isolating_discs hp hp1 ψ hreal
  exact exists_sourceCriticalRootRatio_enclosingCircle_of_isolating
    hp hp1 ψ ψ N ε (hcluster ψ hψU) hdisjoint n

end NLS.ZakharovShabat
