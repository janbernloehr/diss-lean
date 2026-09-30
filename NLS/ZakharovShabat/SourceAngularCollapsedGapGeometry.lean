import NLS.ZakharovShabat.SourceAngularCollapsedPathIntegral
import NLS.ZakharovShabat.SourceIsolatingContourGeometry

/-!
# Collapsed-gap angular integrals in the full assigned disc

A collapsed selected gap is exactly its midpoint singleton. Every
other gap is excluded by assigned isolation, so an admissible path
inside the assigned disc needs only to avoid the midpoint in its
interior. The removable off-diagonal integrand gives path independence
on the whole disc, including paths with that midpoint as an endpoint.
-/

noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal unitInterval
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem sourcePeriodicSegment_eq_singleton_of_collapsed_gap
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (m : ℤ)
    (hgap : sourcePeriodicGapDisplacement hp hp1 ψ m = 0) :
    sourcePeriodicSegment hp hp1 ψ m = {sourceStandardRootMidpoint hp hp1 ψ m} := by
  have hr : canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m =
      canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m := by
    apply sub_eq_zero.mp
    simpa only [sourcePeriodicGapDisplacement_apply,canonicalPeriodicGap] using hgap
  have hτ : sourceStandardRootMidpoint hp hp1 ψ m =
      canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m := by
    unfold sourceStandardRootMidpoint canonicalPeriodicMidpoint
    rw [hr]
    ring
  simp only [sourcePeriodicSegment,hr,segment_same,hτ]

theorem mem_sourceCanonicalRootDomain_of_collapsed_gap
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (m : ℤ)
    (hgap : sourcePeriodicGapDisplacement hp hp1 ψ m = 0) (z : ℂ)
    (hz : z ∈ sourceStandardRootOmittedDomain hp hp1 ψ m)
    (hzt : z ≠ sourceStandardRootMidpoint hp hp1 ψ m) :
    z ∈ sourceCanonicalRootDomain hp hp1 ψ := by
  intro k
  by_cases hkm : k = m
  · subst k
    rw [sourcePeriodicSegment_eq_singleton_of_collapsed_gap hp hp1 ψ m hgap]
    simpa only [mem_singleton_iff] using hzt
  · exact hz k hkm

/-- Real interlacing puts the Dirichlet terminal at the collapsed
endpoint. Complex sources are not asserted to have this property. -/
theorem sourceDirichletRoot_eq_midpoint_of_real_collapsed_gap
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p)
    (hreal : IsRealType (CoeffPair.toMax p ψ)) (m : ℤ)
    (hgap : sourcePeriodicGapDisplacement hp hp1 ψ m = 0) :
    canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m = sourceStandardRootMidpoint hp hp1 ψ m := by
  have hμgap := canonicalPeriodOneBoundaryRoots_mem_gap hp hp1 .dirichlet ψ hreal m
  have hr : canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m =
      canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m := by
    apply sub_eq_zero.mp
    simpa only [sourcePeriodicGapDisplacement_apply,canonicalPeriodicGap] using hgap
  rw [hr] at hμgap
  have hμl : canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m =
      canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m := by
    apply Complex.ext
    · exact le_antisymm hμgap.2 hμgap.1
    · rw [canonicalPeriodOneBoundaryRoots_im_eq_zero hp hp1 .dirichlet ψ hreal m,
        sourceSpectralCluster_im_eq_zero hp hp1 ψ hreal m (Or.inl rfl)]
  rw [hμl]
  unfold sourceStandardRootMidpoint canonicalPeriodicMidpoint
  rw [hr]
  ring

namespace SourcePsiSquaredGapComplexExtension
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- Any two C¹ admissible paths in the entire assigned collapsed-gap
disc have the same actual off-diagonal canonical-sheet integral. -/
theorem angular_collapsed_pathIntegral_eq_of_assigned_disc
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 W s)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (n m : ℤ) (hmn : m ≠ n)
    (hgap : sourcePeriodicGapDisplacement hp hp1 ψ m = 0)
    (hdata : SourceAngularEndpointSpectralData hp hp1 ψ m)
    (φ : CoeffPair p) (N : ℕ) (ε : ℝ)
    (hclusters : ∀ k, sourceSpectralCluster hp hp1 ψ k ⊆ sourceIsolatingDisc hp hp1 φ N ε k)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint
      (sourceIsolatingDisc hp hp1 φ N ε i) (sourceIsolatingDisc hp hp1 φ N ε j))
    {a b : ℂ} (γ₁ γ₂ : Path a b)
    (hγ₁ : ContDiffOn ℝ 1 γ₁.extend (Icc 0 1)) (hγ₂ : ContDiffOn ℝ 1 γ₂.extend (Icc 0 1))
    (hγ₁D : ∀ t : I, γ₁ t ∈ sourceIsolatingDisc hp hp1 φ N ε m)
    (hγ₂D : ∀ t : I, γ₂ t ∈ sourceIsolatingDisc hp hp1 φ N ε m)
    (havoid₁ : ∀ t ∈ Ioo (0:ℝ) 1, γ₁.extend t ≠ sourceStandardRootMidpoint hp hp1 ψ m)
    (havoid₂ : ∀ t ∈ Ioo (0:ℝ) 1, γ₂.extend t ≠ sourceStandardRootMidpoint hp hp1 ψ m) :
    sourceAngularPathIntegral n s (fun t => sourceCanonicalRoot hp hp1 t.2 t.1) ψ γ₁ =
      sourceAngularPathIntegral n s (fun t => sourceCanonicalRoot hp hp1 t.2 t.1) ψ γ₂ := by
  have hTD := sourceIsolatingDisc_subset_omittedDomain hp hp1 φ ψ N ε hclusters hdisjoint m
  have hconv : Convex ℝ (sourceIsolatingDisc hp hp1 φ N ε m) := by
    rw [sourceIsolatingDisc_eq_ball]
    exact convex_ball _ _
  apply hs.angular_collapsed_pathIntegral_eq_of_convex_paths ψ hψ n m hmn hgap hdata
    _ hTD hconv (isOpen_sourceIsolatingDisc hp hp1 φ N ε m)
    γ₁ γ₂ hγ₁ hγ₂ hγ₁D hγ₂D
  · intro t ht
    apply mem_sourceCanonicalRootDomain_of_collapsed_gap hp hp1 ψ m hgap _ _ (havoid₁ t ht)
    apply hTD
    simpa only [Path.extend_apply γ₁ (Ioo_subset_Icc_self ht)] using hγ₁D ⟨t,Ioo_subset_Icc_self ht⟩
  · intro t ht
    apply mem_sourceCanonicalRootDomain_of_collapsed_gap hp hp1 ψ m hgap _ _ (havoid₂ t ht)
    apply hTD
    simpa only [Path.extend_apply γ₂ (Ioo_subset_Icc_self ht)] using hγ₂D ⟨t,Ioo_subset_Icc_self ht⟩

/-- Admissible loops in the assigned collapsed-gap disc have zero
actual off-diagonal integral, even when based at its midpoint. -/
theorem angular_collapsed_loop_integral_eq_zero_of_assigned_disc
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 W s)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (n m : ℤ) (hmn : m ≠ n)
    (hgap : sourcePeriodicGapDisplacement hp hp1 ψ m = 0)
    (hdata : SourceAngularEndpointSpectralData hp hp1 ψ m)
    (φ : CoeffPair p) (N : ℕ) (ε : ℝ)
    (hclusters : ∀ k, sourceSpectralCluster hp hp1 ψ k ⊆ sourceIsolatingDisc hp hp1 φ N ε k)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint
      (sourceIsolatingDisc hp hp1 φ N ε i) (sourceIsolatingDisc hp hp1 φ N ε j))
    {a : ℂ} (γ : Path a a) (hγ : ContDiffOn ℝ 1 γ.extend (Icc 0 1))
    (hγD : ∀ t : I, γ t ∈ sourceIsolatingDisc hp hp1 φ N ε m)
    (havoid : ∀ t ∈ Ioo (0:ℝ) 1, γ.extend t ≠ sourceStandardRootMidpoint hp hp1 ψ m) :
    sourceAngularPathIntegral n s (fun t => sourceCanonicalRoot hp hp1 t.2 t.1) ψ γ = 0 := by
  have hTD := sourceIsolatingDisc_subset_omittedDomain hp hp1 φ ψ N ε hclusters hdisjoint m
  have hconv : Convex ℝ (sourceIsolatingDisc hp hp1 φ N ε m) := by
    rw [sourceIsolatingDisc_eq_ball]
    exact convex_ball _ _
  apply hs.angular_collapsed_loop_integral_eq_zero ψ hψ n m hmn hgap hdata
    _ hTD hconv (isOpen_sourceIsolatingDisc hp hp1 φ N ε m) γ hγ hγD
  intro t ht
  apply mem_sourceCanonicalRootDomain_of_collapsed_gap hp hp1 ψ m hgap _ _ (havoid t ht)
  apply hTD
  simpa only [Path.extend_apply γ (Ioo_subset_Icc_self ht)] using hγD ⟨t,Ioo_subset_Icc_self ht⟩

/-- At a real collapsed gap, the Dirichlet terminal equals the starting
endpoint. Every admissible off-diagonal angular integral therefore
vanishes on both choices of the canonical spectral sheet. -/
theorem angular_real_collapsed_dirichlet_integral_eq_zero
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 W s)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n m : ℤ) (hmn : m ≠ n) (hgap : sourcePeriodicGapDisplacement hp hp1 ψ m = 0)
    (hdata : SourceAngularEndpointSpectralData hp hp1 ψ m)
    (φ : CoeffPair p) (N : ℕ) (ε : ℝ)
    (hclusters : ∀ k, sourceSpectralCluster hp hp1 ψ k ⊆ sourceIsolatingDisc hp hp1 φ N ε k)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint
      (sourceIsolatingDisc hp hp1 φ N ε i) (sourceIsolatingDisc hp hp1 φ N ε j))
    (γ : Path (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m)
      (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m))
    (hγ : ContDiffOn ℝ 1 γ.extend (Icc 0 1))
    (hγD : ∀ t : I, γ t ∈ sourceIsolatingDisc hp hp1 φ N ε m)
    (havoid : ∀ t ∈ Ioo (0:ℝ) 1, γ.extend t ≠ sourceStandardRootMidpoint hp hp1 ψ m) :
    sourceAngularPathIntegral n s (fun t => sourceCanonicalRoot hp hp1 t.2 t.1) ψ γ = 0 ∧
      sourceAngularPathIntegral n s (fun t => -sourceCanonicalRoot hp hp1 t.2 t.1) ψ γ = 0 := by
  have hlτ : canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m =
      sourceStandardRootMidpoint hp hp1 ψ m := by
    have hl : canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m ∈
        sourcePeriodicSegment hp hp1 ψ m := left_mem_segment ℝ _ _
    rw [sourcePeriodicSegment_eq_singleton_of_collapsed_gap hp hp1 ψ m hgap] at hl
    exact hl
  have hμl := (sourceDirichletRoot_eq_midpoint_of_real_collapsed_gap hp hp1 ψ hreal m hgap).trans hlτ.symm
  have hzero := hs.angular_collapsed_loop_integral_eq_zero_of_assigned_disc
    ψ hψ n m hmn hgap hdata φ N ε hclusters hdisjoint (γ.cast rfl hμl.symm) hγ hγD havoid
  have hcanonical : sourceAngularPathIntegral n s (fun t => sourceCanonicalRoot hp hp1 t.2 t.1) ψ γ = 0 := by
    simpa only [sourceAngularPathIntegral,curveIntegral_cast] using hzero
  exact ⟨hcanonical,by rw [sourceAngularPathIntegral_neg_sheet,hcanonical,neg_zero]⟩

end SourcePsiSquaredGapComplexExtension
end NLS.ZakharovShabat
