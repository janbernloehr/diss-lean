import NLS.ZakharovShabat.SourceAngularOriginalEtaPaths

/-!
# The retained source domain and actual disks for Section 13

Every complex source has original isolating neighborhoods that contain
both the selected gaps and the Dirichlet terminals. The same W and s
support the integration interface, endpoint spectral data, and the
original-disk beta and eta path comparison theorems.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Actual original disks and terminal containment exist throughout the unchanged W. -/
theorem SourceLemma12_12Data.angular_original_disks
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W : Set (CoeffPair p)}
    {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
    (H : SourceLemma12_12Data hp hp1 W₀ W s) (ψ : CoeffPair p) (hψ : ψ ∈ W) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ ψ ∈ V ∧ V ⊆ W ∧
      ∃ D : ℤ → Set ℂ, ∃ c : ℝ, SourceIsolatingNeighborhoods hp hp1 V D c ∧
        ∀ χ ∈ V, ∀ m : ℤ, canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet χ m ∈ D m := by
  obtain ⟨U,hU,_,hψU,hUW,D,c,hD⟩ :=
    H.previous.previous.psi.previous.quotients.roots.roots.neighborhoods ψ (H.previous.previous.subset hψ)
  have hW : IsOpen W := by
    obtain ⟨A,hW,_⟩ := H.previous.previous.atlas
    exact hW ▸ A.toSourcePsiComplexRootAtlas.isOpen_domain
  refine ⟨U ∩ W,hU.inter hW,⟨hψU,hψ⟩,inter_subset_right,D,c,
    hD.toSourceIsolatingNeighborhoods.restrict_source inter_subset_left,?_⟩
  intro χ hχ m
  exact hD.cluster χ hχ.1 m (Or.inr (Or.inr (Or.inl rfl)))

/-- A simultaneous original circle family contains every Dirichlet terminal. -/
theorem SourceLemma12_12Data.angular_original_circles
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W : Set (CoeffPair p)}
    {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
    (H : SourceLemma12_12Data hp hp1 W₀ W s) (ψ : CoeffPair p) (hψ : ψ ∈ W) :
    ∃ P : (m : ℤ) → SourceCriticalRootPeriodCircle hp hp1 ψ m,
      ∀ m : ℤ, canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m ∈
        ball ((P m).center:ℂ) (P m).radius := by
  obtain ⟨V,_,hψV,_,D,c,hD,hμ⟩ := H.angular_original_disks ψ hψ
  choose a r hr he using hD.discs
  refine ⟨fun m => hD.periodCircle ψ hψV m (a m) (r m) (hr m) (he m),?_⟩
  intro m
  change canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m ∈ ball (a m:ℂ) (r m)
  rw [← he m]
  exact hμ ψ hψV m

/-- Section 13's integration domain retains all of Lemma 12.12 and the original source data. -/
theorem sourceSection13OriginalDomain (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W₀ : Set (CoeffPair p), IsOpen W₀ ∧ IsConnected W₀ ∧ realTypeSourceLocus p ⊆ W₀ ∧
      ∃ W : Set (CoeffPair p), IsOpen W ∧ IsSimplyConnected W ∧ realTypeSourceLocus p ⊆ W ∧
        ∃ s : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
          SourceLemma12_12Data hp hp1 W₀ W s ∧ SourcePsiSquaredGapComplexExtension hp hp1 W s ∧
          (∀ ψ ∈ W, ∀ m : ℤ, SourceAngularEndpointSpectralData hp hp1 ψ m) ∧
          ∀ ψ ∈ W, ∃ P : (m : ℤ) → SourceCriticalRootPeriodCircle hp hp1 ψ m,
            ∀ m : ℤ, canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m ∈
              ball ((P m).center:ℂ) (P m).radius := by
  obtain ⟨W₀,ho,hc,hr,W,hW,hs,hrW,s,H⟩ := sourceLemma12_12 hp hp1
  exact ⟨W₀,ho,hc,hr,W,hW,hs,hrW,s,H,H.angular_extension,H.angular_endpoint_data,H.angular_original_circles⟩

end NLS.ZakharovShabat
