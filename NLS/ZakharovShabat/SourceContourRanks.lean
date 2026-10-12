import NLS.FunctionalAnalysis.ConjugatedRanges
import NLS.ZakharovShabat.SourceParityRestriction
/-! # Original-norm contour ranks and their parity components

Linear range equivalences connect the actual source contour integrals to
the established coefficient-space projectors. The actual typed parity
restrictions have the ranks of the corresponding ambient intersections.
-/
noncomputable section
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A typed restriction's range is isometrically the ambient range in that parity. -/
def sourceParityCompressionRangeEquiv (r : ℤ) (A : CoeffPair p →L[ℂ] CoeffPair p)
    (hA : Commute (sourceParityProjection r) A) (hAA : IsIdempotentElem A) :
    (sourceParityCompression r A).range ≃ₗᵢ[ℂ] ↥(A.range ⊓ sourceParitySubspace r) where
  toFun x := ⟨x.val.val, (mem_range_sourceParityCompression_iff r A hA hAA x.val).mp x.property,
    x.val.property⟩
  invFun x := ⟨⟨x.val,x.property.2⟩,
    (mem_range_sourceParityCompression_iff r A hA hAA ⟨x.val,x.property.2⟩).mpr x.property.1⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' _ := rfl

theorem finrank_range_sourceParityCompression (r : ℤ) (A : CoeffPair p →L[ℂ] CoeffPair p)
    (hA : Commute (sourceParityProjection r) A) (hAA : IsIdempotentElem A) :
    Module.finrank ℂ (sourceParityCompression r A).range =
      Module.finrank ℂ ↥(A.range ⊓ sourceParitySubspace r) :=
  (sourceParityCompressionRangeEquiv r A hA hAA).toLinearEquiv.finrank_eq

theorem finrank_range_sourceResolventCircleIntegral (hp : p ≠ ⊤) (φ : CoeffPair p)
    (c : ℂ) (R : ℝ) (hR : 0 ≤ R) (hc : Metric.sphere c R ⊆ sourceResolventSet hp φ) :
    Module.finrank ℂ (sourceResolventCircleIntegral hp φ c R).range =
      Module.finrank ℂ (resolventCircleIntegral hp (CoeffPair.toMax p φ) c R).range := by
  rw [sourceResolventCircleIntegral_eq_conj hp φ c R hR hc]
  exact (ConjugatedRanges.rangeEquiv (CoeffPair.toMax p) _).finrank_eq

theorem finrank_range_sourceCentralRectangleIntegral (hp : p ≠ ⊤) (φ : CoeffPair p) (N : ℕ)
    (hc : centralRectangleBoundary N ⊆ sourceResolventSet hp φ) :
    Module.finrank ℂ (sourceCentralRectangleIntegral hp φ N).range =
      Module.finrank ℂ (centralSpectralProjection hp (CoeffPair.toMax p φ) N).range := by
  rw [sourceCentralRectangleIntegral_eq_conj hp φ N hc,
    centralRectangleIntegral_eq_centralSpectralProjection hp _ N (by rwa [sourceResolventSet_eq] at hc)]
  exact (ConjugatedRanges.rangeEquiv (CoeffPair.toMax p) _).finrank_eq

theorem finrank_range_sourceParityCircleProjection (hp : p ≠ ⊤) (φ : CoeffPair p)
    (hφ : φ ∈ sourceParitySubspace 0) (c : ℂ) (R : ℝ) (r : ℤ) (hR : 0 ≤ R)
    (hc : Metric.sphere c R ⊆ sourceResolventSet hp φ) :
    Module.finrank ℂ (sourceParityCircleProjection hp φ c R r).range =
      Module.finrank ℂ ↥((resolventCircleIntegral hp (CoeffPair.toMax p φ) c R).range ⊓ pairParitySubspace r) := by
  change Module.finrank ℂ (sourceParityCompression r (sourceResolventCircleIntegral hp φ c R)).range = _
  rw [finrank_range_sourceParityCompression r _
    (sourceParityProjection_commute_circleIntegral hp φ hφ r c R hR hc)
    (sourceResolventCircleIntegral_idempotent hp φ c R hR hc),
    sourceResolventCircleIntegral_eq_conj hp φ c R hR hc]
  exact (ConjugatedRanges.rangeInfEquiv (CoeffPair.toMax p) _ (pairParitySubspace r)).finrank_eq

theorem finrank_range_sourceParityCentralProjection (hp : p ≠ ⊤) (φ : CoeffPair p)
    (hφ : φ ∈ sourceParitySubspace 0) (N : ℕ) (r : ℤ)
    (hc : centralRectangleBoundary N ⊆ sourceResolventSet hp φ) :
    Module.finrank ℂ (sourceParityCentralProjection hp φ N r).range =
      Module.finrank ℂ ↥((centralSpectralProjection hp (CoeffPair.toMax p φ) N).range ⊓ pairParitySubspace r) := by
  change Module.finrank ℂ (sourceParityCompression r (sourceCentralRectangleIntegral hp φ N)).range = _
  rw [finrank_range_sourceParityCompression r _
    (sourceParityProjection_commute_centralIntegral hp φ hφ r N hc)
    (sourceCentralRectangleIntegral_idempotent hp φ N hc),
    sourceCentralRectangleIntegral_eq_conj hp φ N hc,
    centralRectangleIntegral_eq_centralSpectralProjection hp _ N (by rwa [sourceResolventSet_eq] at hc)]
  exact (ConjugatedRanges.rangeInfEquiv (CoeffPair.toMax p) _ (pairParitySubspace r)).finrank_eq

/-- Only the residue modulo two determines a parity subspace. -/
theorem pairParitySubspace_eq_of_mod_eq (n r : ℤ) (h : n%2 = r%2) :
    pairParitySubspace (p := p) n = pairParitySubspace r := by
  ext a
  simp only [mem_pairParitySubspace,Coeff.mem_paritySubspace,h]

/-- Distinct parities have trivial intersection. -/
theorem disjoint_pairParitySubspaces_of_mod_ne (n r : ℤ) (h : n%2 ≠ r%2) :
    Disjoint (pairParitySubspace (p := p) n) (pairParitySubspace r) := by
  apply Submodule.disjoint_def.mpr
  intro a ha hb
  simp only [mem_pairParitySubspace,Coeff.mem_paritySubspace] at ha hb
  apply Prod.ext
  · ext k
    by_cases hk : k%2 = n%2
    · exact hb.1 k (by omega)
    · exact ha.1 k hk
  · ext k
    by_cases hk : k%2 = n%2
    · exact hb.2 k (by omega)
    · exact ha.2 k hk

/-- A subspace supported in one parity has full rank in that parity and rank zero in the other. -/
theorem finrank_inf_pairParitySubspace_of_le (S : Submodule ℂ (PairSpace p)) (n r : ℤ)
    (hS : S ≤ pairParitySubspace n) :
    Module.finrank ℂ ↥(S ⊓ pairParitySubspace r) =
      if n%2 = r%2 then Module.finrank ℂ S else 0 := by
  split_ifs with h
  · rw [← pairParitySubspace_eq_of_mod_eq n r h,inf_eq_left.mpr hS]
  · rw [disjoint_iff.mp ((disjoint_pairParitySubspaces_of_mod_ne n r h).mono_left hS)]
    simp

end NLS.ZakharovShabat
