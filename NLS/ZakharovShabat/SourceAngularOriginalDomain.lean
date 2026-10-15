import NLS.ZakharovShabat.SourceLemma12_12
import NLS.ZakharovShabat.SourceAngularEndpointCommonDomain

/-!
# Section 13 on the retained original psi domain

The integration interface uses exactly the domain and root maps of Lemma
12.12. All endpoint spectral data follow from the preceding original
spectral results, at every complex source, without a further intersection.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceLemma12_12Data
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- The existing integration interface retains the exact original W and s. -/
theorem angular_extension (H : SourceLemma12_12Data hp hp1 W₀ W s) :
    SourcePsiSquaredGapComplexExtension hp hp1 W s := by
  obtain ⟨A,hW,hs⟩ := H.previous.previous.atlas
  subst W s
  let B := A.toSourcePsiComplexRootAtlas
  let D := A.toSourcePsiIsolatingComplexRootAtlas
  refine {
    toSourcePsiMidpointBoundComplexExtension := {
      toSourcePsiFactorMajorantComplexExtension := {
        toSourcePsiNormalizedComplexExtension := {
          toSourcePsiIsolatingComplexExtension := {
            analytic := B.analytic,
            real_agreement := B.eq_sourcePsiGapRoot_of_real,
            contour_zero := B.contour_zero,
            isolation := ?_
          },
          contour_orthogonality := fun ψ hψ => D.contour_orthogonality
            W₀ (Subset.refl _) H.previous.previous.psi.previous.psiIntegrand_joint ψ hψ
        },
        locally_uniform_factor_tail_majorants :=
          A.toSourcePsiFactorMajorantComplexRootAtlas.locally_uniform_factor_tail_majorants
      },
      locally_uniform_midpoint_lower_bounds :=
        A.toSourcePsiMidpointBoundComplexRootAtlas.locally_uniform_midpoint_lower_bounds
    },
    locally_uniform_squared_gap_offsets := A.locally_uniform_squared_gap_offsets
  }
  intro φ
  exact ⟨(B.localBranch φ).sourceRadius,(B.localBranch φ).sourceRadius_pos,
    D.cutoff φ,D.enlargement φ,D.enlargement_pos φ,D.enlargement_le φ,
    subset_iUnion B.sourceBall φ,D.clusters φ,D.disjoint φ,D.global_placement φ,D.filled_placement φ⟩

/-- The original spectral domain already contains all endpoint integration data. -/
theorem angular_endpoint_data (H : SourceLemma12_12Data hp hp1 W₀ W s)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (m : ℤ) :
    SourceAngularEndpointSpectralData hp hp1 ψ m := by
  have hψ₀ := H.previous.previous.subset hψ
  let H5 := H.previous.previous.psi.previous.quotients.roots
  have hroot := H5.joint m
  have heq : sourceStandardRootOmittedDomain hp hp1 ψ m =
      (fun z : ℂ => (z,ψ)) ⁻¹' sourceStandardRootOmittedJointDomain hp hp1 W₀ m := by
    ext z
    change (∀ k, k ≠ m → z ∉ sourcePeriodicSegment hp hp1 ψ k) ↔
      ψ ∈ W₀ ∧ (∀ k, k ≠ m → z ∉ sourcePeriodicSegment hp hp1 ψ k)
    exact ⟨fun hz => ⟨hψ₀,hz⟩,And.right⟩
  refine ⟨?_,H.previous.previous.psi.previous.previous.previous.segment_subset_omitted ψ hψ₀ m,?_⟩
  · rw [heq]
    exact hroot.1.preimage (continuous_id.prodMk continuous_const)
  · exact H5.spectral ψ hψ₀ m

end SourceLemma12_12Data
end NLS.ZakharovShabat
