import NLS.ZakharovShabat.SourcePsiMidpointBoundComplexRootAtlas
import NLS.ZakharovShabat.SourcePsiComplexFactorAsymptotics

/-!
# Uniform midpoint lower bounds on the normalized complex psi domain

The actual normalized analytic psi family can be constructed on a
common open simply connected neighborhood carrying both chi tail
majorants and positive chi midpoint lower bounds, locally uniformly
at every complex source and independently of both indices. The
subsequent actual tail and finite-head offset modules use these
bounds in the lp assembly of SourcePsiLemma12_12.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual normalized complex psi extension with both the tail
factor majorants and locally uniform positive midpoint lower bounds. -/
structure SourcePsiMidpointBoundComplexExtension (hp : p ≠ ⊤) (hp1 : 1 < p)
    (W : Set (CoeffPair p)) (s : (n : ℤ) → CoeffPair p → DeletedCoeff p n) : Prop
    extends SourcePsiFactorMajorantComplexExtension hp hp1 W s where
  locally_uniform_midpoint_lower_bounds : ∀ ψ ∈ W,
    ∃ V : Set (CoeffPair p), IsOpen V ∧ ψ ∈ V ∧ V ⊆ W ∧
      ∃ C : ℝ, 0 < C ∧ ∀ χ ∈ V, ∀ n m : ℤ, m ≠ n →
        C ≤ ‖sourcePsiMidpointFilledRegularFactor hp hp1 n m (s n χ) χ
          (sourceStandardRootMidpoint hp hp1 χ m)‖

/-- A common open simply connected complex neighborhood preserves
the analytic psi roots, exact contour normalization, assigned root
isolation, uniform chi tail majorants, and positive midpoint bounds
for all omitted and retained indices, locally at every complex source. -/
theorem exists_sourcePsi_normalized_complex_extension_with_uniform_midpoint_bounds
    (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ U W : Set (CoeffPair p), SourceSpectralIsolationNeighborhood hp hp1 U ∧
      IsOpen W ∧ IsSimplyConnected W ∧ realTypeSourceLocus p ⊆ W ∧ W ⊆ U ∧
      ∃ s : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
        SourcePsiMidpointBoundComplexExtension hp hp1 W s := by
  obtain ⟨U,hU,hUconn,hreal,hgeometry⟩ := exists_global_source_isolating_neighborhood hp hp1
  obtain ⟨V,hV,_,hVreal,hdata⟩ := exists_global_sourcePsiContourIntegrand_jointAnalytic hp hp1
  obtain ⟨A⟩ := nonempty_sourcePsiMidpointBoundComplexRootAtlas hp hp1 (U ∩ V)
    (hU.inter hV) (fun φ hφ => ⟨hreal hφ,hVreal hφ⟩)
  let B := A.toSourcePsiComplexRootAtlas
  let D := A.toSourcePsiIsolatingComplexRootAtlas
  refine ⟨U,B.domain,⟨hU,hUconn,hreal,hgeometry⟩,B.isOpen_domain,
    B.isSimplyConnected_domain,B.realType_subset_domain,
    D.domain_subset.trans inter_subset_left,B.branch,{
      toSourcePsiFactorMajorantComplexExtension := {
        toSourcePsiNormalizedComplexExtension := {
          toSourcePsiIsolatingComplexExtension := {
            analytic := B.analytic,
            real_agreement := B.eq_sourcePsiGapRoot_of_real,
            contour_zero := B.contour_zero,
            isolation := ?_
          },
          contour_orthogonality := fun ψ hψ => D.contour_orthogonality V inter_subset_right hdata ψ hψ
        },
        locally_uniform_factor_tail_majorants :=
          A.toSourcePsiFactorMajorantComplexRootAtlas.locally_uniform_factor_tail_majorants
      },
      locally_uniform_midpoint_lower_bounds := A.locally_uniform_midpoint_lower_bounds
    }⟩
  intro φ
  exact ⟨(B.localBranch φ).sourceRadius,(B.localBranch φ).sourceRadius_pos,
    D.cutoff φ,D.enlargement φ,D.enlargement_pos φ,D.enlargement_le φ,
    subset_iUnion B.sourceBall φ,D.clusters φ,D.disjoint φ,D.global_placement φ,D.filled_placement φ⟩

end NLS.ZakharovShabat
