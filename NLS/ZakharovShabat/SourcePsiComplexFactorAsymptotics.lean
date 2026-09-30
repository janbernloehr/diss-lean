import NLS.ZakharovShabat.SourcePsiFactorMajorantComplexRootAtlas
import NLS.ZakharovShabat.SourcePsiLemma12_11

/-!
# Locally uniform chi tail asymptotics on the normalized psi domain

Construct the actual normalized analytic psi root family from the
atlas carrying chi majorants. The common open simply connected
neighborhood retains Lemmas 12.10 and 12.11, and at every complex
source its chi tail error has locally uniform lp majorants independent
of the deleted index. This supplies the tail form of (2.32); the
uniform midpoint lower bound and finite-head offset estimates of
Lemma 12.12 remain to be proved.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual normalized complex psi extension with locally uniform
chi tail majorants at every source, uniformly in the deleted index. -/
structure SourcePsiFactorMajorantComplexExtension (hp : p ≠ ⊤) (hp1 : 1 < p)
    (W : Set (CoeffPair p)) (s : (n : ℤ) → CoeffPair p → DeletedCoeff p n) : Prop
    extends SourcePsiNormalizedComplexExtension hp hp1 W s where
  locally_uniform_factor_tail_majorants : ∀ ψ ∈ W,
    ∃ V : Set (CoeffPair p), IsOpen V ∧ ψ ∈ V ∧ V ⊆ W ∧
      ∃ K : ℕ, ∃ C : ℝ, 0 ≤ C ∧
        ∀ χ ∈ V, ∀ n : ℤ, ∃ E : Coeff p, ‖E‖ ≤ C ∧
          ∀ m : ℤ, K ≤ m.natAbs → m ≠ n →
            ∀ z ∈ closedBall ((Real.pi : ℂ)*m) (Real.pi/8),
              ‖sourcePsiMidpointFilledRegularFactor hp hp1 n m (s n χ) χ z-I‖ ≤ ‖E m‖

/-- One common complex neighborhood has the actual analytic psi
family, exact normalization, assigned isolation, and locally uniform
tail form of (2.32) with a bound independent of the deleted index. -/
theorem exists_sourcePsi_normalized_complex_extension_with_tail_factor_majorants
    (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ U W : Set (CoeffPair p), SourceSpectralIsolationNeighborhood hp hp1 U ∧
      IsOpen W ∧ IsSimplyConnected W ∧ realTypeSourceLocus p ⊆ W ∧ W ⊆ U ∧
      ∃ s : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
        SourcePsiFactorMajorantComplexExtension hp hp1 W s := by
  obtain ⟨U,hU,hUconn,hreal,hgeometry⟩ := exists_global_source_isolating_neighborhood hp hp1
  obtain ⟨V,hV,_,hVreal,hdata⟩ := exists_global_sourcePsiContourIntegrand_jointAnalytic hp hp1
  obtain ⟨A⟩ := nonempty_sourcePsiFactorMajorantComplexRootAtlas hp hp1 (U ∩ V)
    (hU.inter hV) (fun φ hφ => ⟨hreal hφ,hVreal hφ⟩)
  let B := A.toSourcePsiComplexRootAtlas
  let D := A.toSourcePsiIsolatingComplexRootAtlas
  refine ⟨U,B.domain,⟨hU,hUconn,hreal,hgeometry⟩,B.isOpen_domain,
    B.isSimplyConnected_domain,B.realType_subset_domain,
    D.domain_subset.trans inter_subset_left,B.branch,{
      toSourcePsiNormalizedComplexExtension := {
        toSourcePsiIsolatingComplexExtension := {
          analytic := B.analytic,
          real_agreement := B.eq_sourcePsiGapRoot_of_real,
          contour_zero := B.contour_zero,
          isolation := ?_
        },
        contour_orthogonality := fun ψ hψ => D.contour_orthogonality V inter_subset_right hdata ψ hψ
      },
      locally_uniform_factor_tail_majorants := A.locally_uniform_factor_tail_majorants
    }⟩
  intro φ
  exact ⟨(B.localBranch φ).sourceRadius,(B.localBranch φ).sourceRadius_pos,
    D.cutoff φ,D.enlargement φ,D.enlargement_pos φ,D.enlargement_le φ,
    subset_iUnion B.sourceBall φ,D.clusters φ,D.disjoint φ,D.global_placement φ,D.filled_placement φ⟩

end NLS.ZakharovShabat
