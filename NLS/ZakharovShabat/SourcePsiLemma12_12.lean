import NLS.ZakharovShabat.SourcePsiSquaredGapComplexRootAtlas
import NLS.ZakharovShabat.SourcePsiComplexMidpointBounds

/-!
# Lemma 12.12 on one common normalized complex psi domain

The actual analytic psi root family has squared-gap lp offsets on
one common open simply connected complex neighborhood of the real
source locus. Their norm bound is uniform in the omitted index and
locally uniform at every complex source. Exact contour normalization,
assigned spectral isolation, chi majorants, and midpoint lower bounds
are retained. Filling the omitted root with its moving midpoint gives
the factorization at every index, including collapsed gaps, and the
literal p-power sum has the dissertation's locally uniform bound.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

structure SourcePsiSquaredGapComplexExtension (hp : p ≠ ⊤) (hp1 : 1 < p)
    (W : Set (CoeffPair p)) (s : (n : ℤ) → CoeffPair p → DeletedCoeff p n) : Prop
    extends SourcePsiMidpointBoundComplexExtension hp hp1 W s where
  locally_uniform_squared_gap_offsets : ∀ ψ ∈ W,
    ∃ V : Set (CoeffPair p), IsOpen V ∧ ψ ∈ V ∧ V ⊆ W ∧
      ∃ C : ℝ, 0 < C ∧ ∀ χ ∈ V, ∀ n : ℤ, ∃ α : Coeff p, α n = 0 ∧
        (∀ m, m ≠ n → displacedRoots (s n χ : Coeff p) m =
          sourceStandardRootMidpoint hp hp1 χ m+(sourcePeriodicGapDisplacement hp hp1 χ m)^2*α m) ∧
        ‖α‖ ≤ C

/-- Source-space Lemma 12.12 with the actual analytic root family,
exact normalization, isolation, and squared-gap lp offsets uniformly
in the omitted index and locally uniformly throughout one common
open simply connected complex neighborhood of all real sources. -/
theorem exists_sourcePsi_lemma12_12 (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ U W : Set (CoeffPair p), SourceSpectralIsolationNeighborhood hp hp1 U ∧
      IsOpen W ∧ IsSimplyConnected W ∧ realTypeSourceLocus p ⊆ W ∧ W ⊆ U ∧
      ∃ s : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
        SourcePsiSquaredGapComplexExtension hp hp1 W s := by
  obtain ⟨U,hU,hUconn,hreal,hgeometry⟩ := exists_global_source_isolating_neighborhood hp hp1
  obtain ⟨V,hV,_,hVreal,hdata⟩ := exists_global_sourcePsiContourIntegrand_jointAnalytic hp hp1
  obtain ⟨A⟩ := nonempty_sourcePsiSquaredGapComplexRootAtlas hp hp1 (U ∩ V)
    (hU.inter hV) (fun φ hφ => ⟨hreal hφ,hVreal hφ⟩)
  let B := A.toSourcePsiComplexRootAtlas
  let D := A.toSourcePsiIsolatingComplexRootAtlas
  refine ⟨U,B.domain,⟨hU,hUconn,hreal,hgeometry⟩,B.isOpen_domain,
    B.isSimplyConnected_domain,B.realType_subset_domain,
    D.domain_subset.trans inter_subset_left,B.branch,{
      toSourcePsiMidpointBoundComplexExtension := {
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
        locally_uniform_midpoint_lower_bounds :=
          A.toSourcePsiMidpointBoundComplexRootAtlas.locally_uniform_midpoint_lower_bounds
      },
      locally_uniform_squared_gap_offsets := A.locally_uniform_squared_gap_offsets
    }⟩
  intro φ
  exact ⟨(B.localBranch φ).sourceRadius,(B.localBranch φ).sourceRadius_pos,
    D.cutoff φ,D.enlargement φ,D.enlargement_pos φ,D.enlargement_le φ,
    subset_iUnion B.sourceBall φ,D.clusters φ,D.disjoint φ,D.global_placement φ,D.filled_placement φ⟩

/-- The dissertation's literal all-index factorization and p-power
sum estimate. The omitted root is filled with its moving midpoint;
the offset there is zero. The sum is explicitly summable, and one
positive bound works for all omitted indices on a neighborhood of
every complex source, also when selected gaps collapse. -/
theorem SourcePsiSquaredGapComplexExtension.locally_uniform_filled_offsets_power_sum
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 W s) (ψ : CoeffPair p) (hψ : ψ ∈ W) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ ψ ∈ V ∧ V ⊆ W ∧
      ∃ C : ℝ, 0 < C ∧ ∀ χ ∈ V, ∀ n : ℤ, ∃ α : Coeff p, α n = 0 ∧
        (∀ m, displacedRoots (sourcePsiFillDeletedRoot n (s n χ)
          (sourceStandardRootMidpoint hp hp1 χ n)) m =
            sourceStandardRootMidpoint hp hp1 χ m+(sourcePeriodicGapDisplacement hp hp1 χ m)^2*α m) ∧
        Summable (fun m : ℤ => ‖α m‖^p.toReal) ∧
        (∑' m : ℤ, ‖α m‖^p.toReal) ≤ C := by
  have hpr : 0 < p.toReal := ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans hp1)) hp
  obtain ⟨V,hV,hψV,hVW,L,hL,hbound⟩ := hs.locally_uniform_squared_gap_offsets ψ hψ
  refine ⟨V,hV,hψV,hVW,L^p.toReal,Real.rpow_pos_of_pos hL _,?_⟩
  intro χ hχ n
  obtain ⟨α,hαn,hfactor,hαnorm⟩ := hbound χ hχ n
  refine ⟨α,hαn,?_,(lp.memℓp α).summable hpr,?_⟩
  · intro m
    by_cases hmn : m = n
    · subst m
      rw [displacedRoots_sourcePsiFillDeletedRoot_same,hαn,mul_zero,add_zero]
    · rw [displacedRoots_sourcePsiFillDeletedRoot_other n m hmn]
      exact hfactor m hmn
  · rw [← lp.norm_rpow_eq_tsum hpr α]
    exact Real.rpow_le_rpow (norm_nonneg _) hαnorm hpr.le

end NLS.ZakharovShabat
