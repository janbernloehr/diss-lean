import NLS.ZakharovShabat.SourceAbelianMomentCosineNeighborhood

/-! # Common spectral regularity of all moment numerators

One source neighborhood makes every filled even numerator analytic across
its selected gap. The domain and gap separation are independent of the
numerator input and of the moment order.
-/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceAbelianMomentAtlas
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
variable {W : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- A common almost-real neighborhood supports all regular numerators,
with the selected complex segment avoiding every other selected segment. -/
theorem exists_almostReal_evenNumerator_analytic
    (A : SourceAbelianMomentAtlas hp hp1 W s) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ realTypeSourceLocus p ⊆ U ∧ U ⊆ A.domain ∧
      ∀ ψ ∈ U,
        (∀ k : ℤ, sourcePeriodicSegment hp hp1 ψ k ⊆ sourceStandardRootOmittedDomain hp hp1 ψ k) ∧
        ∀ (n k : ℤ) (m : ℕ) (a : Coeff p),
          AnalyticOnNhd ℂ (sourceAbelianMomentEvenNumerator hp hp1 W n k m a ψ)
            (sourceStandardRootOmittedDomain hp hp1 ψ k) := by
  obtain ⟨W',_,_,hfamilies⟩ := exists_sourceFullAbelianUniformCauchyFamilies hp hp1
  choose C hC using hfamilies
  obtain ⟨O,hO,_,hrealO,hproduct⟩ := exists_global_source_analytic_omittedJointProduct hp hp1
  let T (φ : realTypeSourceSubmodule p) : Set (CoeffPair p) :=
    ball (C φ).discs.source.val (C φ).discs.sourceRadius ∩
      (A.sourceBall ⟨φ.val,φ.property⟩ ∩ O)
  have hT (φ : realTypeSourceSubmodule p) : IsOpen (T φ) := isOpen_ball.inter (isOpen_ball.inter hO)
  have hφT (φ : realTypeSourceSubmodule p) : φ.val ∈ T φ := by
    refine ⟨?_,mem_ball_self (A.localChart ⟨φ.val,φ.property⟩).radius_pos,hrealO φ.property⟩
    rw [hC]
    exact mem_ball_self (C φ).discs.sourceRadius_pos
  let U : Set (CoeffPair p) := ⋃ φ : realTypeSourceSubmodule p, T φ
  refine ⟨U,isOpen_iUnion hT,fun ψ hψ => mem_iUnion.mpr ⟨⟨ψ,hψ⟩,hφT ⟨ψ,hψ⟩⟩,?_,?_⟩
  · intro ψ hψ
    obtain ⟨φ,hφ⟩ := mem_iUnion.mp hψ
    exact mem_iUnion.mpr ⟨⟨φ.val,φ.property⟩,hφ.2.1⟩
  · intro ψ hψ
    obtain ⟨φ,hφ⟩ := mem_iUnion.mp hψ
    refine ⟨fun k z hz => (C φ).discs.avoids_other ψ hφ.1 k
      (ball_subset_closedBall ((C φ).segment_subset_outer k ψ hφ.1 hz)),?_⟩
    intro n k m a
    obtain ⟨D⟩ := (A.localChart ⟨φ.val,φ.property⟩).charts ψ hφ.2.1
    obtain ⟨E⟩ := (C φ).charts ψ hφ.1
    have hP := sourceStandardRootOmittedProduct_analyticOnNhd_spectral hp hp1 k O
      (hproduct k).2.1 ψ hφ.2.2
    have he : sourceAbelianMomentEvenNumerator hp hp1 W n k m a ψ =
        sourceAbelianMomentEvenNumerator hp hp1 W' n k m a ψ := by
      funext z
      unfold sourceAbelianMomentEvenNumerator
      rw [sourceFullAbelianSquare_independent_neighborhood D E]
    rw [he]
    exact (C φ).evenNumerator_analytic ψ hφ.1 n k m a hP

end NLS.ZakharovShabat.SourceAbelianMomentAtlas
