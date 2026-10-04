import NLS.ZakharovShabat.SourceAbelianMomentCircleVanishing
import NLS.ZakharovShabat.SourceStandardRootOmittedJointAnalytic

/-! # Moment vanishing near every real source

The omitted-product analyticity needed for cancellation is supplied by
its established joint analytic extension. One source neighborhood works
simultaneously for all gap indices, numerator coefficients, moment orders,
and circles between the inner and outer radii of the Cauchy family.
-/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Local, uniform versions of Lemma 20.1(iii–iv), with no additional
analyticity assumption on the canonical omitted product. -/
theorem exists_sourceAbelianMoment_local_vanishing (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ realTypeSourceLocus p ⊆ W ∧
      ∀ φ : realTypeSourceSubmodule p,
        ∃ C : SourceFullAbelianUniformCauchyFamily hp hp1 W, C.discs.source = φ ∧
        ∃ V : Set (CoeffPair p), IsOpen V ∧ φ.val ∈ V ∧
          V ⊆ ball C.discs.source.val C.discs.sourceRadius ∧
          ∀ ψ ∈ V, ∀ (n k : ℤ) (a : Coeff p) (R : ℝ),
            C.discs.inner k ≤ R → R < C.discs.outer k →
            (∀ l : ℕ, sourceAbelianMomentCircle hp hp1 W n k (2*l+1)
              a ψ (C.discs.center k) R = 0) ∧
            (canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) k = 0 →
              ∀ m : ℕ, sourceAbelianMomentCircle hp hp1 W n k (m+1)
                a ψ (C.discs.center k) R = 0) := by
  obtain ⟨W,hW,hreal,hfamilies⟩ := exists_sourceFullAbelianUniformCauchyFamilies hp hp1
  obtain ⟨O,hO,_,hrealO,hOdata⟩ := exists_global_source_analytic_omittedJointProduct hp hp1
  refine ⟨W,hW,hreal,?_⟩
  intro φ
  obtain ⟨C,hC⟩ := hfamilies φ
  refine ⟨C,hC,O ∩ ball C.discs.source.val C.discs.sourceRadius,
    hO.inter isOpen_ball,?_,inter_subset_right,?_⟩
  · refine ⟨hrealO φ.property,?_⟩
    rw [hC]
    exact mem_ball_self C.discs.sourceRadius_pos
  · intro ψ hψ n k a R hinner houter
    have hslice := sourceStandardRootOmittedProduct_analyticOnNhd_spectral hp hp1 k O
      (hOdata k).2.1 ψ hψ.1
    exact ⟨fun l => C.momentCircle_odd_eq_zero n k l a ψ hψ.2 hslice R hinner houter,
      fun hgap m => C.momentCircle_succ_eq_zero_of_collapsed n k m a ψ hψ.2 hslice hgap R hinner houter⟩

end NLS.ZakharovShabat
