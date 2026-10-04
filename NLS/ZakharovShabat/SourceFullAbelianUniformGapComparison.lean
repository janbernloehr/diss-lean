import NLS.ZakharovShabat.SourceFullAbelianGapComparison

/-! # A locally uniform reduction of Lemma 19.4 to deleted-factor errors

One source neighborhood and one positive constant control the comparison
on every closed complex gap. The remaining offset term is exactly the
gap magnitude times the actual critical squared-gap quotient; no gap
division is used and the quotient's full sequence norm is locally bounded.
-/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Locally uniform comparison for arbitrary nonnegative bounds on
`chi_j-1`. The constants are independent of the gap, side, angle, source
in the neighborhood, and the chosen compatible Cauchy chart. -/
theorem exists_local_uniform_sourceFullAbelian_gap_comparison
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∃ A : ℝ, 0 < A ∧ ∃ K : ℝ, 0 ≤ K ∧ ∀ ψ ∈ V,
        ‖sourceCriticalGapQuotient hp hp1 ψ‖ ≤ K ∧
        ∀ (W : Set (CoeffPair p)) (C : SourceFullAbelianUniformCauchyFamily hp hp1 W),
          ψ ∈ ball C.discs.source.val C.discs.sourceRadius →
          ∀ (j : ℤ) (E : ℝ), 0 ≤ E →
          (∀ z ∈ sourcePeriodicSegment hp hp1 ψ j,
            ‖sourceSingleRootQuotientJointProduct hp hp1 j
              (z,(canonicalCriticalDisplacement hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ),ψ))-1‖ ≤ E) →
          ∀ θ ∈ Icc (0:ℝ) Real.pi, ∀ upper : Bool,
            ‖C.gapBoundary j ψ θ upper-I*sourceStandardRootGapBoundary hp hp1 ψ j θ upper‖ ≤
              ‖sourcePeriodicGapDisplacement hp hp1 ψ j‖*
                (A*E+‖sourcePeriodicGapDisplacement hp hp1 ψ j‖*
                  ‖sourceCriticalGapQuotient hp hp1 ψ j‖)*Real.pi := by
  obtain ⟨Vd,hVd,hφd,A,hA,hd⟩ :=
    exists_local_uniform_sourceCriticalPoint_gap_distance_bound hp hp1 φ hφ
  obtain ⟨Vq,hVq,hφq,K,hK,hq⟩ := exists_local_uniform_sourceCriticalGapQuotient hp hp1 φ hφ
  refine ⟨Vd ∩ Vq,hVd.inter hVq,⟨hφd,hφq⟩,A,hA,K,hK,?_⟩
  intro ψ hψ
  refine ⟨(hq ψ hψ.2).1,?_⟩
  intro W C hψC j E hE he θ hθ upper
  have hb := C.gapBoundary_sub_root_norm_le_of_factor_error j ψ hψC
    (A*‖sourcePeriodicGapDisplacement hp hp1 ψ j‖) E
    (mul_nonneg hA.le (norm_nonneg _)) hE (hd ψ hψ.1 j)
    (by intro z hz; rw [norm_sourceCriticalRootRatioExtension_add_I]; exact he z hz) θ hθ upper
  have hoff : canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) j-
      sourceStandardRootMidpoint hp hp1 ψ j =
      (sourcePeriodicGapDisplacement hp hp1 ψ j)^2*sourceCriticalGapQuotient hp hp1 ψ j :=
    (hq ψ hψ.2).2 j
  rw [hoff,norm_mul,norm_pow] at hb
  convert hb using 1
  ring

end NLS.ZakharovShabat
