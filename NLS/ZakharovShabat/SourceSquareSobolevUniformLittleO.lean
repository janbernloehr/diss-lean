import NLS.ZakharovShabat.SourcePrimitiveSobolevUniformLittleO
import NLS.ZakharovShabat.SourceFullAbelianSquareGapBound

/-! # Uniform little-o with two literal gap factors

The actual filled Abelian square has uniformly vanishing relative error
on one fixed complex Sobolev neighborhood, including every collapsed gap.
-/
noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat

theorem exists_local_sobolev_square_gap_uniform_littleO
    (t : ℝ) (ht : 0 < t) (ht1 : t < 1) (φ : realTypeSourceSubmodule 2) :
    let L := normalizedWeightedSourceCLM (p := 2) (sourceSobolevSpectralWeight t ht.le)
    ∃ T : Set (CoeffPair 2), IsOpen T ∧ φ.val ∈ T ∧
      ∀ ε > (0:ℝ), ∃ K : ℕ, ∀ ψ ∈ T, ∀ (W : Set (CoeffPair 2))
        (C : SourceFullAbelianUniformCauchyFamily (by norm_num) (by norm_num) W),
        L ψ ∈ ball C.discs.source.val C.discs.sourceRadius →
        ∀ j : ℤ, K ≤ j.natAbs →
          ∀ z ∈ sourcePeriodicSegment (by norm_num) (by norm_num) (L ψ) j,
            Weight.sobolev t j * ‖sourceFullAbelianSquare (by norm_num) (by norm_num) W j (z,L ψ)+
              sourceAngularSelectedPolynomial (by norm_num) (by norm_num) (L ψ) j z‖ ≤
                ‖sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (L ψ) j‖^2*ε := by
  intro L
  obtain ⟨T,hT,hφT,hprimitive⟩ := exists_local_sobolev_primitive_gap_uniform_littleO t ht ht1 φ
  refine ⟨T,hT,hφT,?_⟩
  intro ε hε
  let η := min 1 (ε/2)
  have hη : 0 < η := lt_min zero_lt_one (half_pos hε)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hηε : η ≤ ε/2 := min_le_right _ _
  have hsmall : η*(η+1) ≤ ε := by nlinarith
  obtain ⟨K,hK⟩ := hprimitive η hη
  refine ⟨K,?_⟩
  intro ψ hψ W C hψC j hj z hz
  obtain ⟨θ,hθ,rfl⟩ := exists_sourcePeriodicSegment_cosine_parameter (by norm_num) (by norm_num) (L ψ) j z hz
  let γ := sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (L ψ)
  have hb := hK ψ hψ W C hψC j hj θ hθ true
  have he : ‖C.gapBoundary j (L ψ) θ true-
      I*sourceStandardRootGapBoundary (by norm_num) (by norm_num) (L ψ) j θ true‖ ≤
        ‖γ j‖*(η/Weight.sobolev t j) := by
    rw [← mul_div_assoc]
    exact (le_div_iff₀ ((Weight.sobolev t).positive j)).mpr
      (by simpa only [mul_comm] using hb)
  have hs := C.fullSquare_add_polynomial_norm_le (L ψ) hψC j θ true (η/Weight.sobolev t j)
    (div_nonneg hη.le ((Weight.sobolev t).positive j).le) he
  have hweight : 1 ≤ Weight.sobolev t j := by
    simpa only [Weight.sobolev_zero_apply] using Weight.sobolev_mono ht.le j
  have hw := NLS.weighted_square_gap_error_bound (Weight.sobolev t j) ‖γ j‖ η _ hweight hη.le hs
  exact hw.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hsmall (sq_nonneg ‖γ j‖))

end NLS.ZakharovShabat
