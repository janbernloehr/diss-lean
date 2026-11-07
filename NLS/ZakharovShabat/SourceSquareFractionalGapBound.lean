import NLS.ZakharovShabat.SourcePrimitiveFractionalGapBound
import NLS.ZakharovShabat.SourceFullAbelianSquareGapBound

/-! The ACTUAL filled square has a fractional error with TWO literal
gap factors, uniformly on each entire complex gap including collapse. -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat

theorem exists_local_sobolev_square_gap_bound
    (t : ℝ) (ht : 0≤t) (u : ℝ) (hu0 : 0≤u) (hu1 : u≤1) (hut : u≤t)
    (φ : realTypeSourceSubmodule 2) :
    let L := normalizedWeightedSourceCLM (p := 2) (sourceSobolevSpectralWeight t ht)
    ∃ T : Set (CoeffPair 2), IsOpen T ∧ φ.val∈T ∧ ∃ K : ℕ, ∃ M : ℝ, 0≤M ∧
      ∀ ψ∈T, ∀ (W : Set (CoeffPair 2))
        (C : SourceFullAbelianUniformCauchyFamily (by norm_num) (by norm_num) W),
        L ψ∈ball C.discs.source.val C.discs.sourceRadius →
        ∀ j : ℤ, K≤j.natAbs → ∀ z∈sourcePeriodicSegment (by norm_num) (by norm_num) (L ψ) j,
          Weight.sobolev u j*‖sourceFullAbelianSquare (by norm_num) (by norm_num) W j (z,L ψ)+
            sourceAngularSelectedPolynomial (by norm_num) (by norm_num) (L ψ) j z‖≤
              ‖sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (L ψ) j‖^2*M := by
  intro L
  obtain ⟨T,hT,hφT,K,M,hM,hprimitive⟩ := exists_local_sobolev_primitive_gap_bound t ht u hu0 hu1 hut φ
  refine ⟨T,hT,hφT,K,M*(M+1),mul_nonneg hM (by linarith),?_⟩
  intro ψ hψ W C hψC j hj z hz
  obtain ⟨θ,hθ,rfl⟩ := exists_sourcePeriodicSegment_cosine_parameter (by norm_num) (by norm_num) (L ψ) j z hz
  let γ := sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (L ψ)
  have hb := hprimitive ψ hψ W C hψC j hj θ hθ true
  have he : ‖C.gapBoundary j (L ψ) θ true-
      I*sourceStandardRootGapBoundary (by norm_num) (by norm_num) (L ψ) j θ true‖≤
        ‖γ j‖*(M/Weight.sobolev u j) := by
    rw [← mul_div_assoc]
    exact (le_div_iff₀ ((Weight.sobolev u).positive j)).mpr
      (by simpa only [mul_comm] using hb)
  have hs := C.fullSquare_add_polynomial_norm_le (L ψ) hψC j θ true (M/Weight.sobolev u j)
    (div_nonneg hM ((Weight.sobolev u).positive j).le) he
  have hweight : 1≤Weight.sobolev u j := by
    simpa only [Weight.sobolev_zero_apply] using Weight.sobolev_mono hu0 j
  have hw := NLS.weighted_square_gap_error_bound (Weight.sobolev u j) ‖γ j‖ M _ hweight hM hs
  simpa only [mul_assoc] using hw

end NLS.ZakharovShabat
