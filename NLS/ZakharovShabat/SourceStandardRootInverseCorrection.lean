import NLS.ZakharovShabat.SourceNormalizedActionCircleCorrectionBound
import NLS.ZakharovShabat.SourcePsiNearFreeGapGeometry

/-!
# Reciprocal standard-root correction away from a complex gap

The inverse selected standard root differs from its collapsed-gap
kernel by a term proportional to the squared gap. This estimate will
allow psi contour bounds without assuming the gap is real.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Away from the midpoint, a small complex squared gap changes the
inverse standard root by at most a cubic-pole correction. -/
theorem norm_normalizedStandardRoot_inv_sub_zeroGap_inv_le
    (τ q z : ℂ) (hτ : τ ≠ z)
    (hq : ‖q‖ ≤ ‖τ-z‖^2) :
    ‖(normalizedStandardRoot τ q z)⁻¹ - (τ-z)⁻¹‖ ≤
      ‖q‖/(2*‖τ-z‖^3) := by
  let d : ℂ := τ-z
  let w : ℂ := normalizedStandardRoot τ q z
  let D : ℝ := ‖d‖
  let W : ℝ := ‖w‖
  let Q : ℝ := ‖q‖
  have hd : d ≠ 0 := sub_ne_zero.mpr hτ
  have hD : 0 < D := norm_pos_iff.mpr hd
  have hWbound : D/2 ≤ W :=
    (normalizedStandardRoot_denominator_lower_bounds τ q z hτ hq).1
  have hW : 0 < W := by linarith
  have hw : w ≠ 0 := norm_pos_iff.mp hW
  have hdev : ‖d-w‖ ≤ Q/(4*D) := by
    have h := norm_normalizedStandardRoot_sub_zeroGap_le τ q z hτ
    change ‖w-d‖ ≤ Q/(4*D) at h
    simpa only [norm_sub_rev] using h
  have hdiff : w⁻¹-d⁻¹ = (d-w)/(w*d) := by
    field_simp [hw,hd]
  rw [hdiff,norm_div,norm_mul]
  change ‖d-w‖/(W*D) ≤ Q/(2*D^3)
  have hWD : 0 < W*D := mul_pos hW hD
  have hD3 : 0 < 2*D^3 := by positivity
  apply (div_le_div_iff₀ hWD hD3).mpr
  have hdev' : 4*D*‖d-w‖ ≤ Q := by
    have h := (le_div_iff₀ (by positivity : 0 < 4*D)).mp hdev
    nlinarith
  have hDle : D ≤ 2*W := by linarith
  have hQ : 0 ≤ Q := norm_nonneg q
  have hmult := mul_le_mul_of_nonneg_left hDle hQ
  nlinarith [mul_nonneg hD.le (sq_nonneg D)]

/-- A fixed positive spectral separation gives a bound with a
uniform constant, independent of the gap midpoint and contour point. -/
theorem norm_normalizedStandardRoot_inv_sub_zeroGap_inv_le_of_separation
    (τ q z : ℂ) (a : ℝ) (ha : 0 < a)
    (hsep : a ≤ ‖τ-z‖) (hq : ‖q‖ ≤ a^2) :
    ‖(normalizedStandardRoot τ q z)⁻¹ - (τ-z)⁻¹‖ ≤
      ‖q‖/(2*a^3) := by
  have hτ : τ ≠ z := sub_ne_zero.mp
    (norm_pos_iff.mp (ha.trans_le hsep))
  have hq' : ‖q‖ ≤ ‖τ-z‖^2 :=
    hq.trans (pow_le_pow_left₀ ha.le hsep 2)
  have hmain := norm_normalizedStandardRoot_inv_sub_zeroGap_inv_le
    τ q z hτ hq'
  apply hmain.trans
  apply div_le_div_of_nonneg_left (norm_nonneg q) (by positivity)
  gcongr

/-- On a near-free eighth-π circle, the actual complex selected root
differs from its collapsed-gap inverse by a uniform multiple of the
squared periodic gap. No reality hypothesis is required. -/
theorem norm_sourceStandardRoot_inv_sub_midpoint_inv_le_on_freeCircle
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (m : ℤ)
    (hmid : ‖sourceStandardRootMidpoint hp hp1 ψ m -
      (Real.pi : ℂ)*m‖ ≤ Real.pi/64)
    (hgap : ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖ ≤ Real.pi/32)
    (z : ℂ) (hz : z ∈ sphere ((Real.pi : ℂ)*m) (Real.pi/8)) :
    ‖(sourceStandardRoot hp hp1 ψ m z)⁻¹ -
      (sourceStandardRootMidpoint hp hp1 ψ m-z)⁻¹‖ ≤
        ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖^2 /
          (2*(Real.pi/16)^3) := by
  let c : ℂ := (Real.pi : ℂ)*m
  let τ := sourceStandardRootMidpoint hp hp1 ψ m
  let γ := sourcePeriodicGapDisplacement hp hp1 ψ m
  let a : ℝ := Real.pi/16
  have ha : 0 < a := by dsimp [a]; positivity
  have hzdist : ‖z-c‖ = Real.pi/8 := by
    simpa only [mem_sphere,dist_eq_norm] using hz
  have hsep : a ≤ ‖τ-z‖ := by
    have htri : ‖z-c‖ ≤ ‖z-τ‖+‖τ-c‖ := by
      have heq : z-c = (z-τ)+(τ-c) := by ring
      rw [heq]
      exact norm_add_le _ _
    rw [hzdist,norm_sub_rev] at htri
    dsimp [a]
    nlinarith [Real.pi_pos]
  have hq : ‖γ^2‖ ≤ a^2 := by
    rw [norm_pow]
    have hsmall : ‖γ‖ ≤ a := by dsimp [a,γ] at *; linarith
    exact pow_le_pow_left₀ (norm_nonneg _) hsmall 2
  have h := norm_normalizedStandardRoot_inv_sub_zeroGap_inv_le_of_separation
    τ (γ^2) z a ha hsep hq
  have heq : sourceStandardRoot hp hp1 ψ m z =
      normalizedStandardRoot τ (γ^2) z := by
    simp only [sourceStandardRoot,τ,γ,sourcePeriodicGapDisplacement_apply]
  change ‖(sourceStandardRoot hp hp1 ψ m z)⁻¹ - (τ-z)⁻¹‖ ≤
    ‖γ‖^2/(2*a^3)
  rw [heq]
  simpa only [norm_pow] using h

/-- The reciprocal-root correction has a quadratic-gap contour bound.
It applies to complex gaps and to any bounded numerator factor on the
circle, with no analyticity assumption inside the filled disc. -/
theorem norm_circleIntegral_weighted_root_inverse_correction_le
    (τ q c σ : ℂ) (R a S M : ℝ)
    (hR : 0 ≤ R) (ha : 0 < a) (hS : 0 ≤ S) (hM : 0 ≤ M)
    (hsep : ∀ z ∈ sphere c R, a ≤ ‖τ-z‖)
    (hq : ‖q‖ ≤ a^2)
    (hσ : ∀ z ∈ sphere c R, ‖σ-z‖ ≤ S)
    (f : ℂ → ℂ) (hf : ∀ z ∈ sphere c R, ‖f z‖ ≤ M) :
    ‖∮ z in C(c,R),
      ((σ-z)*f z) *
        ((normalizedStandardRoot τ q z)⁻¹-(τ-z)⁻¹)‖ ≤
      2*Real.pi*R*(S*M*(‖q‖/(2*a^3))) := by
  have hK : 0 ≤ ‖q‖/(2*a^3) := by positivity
  have hpoint (z : ℂ) (hz : z ∈ sphere c R) :
      ‖((σ-z)*f z) *
        ((normalizedStandardRoot τ q z)⁻¹-(τ-z)⁻¹)‖ ≤
        S*M*(‖q‖/(2*a^3)) := by
    rw [norm_mul,norm_mul]
    have hkernel :=
      norm_normalizedStandardRoot_inv_sub_zeroGap_inv_le_of_separation
        τ q z a ha (hsep z hz) hq
    exact mul_le_mul
      (mul_le_mul (hσ z hz) (hf z hz) (norm_nonneg _) hS)
      hkernel (norm_nonneg _) (mul_nonneg hS hM)
  exact circleIntegral.norm_integral_le_of_norm_le_const hR hpoint

/-- On the fixed free-centered contour, replacing the selected
complex standard root by its collapsed-gap kernel costs only a
quadratic-gap term. -/
theorem norm_circleIntegral_sourceStandardRoot_inverse_correction_freeCircle_le
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (m : ℤ) (σ : ℂ)
    (hmid : ‖sourceStandardRootMidpoint hp hp1 ψ m -
      (Real.pi : ℂ)*m‖ ≤ Real.pi/64)
    (hgap : ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖ ≤ Real.pi/32)
    (f : ℂ → ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hf : ∀ z ∈ sphere ((Real.pi : ℂ)*m) (Real.pi/8), ‖f z‖ ≤ M) :
    ‖∮ z in C((Real.pi : ℂ)*m,Real.pi/8),
      ((σ-z)*f z) *
        ((sourceStandardRoot hp hp1 ψ m z)⁻¹-
          (sourceStandardRootMidpoint hp hp1 ψ m-z)⁻¹)‖ ≤
      2*Real.pi*(Real.pi/8)*
        ((‖σ-(Real.pi : ℂ)*m‖+Real.pi/8)*M*
          (‖sourcePeriodicGapDisplacement hp hp1 ψ m‖^2/
            (2*(Real.pi/16)^3))) := by
  let c : ℂ := (Real.pi : ℂ)*m
  let τ := sourceStandardRootMidpoint hp hp1 ψ m
  let γ := sourcePeriodicGapDisplacement hp hp1 ψ m
  let a : ℝ := Real.pi/16
  let S : ℝ := ‖σ-c‖+Real.pi/8
  have ha : 0 < a := by dsimp [a]; positivity
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hsep (z : ℂ) (hz : z ∈ sphere c (Real.pi/8)) :
      a ≤ ‖τ-z‖ := by
    have hzdist : ‖z-c‖ = Real.pi/8 := by
      simpa only [mem_sphere,dist_eq_norm] using hz
    have htri : ‖z-c‖ ≤ ‖z-τ‖+‖τ-c‖ := by
      have heq : z-c = (z-τ)+(τ-c) := by ring
      rw [heq]
      exact norm_add_le _ _
    rw [hzdist,norm_sub_rev] at htri
    dsimp [a]
    nlinarith [Real.pi_pos]
  have hq : ‖γ^2‖ ≤ a^2 := by
    rw [norm_pow]
    have hsmall : ‖γ‖ ≤ a := by dsimp [a,γ] at *; linarith
    exact pow_le_pow_left₀ (norm_nonneg _) hsmall 2
  have hσ (z : ℂ) (hz : z ∈ sphere c (Real.pi/8)) :
      ‖σ-z‖ ≤ S := by
    have hzdist : ‖c-z‖ = Real.pi/8 := by
      simpa only [mem_sphere,dist_eq_norm,norm_sub_rev] using hz
    have heq : σ-z = (σ-c)+(c-z) := by ring
    rw [heq]
    exact (norm_add_le _ _).trans_eq (by rw [hzdist])
  have heq (z : ℂ) : sourceStandardRoot hp hp1 ψ m z =
      normalizedStandardRoot τ (γ^2) z := by
    simp only [sourceStandardRoot,τ,γ,sourcePeriodicGapDisplacement_apply]
  have h := norm_circleIntegral_weighted_root_inverse_correction_le
    τ (γ^2) c σ (Real.pi/8) a S M (by positivity)
      ha hS hM hsep hq hσ f hf
  change ‖∮ z in C(c,Real.pi/8),
      ((σ-z)*f z) *
        ((sourceStandardRoot hp hp1 ψ m z)⁻¹-(τ-z)⁻¹)‖ ≤
      2*Real.pi*(Real.pi/8)*(S*M*(‖γ‖^2/(2*a^3)))
  simp_rw [heq]
  simpa only [norm_pow] using h

end NLS.ZakharovShabat
