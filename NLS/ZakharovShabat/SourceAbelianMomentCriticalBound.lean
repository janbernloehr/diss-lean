import NLS.ZakharovShabat.SourceAbelianMomentCriticalComparison
import NLS.ZakharovShabat.SourceAbelianMomentSquaredOffsetError

/-! # Cubic-gap control from the actual critical cancellation

The three terms retain the actual psi-critical root error and actual
product difference. The last term has one extra gap factor and a
separated spectral denominator. No squared-gap midpoint error is used.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Pointwise cubic-gap bound for the exact critically cancelled numerator. -/
theorem norm_sourceSecondMomentCriticalNumerator_le
    (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p))
    (n k : ℤ) (hkn : k ≠ n) (a : DeletedCoeff p n) (ψ : CoeffPair p) (z : ℂ)
    (hz : z ∈ sourcePeriodicSegment hp hp1 ψ k)
    (α : ℂ) (hα : displacedRoots (a : Coeff p) k =
      sourceCriticalRoot hp hp1 ψ k+sourcePeriodicGapDisplacement hp hp1 ψ k*α)
    (L P B A D d : ℝ) (hL : 0 ≤ L) (hB : 0 ≤ B) (hA : ‖α‖ ≤ A) (hd : 0 < d)
    (hS : ‖sourceFullAbelianSquare hp hp1 W k (z,ψ)‖ ≤ ‖sourcePeriodicGapDisplacement hp hp1 ψ k‖^2*L)
    (hZ : ‖sourcePsiCriticalFilledQuotient hp hp1 n k a ψ z‖ ≤ P)
    (hR : ‖sourceCriticalRoot hp hp1 ψ k-z‖ ≤ ‖sourcePeriodicGapDisplacement hp hp1 ψ k‖*B)
    (hD : ‖sourcePsiCriticalFilledQuotient hp hp1 n k a ψ z-sourceCriticalDeletedQuotient hp hp1 k ψ z‖ ≤ D)
    (hden : d ≤ ‖sourceCriticalRoot hp hp1 ψ n-z‖) :
    ‖sourceSecondMomentCriticalNumerator hp hp1 W n k a ψ z‖ ≤
      ‖sourcePeriodicGapDisplacement hp hp1 ψ k‖^3*L*
        (P*‖α‖+B*D+‖sourcePeriodicGapDisplacement hp hp1 ψ k‖*(A+B)*P/(2*d)) := by
  let G := ‖sourcePeriodicGapDisplacement hp hp1 ψ k‖
  have hG : 0 ≤ G := norm_nonneg _
  have hAB : 0 ≤ A+B := add_nonneg ((norm_nonneg _).trans hA) hB
  have hden0 : sourceCriticalRoot hp hp1 ψ n-z ≠ 0 := norm_pos_iff.mp (hd.trans_le hden)
  have hroot : ‖displacedRoots (a : Coeff p) k-sourceCriticalRoot hp hp1 ψ k‖ = G*‖α‖ := by
    rw [hα,add_sub_cancel_left,norm_mul]
  have hsig : ‖displacedRoots (a : Coeff p) k-z‖ ≤ G*(A+B) := by
    have ht := norm_sub_le_norm_sub_add_norm_sub (displacedRoots (a : Coeff p) k)
      (sourceCriticalRoot hp hp1 ψ k) z
    rw [hroot] at ht
    nlinarith [mul_le_mul_of_nonneg_left hA hG]
  have hmid : ‖z-sourceStandardRootMidpoint hp hp1 ψ k‖ ≤ G/2 := by
    simpa only [norm_sub_rev] using norm_sourceMidpoint_sub_le_halfGap hp hp1 ψ k z hz
  let Z := sourcePsiCriticalFilledQuotient hp hp1 n k a ψ z
  let X := sourceCriticalDeletedQuotient hp hp1 k ψ z
  have hterm1 : ‖(displacedRoots (a : Coeff p) k-sourceCriticalRoot hp hp1 ψ k)*Z‖ ≤ G*‖α‖*P := by
    rw [norm_mul,hroot]
    exact mul_le_mul_of_nonneg_left hZ (by positivity)
  have hterm2 : ‖(sourceCriticalRoot hp hp1 ψ k-z)*(Z-X)‖ ≤ G*B*D := by
    rw [norm_mul]
    exact mul_le_mul hR hD (norm_nonneg _) (mul_nonneg hG hB)
  have hterm3 : ‖(z-sourceStandardRootMidpoint hp hp1 ψ k)*(displacedRoots (a : Coeff p) k-z)*Z/
      (sourceCriticalRoot hp hp1 ψ n-z)‖ ≤ (G/2*(G*(A+B))*P)/d := by
    rw [norm_div,norm_mul,norm_mul]
    apply (div_le_div_of_nonneg_left (by positivity) hd hden).trans
    exact div_le_div_of_nonneg_right
      (mul_le_mul (mul_le_mul hmid hsig (norm_nonneg _) (by positivity)) hZ (norm_nonneg _) (by positivity)) hd.le
  have hsum := (norm_add_le
    ((displacedRoots (a : Coeff p) k-sourceCriticalRoot hp hp1 ψ k)*Z+
      (sourceCriticalRoot hp hp1 ψ k-z)*(Z-X))
    ((z-sourceStandardRootMidpoint hp hp1 ψ k)*(displacedRoots (a : Coeff p) k-z)*Z/(sourceCriticalRoot hp hp1 ψ n-z))).trans
      (add_le_add ((norm_add_le _ _).trans (add_le_add hterm1 hterm2)) hterm3)
  rw [sourceSecondMomentCriticalNumerator_eq_three_terms hp hp1 W n k hkn a ψ z hden0,norm_mul,norm_mul,norm_I,one_mul]
  calc
    _ ≤ (G^2*L)*(G*‖α‖*P+G*B*D+(G/2*(G*(A+B))*P)/d) :=
      mul_le_mul hS hsum (norm_nonneg _) (by positivity)
    _ = _ := by dsimp only [G]; ring

namespace SourceAbelianMomentErrorDomain
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W W' : Set (CoeffPair p)}
variable {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n} {A₀ : SourceAbelianMomentAtlas hp hp1 W s}

/-- The critically cancelled cubic-gap estimate for the actual second moment.
All pointwise bounds are on the actual gap, and no nonzero-gap assumption is needed. -/
theorem critical_cubic_bound
    (E : SourceAbelianMomentErrorDomain A₀) (C : SourceFullAbelianUniformCauchyFamily hp hp1 W')
    (ψ : CoeffPair p) (hψ : ψ ∈ E.domain)
    (hψC : ψ ∈ ball C.discs.source.val C.discs.sourceRadius)
    (n k : ℤ) (hkn : k ≠ n) (α : ℂ)
    (hα : displacedRoots (s n ψ : Coeff p) k =
      sourceCriticalRoot hp hp1 ψ k+sourcePeriodicGapDisplacement hp hp1 ψ k*α)
    (L P B A D d : ℝ) (hL : 0 ≤ L) (hB : 0 ≤ B) (hA : ‖α‖ ≤ A) (hd : 0 < d)
    (hS : ∀ z ∈ sourcePeriodicSegment hp hp1 ψ k,
      ‖sourceFullAbelianSquare hp hp1 W k (z,ψ)‖ ≤ ‖sourcePeriodicGapDisplacement hp hp1 ψ k‖^2*L)
    (hZ : ∀ z ∈ sourcePeriodicSegment hp hp1 ψ k,
      ‖sourcePsiCriticalFilledQuotient hp hp1 n k (s n ψ) ψ z‖ ≤ P)
    (hR : ∀ z ∈ sourcePeriodicSegment hp hp1 ψ k,
      ‖sourceCriticalRoot hp hp1 ψ k-z‖ ≤ ‖sourcePeriodicGapDisplacement hp hp1 ψ k‖*B)
    (hD : ∀ z ∈ sourcePeriodicSegment hp hp1 ψ k,
      ‖sourcePsiCriticalFilledQuotient hp hp1 n k (s n ψ) ψ z-sourceCriticalDeletedQuotient hp hp1 k ψ z‖ ≤ D)
    (hden : ∀ z ∈ sourcePeriodicSegment hp hp1 ψ k, d ≤ ‖sourceCriticalRoot hp hp1 ψ n-z‖) :
    ‖(2*Real.pi:ℂ)⁻¹*((sourceCriticalRoot hp hp1 ψ n-sourceStandardRootMidpoint hp hp1 ψ k)*
      A₀.moment n k 2 ψ)‖ ≤ ‖sourcePeriodicGapDisplacement hp hp1 ψ k‖^3*L*
        (P*‖α‖+B*D+‖sourcePeriodicGapDisplacement hp hp1 ψ k‖*(A+B)*P/(2*d)) := by
  apply E.critical_comparison_bound C ψ hψ hψC n k
  intro z hz
  exact norm_sourceSecondMomentCriticalNumerator_le hp hp1 W n k hkn (s n ψ) ψ z hz α hα
    L P B A D d hL hB hA hd (hS z hz) (hZ z hz) (hR z hz) (hD z hz) (hden z hz)

/-- Spectral separation turns the critical scaling into the literal n-k
weight of Lemma 5.3, with an explicit cubic-gap coefficient bound. -/
theorem critical_cubic_index_bound
    (E : SourceAbelianMomentErrorDomain A₀) (C : SourceFullAbelianUniformCauchyFamily hp hp1 W')
    (ψ : CoeffPair p) (hψ : ψ ∈ E.domain)
    (hψC : ψ ∈ ball C.discs.source.val C.discs.sourceRadius)
    (n k : ℤ) (hkn : k ≠ n) (α : ℂ)
    (hα : displacedRoots (s n ψ : Coeff p) k =
      sourceCriticalRoot hp hp1 ψ k+sourcePeriodicGapDisplacement hp hp1 ψ k*α)
    (L P B A D : ℝ) (hL : 0 ≤ L) (hB : 0 ≤ B) (hA : ‖α‖ ≤ A)
    (hS : ∀ z ∈ sourcePeriodicSegment hp hp1 ψ k,
      ‖sourceFullAbelianSquare hp hp1 W k (z,ψ)‖ ≤ ‖sourcePeriodicGapDisplacement hp hp1 ψ k‖^2*L)
    (hZ : ∀ z ∈ sourcePeriodicSegment hp hp1 ψ k,
      ‖sourcePsiCriticalFilledQuotient hp hp1 n k (s n ψ) ψ z‖ ≤ P)
    (hR : ∀ z ∈ sourcePeriodicSegment hp hp1 ψ k,
      ‖sourceCriticalRoot hp hp1 ψ k-z‖ ≤ ‖sourcePeriodicGapDisplacement hp hp1 ψ k‖*B)
    (hD : ∀ z ∈ sourcePeriodicSegment hp hp1 ψ k,
      ‖sourcePsiCriticalFilledQuotient hp hp1 n k (s n ψ) ψ z-sourceCriticalDeletedQuotient hp hp1 k ψ z‖ ≤ D)
    (hden : ∀ z ∈ sourcePeriodicSegment hp hp1 ψ k,
      (Real.pi/2)*|((n-k:ℤ):ℝ)| ≤ ‖sourceCriticalRoot hp hp1 ψ n-z‖) :
    ‖((n-k:ℤ):ℂ)*A₀.moment n k 2 ψ‖ ≤ ‖sourcePeriodicGapDisplacement hp hp1 ψ k‖^3*
      (4*L*(P*‖α‖+B*D+((A+B)*P/Real.pi)*
        (‖sourcePeriodicGapDisplacement hp hp1 ψ k‖*‖NLS.Fourier.hilbertKernel (n-k)‖))) := by
  have hj : 0 < |((n-k:ℤ):ℝ)| := by exact_mod_cast abs_pos.mpr (sub_ne_zero.mpr hkn.symm)
  have hd : 0 < (Real.pi/2)*|((n-k:ℤ):ℝ)| := mul_pos (by positivity) hj
  have hb := E.critical_cubic_bound C ψ hψ hψC n k hkn α hα L P B A D
    ((Real.pi/2)*|((n-k:ℤ):ℝ)|) hL hB hA hd hS hZ hR hD hden
  have hkernel : ‖NLS.Fourier.hilbertKernel (n-k)‖ = |((n-k:ℤ):ℝ)|⁻¹ := by
    rw [NLS.Fourier.hilbertKernel,norm_neg,norm_inv,Complex.norm_intCast]
  have he : ‖sourcePeriodicGapDisplacement hp hp1 ψ k‖*(A+B)*P/
      (2*((Real.pi/2)*|((n-k:ℤ):ℝ)|)) = ((A+B)*P/Real.pi)*
        (‖sourcePeriodicGapDisplacement hp hp1 ψ k‖*‖NLS.Fourier.hilbertKernel (n-k)‖) := by
    rw [hkernel]
    field_simp
  rw [he,norm_mul,norm_mul,norm_inv] at hb
  have hπ : ‖(2*Real.pi:ℂ)‖ = 2*Real.pi := by simp only [norm_mul,norm_ofNat,Complex.norm_real,Real.norm_of_nonneg Real.pi_pos.le]
  rw [hπ] at hb
  have hraw := (inv_mul_le_iff₀ (by positivity : (0:ℝ)<2*Real.pi)).mp hb
  have hmid := mul_le_mul_of_nonneg_right
    (hden _ (sourcePeriodicMidpoint_mem_segment hp hp1 ψ k)) (norm_nonneg (A₀.moment n k 2 ψ))
  rw [norm_mul,Complex.norm_intCast]
  apply (mul_le_mul_iff_left₀ (by positivity : (0:ℝ)<Real.pi/2)).mp
  nlinarith

end SourceAbelianMomentErrorDomain

end NLS.ZakharovShabat
