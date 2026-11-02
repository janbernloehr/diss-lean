import NLS.KdV.HillBilinearSymmetry
import NLS.KdV.HillSpectralLipschitz
import NLS.KdV.HillAnalytic
import NLS.FunctionalAnalysis.TwoDimensionalDeterminant

/-!
# Weighted separation of two high-strip Hill roots

The literal reduced matrix has equal diagonal entries. Its determinant
factorization, the shifted coefficient estimates and the proved spectral
Lipschitz bound control the distance between any two roots in the strip.
No unproved global spectral labeling or choice of root branches is used.
-/

noncomputable section
open scoped ENNReal
namespace NLS.KdV

variable (w : SpectralWeight) (q : WeightedCoeff w.toWeight 2)
  (n : ℕ) (hn : 1 ≤ n) (z : ℂ) (hz : z ∈ reducedHillStrip n)
  (hcut : 8*‖q‖ ≤ (n : ℝ))

theorem hillEffectivePotential_decompose (u : ℂ × ℂ) :
    hillEffectivePotential w q n hn z hz hcut u =
      u.1 • hillCorrectedMode w q n hn z hz hcut n+
        u.2 • hillCorrectedMode w q n hn z hz hcut (-(n : ℤ)) := by
  rw [hillCorrectedMode_pos, hillCorrectedMode_neg, ← map_smul, ← map_smul, ← map_add]
  congr 1
  ext <;> simp

/-- The source's homogeneous-diagonal matrix is the constructed operator. -/
theorem hillReducedOperator_apply (u : ℂ × ℂ) :
    hillReducedOperator w q n hn z hz hcut u =
      (((z-(freeHillValue n : ℂ)-hillDiagonal w q n hn z hz hcut)*u.1-
          hillUpperCoupling w q n hn z hz hcut*u.2),
       ((z-(freeHillValue n : ℂ)-hillDiagonal w q n hn z hz hcut)*u.2-
          hillLowerCoupling w q n hn z hz hcut*u.1)) := by
  have he := hillEffectivePotential_decompose w q n hn z hz hcut u
  have hd := hillDiagonal_eq_opposite w q n hn z hz hcut
  apply Prod.ext
  · change (z-(freeHillValue n : ℂ))*u.1-
      (hillEffectivePotential w q n hn z hz hcut u).val n = _
    rw [he, WeightedCoeff.add_val, WeightedCoeff.smul_val, WeightedCoeff.smul_val]
    change (z-(freeHillValue n : ℂ))*u.1-
      (u.1*hillDiagonal w q n hn z hz hcut+u.2*hillUpperCoupling w q n hn z hz hcut) = _
    ring
  · change (z-(freeHillValue n : ℂ))*u.2-
      (hillEffectivePotential w q n hn z hz hcut u).val (-(n : ℤ)) = _
    rw [he, WeightedCoeff.add_val, WeightedCoeff.smul_val, WeightedCoeff.smul_val]
    change (z-(freeHillValue n : ℂ))*u.2-
      (u.1*hillLowerCoupling w q n hn z hz hcut+u.2*hillOppositeDiagonal w q n hn z hz hcut) = _
    rw [← hd]
    ring

theorem hillReducedDeterminant_factorization :
    hillReducedDeterminant w n (q,z) =
      (z-(freeHillValue n : ℂ)-hillDiagonal w q n hn z hz hcut)^2-
        hillUpperCoupling w q n hn z hz hcut*hillLowerCoupling w q n hn z hz hcut := by
  rw [hillReducedDeterminant_eq w n hn (q,z) hz hcut, FiniteSpectralDeterminant.det_prod_formula,
    hillReducedOperator_apply, hillReducedOperator_apply]
  simp only [mul_one, mul_zero, sub_zero, zero_sub]
  ring

theorem hillUpperCoupling_le :
    w (2*(n : ℤ))*‖hillUpperCoupling w q n hn z hz hcut‖ ≤
      w (2*(n : ℤ))*‖q.val (2*(n : ℤ))‖+8*‖q‖^2/(n : ℝ) := by
  have ht := norm_le_norm_sub_add (hillUpperCoupling w q n hn z hz hcut) (q.val (2*(n : ℤ)))
  have hm := mul_le_mul_of_nonneg_left ht (w.positive (2*(n : ℤ))).le
  have he := hillUpperCoupling_error_le w q n hn z hz hcut
  nlinarith

theorem hillLowerCoupling_le :
    w (2*(n : ℤ))*‖hillLowerCoupling w q n hn z hz hcut‖ ≤
      w (2*(n : ℤ))*‖q.val (-(2*(n : ℤ)))‖+8*‖q‖^2/(n : ℝ) := by
  have ht := norm_le_norm_sub_add (hillLowerCoupling w q n hn z hz hcut) (q.val (-(2*(n : ℤ))))
  have hm := mul_le_mul_of_nonneg_left ht (w.positive (2*(n : ℤ))).le
  have he := hillLowerCoupling_error_le w q n hn z hz hcut
  nlinarith

theorem hillReduced_root_shift_bound (hd : hillReducedDeterminant w n (q,z) = 0) :
    (w (2*(n : ℤ))*‖z-(freeHillValue n : ℂ)-hillDiagonal w q n hn z hz hcut‖)^2 ≤
      (w (2*(n : ℤ))*‖q.val (2*(n : ℤ))‖+8*‖q‖^2/(n : ℝ))*
      (w (2*(n : ℤ))*‖q.val (-(2*(n : ℤ)))‖+8*‖q‖^2/(n : ℝ)) := by
  have hW : 0 ≤ w (2*(n : ℤ)) := (w.positive _).le
  rw [hillReducedDeterminant_factorization w q n hn z hz hcut] at hd
  have he := congrArg norm (sub_eq_zero.mp hd)
  rw [norm_pow, norm_mul] at he
  calc
    _ = (w (2*(n : ℤ))*‖hillUpperCoupling w q n hn z hz hcut‖)*
        (w (2*(n : ℤ))*‖hillLowerCoupling w q n hn z hz hcut‖) := by rw [mul_pow, he]; ring
    _ ≤ _ := mul_le_mul (hillUpperCoupling_le w q n hn z hz hcut)
      (hillLowerCoupling_le w q n hn z hz hcut) (by positivity) (by positivity)

include hn hz hcut in
/-- Corrected-constant weighted counterpart of the root-separation estimate.
The roots may coincide; their analytic orders and labels are not hypotheses. -/
theorem hillReduced_roots_weighted_separation (y : ℂ) (hy : y ∈ reducedHillStrip n)
    (hdz : hillReducedDeterminant w n (q,z) = 0)
    (hdy : hillReducedDeterminant w n (q,y) = 0) :
    (w (2*(n : ℤ)))^2*‖z-y‖^2 ≤
      9*((w (2*(n : ℤ)))^2*‖q.val (2*(n : ℤ))‖^2+
        (w (2*(n : ℤ)))^2*‖q.val (-(2*(n : ℤ)))‖^2)+1152*‖q‖^4/(n : ℝ)^2 := by
  have hW : 0 ≤ w (2*(n : ℤ)) := (w.positive _).le
  let W := w (2*(n : ℤ))
  let A := W*‖z-(freeHillValue n : ℂ)-hillDiagonal w q n hn z hz hcut‖
  let B := W*‖y-(freeHillValue n : ℂ)-hillDiagonal w q n hn y hy hcut‖
  let P := W*‖q.val (2*(n : ℤ))‖
  let M := W*‖q.val (-(2*(n : ℤ)))‖
  let E := 8*‖q‖^2/(n : ℝ)
  let D := W*‖z-y‖
  have hA : A^2 ≤ (P+E)*(M+E) := hillReduced_root_shift_bound w q n hn z hz hcut hdz
  have hB : B^2 ≤ (P+E)*(M+E) := hillReduced_root_shift_bound w q n hn y hy hcut hdy
  have hdiag := hillDiagonal_sub_le_quarter w q n hn z y hz hy hcut
  have ht : ‖z-y‖ ≤ ‖hillDiagonal w q n hn z hz hcut-hillDiagonal w q n hn y hy hcut‖+
      (‖z-(freeHillValue n : ℂ)-hillDiagonal w q n hn z hz hcut‖+
        ‖y-(freeHillValue n : ℂ)-hillDiagonal w q n hn y hy hcut‖) := by
    calc
      _ = ‖(hillDiagonal w q n hn z hz hcut-hillDiagonal w q n hn y hy hcut)+
          ((z-(freeHillValue n : ℂ)-hillDiagonal w q n hn z hz hcut)-
            (y-(freeHillValue n : ℂ)-hillDiagonal w q n hn y hy hcut))‖ := by congr 1; ring
      _ ≤ ‖hillDiagonal w q n hn z hz hcut-hillDiagonal w q n hn y hy hcut‖+
          ‖(z-(freeHillValue n : ℂ)-hillDiagonal w q n hn z hz hcut)-
            (y-(freeHillValue n : ℂ)-hillDiagonal w q n hn y hy hcut)‖ := norm_add_le _ _
      _ ≤ _ := add_le_add le_rfl (norm_sub_le _ _)
  have hlin : D ≤ (1/4 : ℝ)*D+(A+B) := by
    have hm := mul_le_mul_of_nonneg_left (ht.trans (add_le_add hdiag le_rfl)) hW
    dsimp [D, A, B, W]
    nlinarith
  have hD : 0 ≤ D := by dsimp [D, W]; positivity
  have hAB : 0 ≤ A+B := by dsimp [A, B, W]; positivity
  have hs := mul_self_le_mul_self hD (show D ≤ (4/3 : ℝ)*(A+B) by linarith)
  have hsum : (A+B)^2 ≤ 4*((P+E)*(M+E)) := by nlinarith [sq_nonneg (A-B)]
  have hprod : (P+E)*(M+E) ≤ P^2+M^2+2*E^2 := by
    nlinarith [sq_nonneg (P-M), sq_nonneg (P-E), sq_nonneg (M-E)]
  have hmain : D^2 ≤ 9*(P^2+M^2+2*E^2) := by
    nlinarith [sq_nonneg P, sq_nonneg M, sq_nonneg E]
  dsimp [D, P, M, E, W] at hmain
  convert hmain using 1 <;> ring

end NLS.KdV
