import NLS.KdV.SingularHillRayleigh
import NLS.KdV.SingularHillFreeSpectrum

/-!
# A lower spectral bound controls the original mean-zero H-minus-one norm

The shifted positive form is tested against the actual constant function.
Its quadratic energy is the shift because the potential has mean zero.
Cauchy–Schwarz controls the entire original dual norm, while multiplication
depends linearly on the unchanged H-minus-one norm of the potential.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.SmoothPeriodicTest NLS.Fourier.PeriodicFourierLebesgue

/-- The original operator sends the physical constant one to its potential. -/
theorem singularHillOperator_freeMode_zero (q : FourierLebesgueSpace (2:ℝ) (-1) 2) :
    singularHillOperator q (singularHillFreeMode 0) = q := by
  apply Subtype.ext
  apply Distribution.ext_coefficients
  intro k
  rw [singularHillOperator_coefficient]
  simp only [singularHillFreeMode_coefficient,mul_ite,mul_one,mul_zero,tsum_ite_eq,sub_zero]
  by_cases hk : k = 0
  · simp [hk,freeHillValue]
  · simp only [if_neg hk,zero_add]

/-- Testing against the actual constant one is exactly the original zero mode. -/
theorem singularHillSesquilinear_freeMode_zero (q : FourierLebesgueSpace (2:ℝ) (-1) 2) :
    singularHillSesquilinear q (singularHillFreeMode 0) = q.val (mode 0) := by
  rw [singularHillSesquilinear_eq_tsum_neg]
  simp only [singularHillFreeMode_coefficient]
  simp

/-- A fixed finite constant involving only the original operator norms. -/
def singularHillPotentialBoundConstant : ℝ :=
  1+‖singularHillLaplacian‖+‖singularHillDomainInclusion‖+
    ‖hminusOneMultiplicationFamily (L := 2)‖+
      ‖singularHillDomainInclusion (singularHillFreeMode 0)‖^2

/-- The fixed original-space bound constant is strictly positive. -/
theorem singularHillPotentialBoundConstant_pos : 0 < singularHillPotentialBoundConstant := by
  unfold singularHillPotentialBoundConstant
  positivity

/-- Every real mean-zero original H-minus-one potential is norm-bounded by
any lower bound on its actual spectrum. The constant is independent of q. -/
theorem norm_singularHillPotential_le_of_spectral_lower_bound
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (hq : q.val = q.val.conjugate)
    (hmean : q.val (mode 0) = 0)
    (a : ℝ) (ha : ∀ z ∈ singularHillSpectrum q, a ≤ z.re) :
    ‖q‖ ≤ 4*(|a|+1)*singularHillPotentialBoundConstant := by
  let R := |a|+1
  have hR : 0 < R := by dsimp [R]; positivity
  have hR1 : 1 ≤ R := by dsimp [R]; linarith [abs_nonneg a]
  have hRa : -R ≤ a := by dsimp [R]; linarith [neg_le_abs a]
  let D := sobolevDualIsometry (L := 2) (p := 2) (q := 2) 1
    (by norm_num : (2:ℝ≥0∞) ≠ ⊤)
  let C := sobolevConjugation (L := 2) 1 2
  let P := singularHillOperator q-((-R:ℝ):ℂ) • singularHillDomainInclusion
  let v := singularHillFreeMode 0
  let W := singularHillDomainInclusion v
  have hs : LinearMap.IsSymm (realDualityForm D C P) :=
    realDualityForm_singularHillPencil_isSymm q hq (-R)
  have hn : ∀ f, 0 ≤ realDualityForm D C P f f := by
    intro f
    rw [realDualityForm_singularHillPencil]
    have h := singularHill_form_lower_bound_of_spectral_lower_bound q hq (-R)
      (fun z hz => hRa.trans (ha z hz)) f
    linarith only [h]
  have hv : realDualityForm D C P v v = R := by
    rw [realDualityForm_singularHillPencil,singularHillOperator_freeMode_zero,
      singularHillSesquilinear_freeMode_zero,hmean,Complex.zero_re,
      singularHillSesquilinear_freeMode_zero,singularHillDomainInclusion_val]
    simp [v]
  have hpos := norm_apply_sq_le_realDualityForm_mul_norm D C P hs hn v
  rw [hv] at hpos
  have hscalar : ‖((-R:ℝ):ℂ)‖ = R := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_neg,abs_of_pos hR]
  let A := ‖singularHillLaplacian‖
  let B := ‖singularHillDomainInclusion‖
  let M := ‖hminusOneMultiplicationFamily (L := 2)‖
  have hL : ‖singularHillOperator q‖ ≤ A+M*‖q‖ := by
    have h := (hminusOneMultiplicationFamily (L := 2)).le_opNorm q
    change ‖hminusOneMultiplication q‖ ≤ M*‖q‖ at h
    have hsum := norm_add_le singularHillLaplacian (hminusOneMultiplication q)
    change ‖singularHillOperator q‖ ≤ A+‖hminusOneMultiplication q‖ at hsum
    linarith only [h,hsum]
  have hP : ‖P‖ ≤ A+R*B+M*‖q‖ := by
    have h := norm_sub_le (singularHillOperator q)
      (((-R:ℝ):ℂ) • singularHillDomainInclusion)
    rw [norm_smul,hscalar] at h
    dsimp [B]
    linarith only [h,hL]
  have heq : q = P v+((-R:ℝ):ℂ) • W := by
    dsimp [P,W]
    rw [sub_apply,_root_.smul_apply,singularHillOperator_freeMode_zero]
    abel
  have hqnorm : ‖q‖ ≤ ‖P v‖+R*‖W‖ := by
    calc
      ‖q‖ = ‖P v+((-R:ℝ):ℂ) • W‖ := congrArg norm heq
      _ ≤ ‖P v‖+‖((-R:ℝ):ℂ) • W‖ := norm_add_le _ _
      _ = _ := by rw [norm_smul,hscalar]
  have hsq : ‖q‖^2 ≤ 2*(R*(A+R*B+M*‖q‖))+2*R^2*‖W‖^2 := by
    have hmul := mul_le_mul_of_nonneg_left hP hR.le
    have hsum : ‖q‖^2 ≤ (‖P v‖+R*‖W‖)^2 :=
      (sq_le_sq₀ (norm_nonneg q) (by positivity)).mpr hqnorm
    nlinarith only [hmul,hsum,hpos,sq_nonneg (‖P v‖-R*‖W‖)]
  let K := singularHillPotentialBoundConstant
  have hA : 0 ≤ A := norm_nonneg _
  have hB : 0 ≤ B := norm_nonneg _
  have hM : 0 ≤ M := norm_nonneg (hminusOneMultiplicationFamily (L := 2))
  have hW : 0 ≤ ‖W‖^2 := sq_nonneg _
  have hK : K = 1+A+B+M+‖W‖^2 := rfl
  have hK1 : 1 ≤ K := by rw [hK]; linarith only [hA,hB,hM,hW]
  have hAK : A ≤ K := by rw [hK]; linarith only [hB,hM,hW]
  have hBK : B ≤ K := by rw [hK]; linarith only [hA,hM,hW]
  have hMK : M ≤ K := by rw [hK]; linarith only [hA,hB,hW]
  have hWK : ‖W‖^2 ≤ K := by rw [hK]; linarith only [hA,hB,hM]
  have hstep : ‖q‖^2 ≤ 6*R^2*K+2*R*K*‖q‖ := by
    have h1 := mul_le_mul_of_nonneg_left hAK hR.le
    have h2 := mul_le_mul_of_nonneg_left hBK (sq_nonneg R)
    have h3 := mul_le_mul_of_nonneg_left hMK (mul_nonneg hR.le (norm_nonneg q))
    have h4 := mul_le_mul_of_nonneg_left hWK (sq_nonneg R)
    have h5 : R*K ≤ R^2*K := mul_le_mul_of_nonneg_right
      (show R ≤ R^2 by nlinarith only [hR1]) (by linarith only [hK1])
    nlinarith only [hsq,h1,h2,h3,h4,h5]
  have hfinal : ‖q‖^2 ≤ 6*(R*K)^2+2*(R*K)*‖q‖ := by
    have h := mul_nonneg (sq_nonneg R) (show 0 ≤ K^2-K by nlinarith only [hK1])
    nlinarith only [hstep,h]
  have hkpos : 0 < R*K := mul_pos hR (by linarith only [hK1])
  change ‖q‖ ≤ 4*R*K
  by_contra! hbig
  have hmul := mul_pos (show 0 < ‖q‖-4*(R*K) by nlinarith only [hbig])
    (show 0 < ‖q‖+2*(R*K) by positivity)
  nlinarith only [hfinal,hmul,sq_nonneg (R*K)]

end NLS.KdV
