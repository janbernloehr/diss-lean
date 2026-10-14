import NLS.ZakharovShabat.SourceStandardRootProductFactors
import NLS.ComplexAnalysis.QuadraticProductError

/-!
# The exact first-order term of an inverse-square-root product

The linear term is half the radicand perturbation. A uniform bound on
the inverse roots controls the quadratic remainder without requiring
the perturbations to lie in a small disk.
-/

noncomputable section
open Complex
namespace NLS.ZakharovShabat

/-- An algebraic Taylor identity, valid away from the zero root. -/
theorem inv_sqrt_one_sub_taylor (q : ℂ) (hs : Complex.sqrt (1-q) ≠ 0) :
    (Complex.sqrt (1-q))⁻¹-1-q/2 =
      (Complex.sqrt (1-q)-1)^2*((2:ℂ)⁻¹+(Complex.sqrt (1-q))⁻¹) := by
  have hsq : Complex.sqrt (1-q)^2 = 1-q := by
    have h := Complex.cpow_nat_inv_pow (1-q) (Nat.succ_ne_zero 1)
    norm_num at h
    simpa only [Complex.sqrt,one_div] using h
  field_simp [hs]
  linear_combination -Complex.sqrt (1-q)*hsq

/-- The first-order error is quadratic in the actual radicand. -/
theorem norm_inv_sqrt_one_sub_taylor_le (q : ℂ) (hs : Complex.sqrt (1-q) ≠ 0)
    {B : ℝ} (hB : ‖(Complex.sqrt (1-q))⁻¹‖ ≤ B) :
    ‖(Complex.sqrt (1-q))⁻¹-1-q/2‖ ≤ (B+1/2)*‖q‖^2 := by
  rw [inv_sqrt_one_sub_taylor q hs,norm_mul,norm_pow]
  have hroot := norm_sqrt_one_sub_sub_one_le q
  have hsum : ‖(2:ℂ)⁻¹+(Complex.sqrt (1-q))⁻¹‖ ≤ B+1/2 := by
    apply (norm_add_le _ _).trans
    have hi : ‖(2:ℂ)⁻¹‖ = (1/2:ℝ) := by norm_num
    rw [hi]
    linarith
  calc
    _ ≤ ‖q‖^2*(B+1/2) := by gcongr
    _ = _ := by ring

theorem norm_inv_sqrt_one_sub_sub_one_le_bound (q : ℂ)
    (hs : Complex.sqrt (1-q) ≠ 0) {B : ℝ}
    (hB : ‖(Complex.sqrt (1-q))⁻¹‖ ≤ B) :
    ‖(Complex.sqrt (1-q))⁻¹-1‖ ≤ B*‖q‖ := by
  have he : (Complex.sqrt (1-q))⁻¹-1 =
      -(Complex.sqrt (1-q)-1)*(Complex.sqrt (1-q))⁻¹ := by field_simp [hs]; ring
  rw [he,norm_mul,norm_neg]
  exact (mul_le_mul (norm_sqrt_one_sub_sub_one_le q) hB
    (norm_nonneg _) (norm_nonneg _)).trans_eq (mul_comm _ _)

/-- The infinite-product remainder after the signed linear term is quadratic
in the absolute radicand sum. No ordering or smallness hypothesis is used. -/
theorem norm_tprod_inv_sqrt_taylor_le {ι : Type*} (q : ι → ℂ)
    (hq : Summable (fun i => ‖q i‖))
    (hs : ∀ i, Complex.sqrt (1-q i) ≠ 0)
    {B Q : ℝ} (hB0 : 0 ≤ B) (hB : ∀ i, ‖(Complex.sqrt (1-q i))⁻¹‖ ≤ B)
    (hQ : (∑' i, ‖q i‖) ≤ Q) :
    ‖(∏' i, (Complex.sqrt (1-q i))⁻¹)-1-(∑' i, q i)/2‖ ≤
      (B^2*Real.exp (B*Q)+B+1/2)*(∑' i, ‖q i‖)^2 := by
  let u := fun i => (Complex.sqrt (1-q i))⁻¹-1
  let S := ∑' i, ‖q i‖
  have hS0 : 0 ≤ S := tsum_nonneg (fun _ => norm_nonneg _)
  have hupt (i : ι) : ‖u i‖ ≤ B*‖q i‖ :=
    norm_inv_sqrt_one_sub_sub_one_le_bound _ (hs i) (hB i)
  have hu : Summable (fun i => ‖u i‖) :=
    (hq.mul_left B).of_nonneg_of_le (fun _ => norm_nonneg _) hupt
  have hus : (∑' i, ‖u i‖) ≤ B*S := by
    simpa only [S,tsum_mul_left] using hu.tsum_le_tsum hupt (hq.mul_left B)
  have hQ0 : 0 ≤ Q := hS0.trans hQ
  have hpoint (i : ι) : ‖u i-q i/2‖ ≤ ((B+1/2)*S)*‖q i‖ := by
    apply (norm_inv_sqrt_one_sub_taylor_le _ (hs i) (hB i)).trans
    have hi : ‖q i‖ ≤ S := hq.le_tsum i (fun _ _ => norm_nonneg _)
    calc
      _ ≤ (B+1/2)*(S*‖q i‖) := by rw [pow_two]; gcongr
      _ = _ := by ring
  have hr : Summable (fun i => ‖u i-q i/2‖) :=
    (hq.mul_left ((B+1/2)*S)).of_nonneg_of_le (fun _ => norm_nonneg _) hpoint
  have hlin : ‖(∑' i, u i)-(∑' i, q i)/2‖ ≤ (B+1/2)*S^2 := by
    rw [← tsum_div_const,← hu.of_norm.tsum_sub (hq.of_norm.div_const 2)]
    apply (norm_tsum_le_tsum_norm hr).trans
    have ht := hr.tsum_le_tsum hpoint (hq.mul_left ((B+1/2)*S))
    simpa only [tsum_mul_left,S,mul_assoc,pow_two] using ht
  have hprod := ComplexAnalysis.norm_tprod_one_add_sub_one_sub_tsum_le u hu
  have he : (∏' i, (1+u i)) = ∏' i, (Complex.sqrt (1-q i))⁻¹ := by
    apply tprod_congr
    intro i
    dsimp [u]
    ring
  rw [he] at hprod
  have hprod' : ‖(∏' i, (Complex.sqrt (1-q i))⁻¹)-1-∑' i, u i‖ ≤
      (B*S)^2*Real.exp (B*Q) := by
    apply hprod.trans
    gcongr
    exact hus.trans (mul_le_mul_of_nonneg_left hQ hB0)
  have he' : (∏' i, (Complex.sqrt (1-q i))⁻¹)-1-(∑' i, q i)/2 =
      ((∏' i, (Complex.sqrt (1-q i))⁻¹)-1-∑' i, u i)+
        ((∑' i, u i)-(∑' i, q i)/2) := by ring
  rw [he']
  exact (norm_add_le _ _).trans ((add_le_add hprod' hlin).trans_eq (by dsimp [S]; ring))

end NLS.ZakharovShabat
