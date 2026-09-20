import NLS.ZakharovShabat.RestoredSineProductLp
import NLS.ZakharovShabat.EntireSpectralPairProducts

/-!
# Paired spectral products from restored sine factors

The entire paired product is exactly minus four times the two restored sine
products away from the free lattice. Positive lp error majorants therefore
control its difference from the free paired product there.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Roots obtained by adding an lp displacement to the free lattice. -/
def displacedRoots (a : Coeff p) (n : ℤ) : ℂ := (Real.pi : ℂ)*n+a n

omit [Fact (1 ≤ p)] in
/-- The constructed roots have exactly their given lp displacement. -/
theorem memℓp_displacedRoots (a : Coeff p) :
    Memℓp (fun n => displacedRoots a n-(Real.pi : ℂ)*n) p := by
  simpa [displacedRoots] using (show Memℓp (fun n => a n) p from lp.memℓp a)

/-- The paired entire product is the product of the restored local sine factors off the lattice. -/
theorem entireSpectralPairProduct_eq_restored (hp : p ≠ ⊤) (a b : Coeff p)
    (n : ℤ) (z : ℂ) (hz : z ∉ freeLattice) :
    entireSpectralPairProduct (displacedRoots a) (displacedRoots b) z =
      -4*restoredSineProduct a n z*restoredSineProduct b n z := by
  rw [entireSpectralPairProduct_eq_offLattice hp _ _ (memℓp_displacedRoots a) (memℓp_displacedRoots b) z hz,
    spectralPairProductFormula, spectralRelativePairProduct,
    (multipliable_spectralRelativeFactor hp _ (memℓp_displacedRoots a) z hz).tprod_mul
      (multipliable_spectralRelativeFactor hp _ (memℓp_displacedRoots b) z hz),
    restoredSineProduct_eq_offLattice hp a n z hz, restoredSineProduct_eq_offLattice hp b n z hz]
  have hfree : (freeDiscriminant z)^2-4 = -4*Complex.sin z^2 := by
    have hs := Complex.sin_sq_add_cos_sq z
    unfold freeDiscriminant
    linear_combination 4*hs
  rw [hfree]
  simp only [spectralRelativeFactor, displacedRoots]
  ring

/-- A positive sequence controlling the difference of two-factor products. -/
def spectralPairErrorMajorant (C : ℝ) (A B : Coeff p) : Coeff p :=
  (4 : ℂ) • ((((C+‖B‖ : ℝ) : ℂ) • Coeff.magnitude A)+(C : ℂ) • Coeff.magnitude B)

/-- The majorant has no coefficient cancellation. -/
theorem norm_spectralPairErrorMajorant_apply {C : ℝ} (hC : 0 ≤ C) (A B : Coeff p) (n : ℤ) :
    ‖spectralPairErrorMajorant C A B n‖ = 4*((C+‖B‖)*‖A n‖+C*‖B n‖) := by
  simp only [spectralPairErrorMajorant, lp.coeFn_smul, lp.coeFn_add, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, Coeff.magnitude_apply, ← Complex.ofReal_add, ← Complex.ofReal_mul]
  rw [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_of_nonneg (by positivity)]

/-- The lp norm of the paired majorant is bounded in terms of the two input majorant norms. -/
theorem norm_spectralPairErrorMajorant_le {C : ℝ} (hC : 0 ≤ C) (A B : Coeff p) :
    ‖spectralPairErrorMajorant C A B‖ ≤ 4*((C+‖B‖)*‖A‖+C*‖B‖) := by
  rw [spectralPairErrorMajorant, norm_smul, Complex.norm_ofNat]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply (norm_add_le _ _).trans
  simp only [norm_smul, Coeff.norm_magnitude, Complex.norm_real,
    Real.norm_of_nonneg hC, Real.norm_of_nonneg (add_nonneg hC (norm_nonneg B))]
  rfl

/-- Pointwise errors of two sine factors control the paired-product error off the lattice. -/
theorem norm_entireSpectralPairProduct_sub_free_le_offLattice (hp : p ≠ ⊤)
    (a b A B : Coeff p) {C : ℝ} (hC : 0 ≤ C) (n : ℤ) (z : ℂ) (hz : z ∉ freeLattice)
    (hs : ‖Complex.sin z‖ ≤ C)
    (ha : ‖restoredSineProduct a n z-Complex.sin z‖ ≤ ‖A n‖)
    (hb : ‖restoredSineProduct b n z-Complex.sin z‖ ≤ ‖B n‖) :
    ‖entireSpectralPairProduct (displacedRoots a) (displacedRoots b) z-
      ((freeDiscriminant z)^2-4)‖ ≤ ‖spectralPairErrorMajorant C A B n‖ := by
  have hB := lp.norm_apply_le_norm (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' B n
  have hfb : ‖restoredSineProduct b n z‖ ≤ C+‖B‖ :=
    (norm_le_norm_sub_add _ _).trans (by linarith)
  have he : entireSpectralPairProduct (displacedRoots a) (displacedRoots b) z-
      ((freeDiscriminant z)^2-4) = -4*((restoredSineProduct a n z-Complex.sin z)*
      restoredSineProduct b n z+Complex.sin z*(restoredSineProduct b n z-Complex.sin z)) := by
    rw [entireSpectralPairProduct_eq_restored hp a b n z hz]
    have hs := Complex.sin_sq_add_cos_sq z
    unfold freeDiscriminant
    linear_combination -4*hs
  rw [he, norm_mul, norm_spectralPairErrorMajorant_apply hC]
  norm_num only [norm_neg, Complex.norm_ofNat]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply (norm_add_le _ _).trans
  simp only [norm_mul]
  have h := add_le_add (mul_le_mul ha hfb (norm_nonneg _) (norm_nonneg _))
    (mul_le_mul hs hb (norm_nonneg _) hC)
  simpa only [mul_comm ‖A n‖] using h

end NLS.ZakharovShabat
