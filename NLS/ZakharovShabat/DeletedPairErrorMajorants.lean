import NLS.ZakharovShabat.DeletedPairRelativeFormula
import NLS.ZakharovShabat.FreeSineQuotientAnalytic
import NLS.ZakharovShabat.FreeHalfDiscGeometry
import NLS.ComplexAnalysis.DiscBounds

/-!
# Disc majorants for the remaining spectral product

The difference from the squared free sine quotient has a common lp
majorant on each closed half-pi disc. Maximum modulus fills the free
center, and Cauchy's estimate controls derivatives on quarter-pi discs.
-/

noncomputable section
open Set Metric
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The remaining product error relative to the filled squared free quotient. -/
def deletedPairError (a b : Coeff p) (n : ℤ) (z : ℂ) : ℂ :=
  deletedSpectralPairProduct (displacedRoots a) (displacedRoots b) n z-(freeSineQuotient n z)^2

/-- The remaining-product error is entire at fixed index. -/
theorem differentiable_deletedPairError (hp : p ≠ ⊤) (a b : Coeff p) (n : ℤ) :
    Differentiable ℂ (deletedPairError a b n) :=
  (differentiableOn_univ.mp (analyticOnNhd_deletedSpectralPairProduct hp _ _
    (memℓp_displacedRoots a) (memℓp_displacedRoots b) n).differentiableOn).sub
    ((differentiable_freeSineQuotient n).pow 2)

/-- A positive coefficient sequence bounding the two relative-product errors. -/
def deletedPairErrorMajorant (C : ℝ) (A B : Coeff p) : Coeff p :=
  ((C^2 : ℝ) : ℂ) • (((1+‖B‖ : ℝ) : ℂ) • Coeff.magnitude A+Coeff.magnitude B)

/-- The chosen majorant adds the error bounds without cancellation. -/
theorem norm_deletedPairErrorMajorant_apply (C : ℝ) (A B : Coeff p) (n : ℤ) :
    ‖deletedPairErrorMajorant C A B n‖ = C^2*((1+‖B‖)*‖A n‖+‖B n‖) := by
  simp only [deletedPairErrorMajorant,lp.coeFn_smul,Pi.smul_apply,lp.coeFn_add,Pi.add_apply,
    smul_eq_mul,Coeff.magnitude_apply,← Complex.ofReal_add,← Complex.ofReal_mul,Complex.norm_real]
  rw [Real.norm_of_nonneg (by positivity)]

/-- The majorant's lp norm has an explicit bound in terms of the two input norms. -/
theorem norm_deletedPairErrorMajorant_le (C : ℝ) (A B : Coeff p) :
    ‖deletedPairErrorMajorant C A B‖ ≤ C^2*((1+‖B‖)*‖A‖+‖B‖) := by
  rw [deletedPairErrorMajorant,norm_smul,Complex.norm_real,Real.norm_of_nonneg (sq_nonneg C)]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg C)
  apply (norm_add_le _ _).trans
  simp only [norm_smul,Coeff.norm_magnitude,Complex.norm_real,
    Real.norm_of_nonneg (by positivity : 0 ≤ 1+‖B‖)]
  rfl

/-- The exact relative formula yields an error bound without excluding actual endpoints. -/
theorem norm_deletedPairError_le_offLattice (hp : p ≠ ⊤) (a b A B : Coeff p)
    {C : ℝ} (hC : 0 ≤ C) (n : ℤ) (z : ℂ) (hz : z ∉ freeLattice)
    (hq : ‖freeSineQuotient n z‖ ≤ C)
    (ha : ‖freeDiscRelativeProduct a n z-1‖ ≤ ‖A n‖)
    (hb : ‖freeDiscRelativeProduct b n z-1‖ ≤ ‖B n‖) :
    ‖deletedPairError a b n z‖ ≤ ‖deletedPairErrorMajorant C A B n‖ := by
  have hB := lp.norm_apply_le_norm (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' B n
  have hprod : ‖freeDiscRelativeProduct b n z‖ ≤ 1+‖B‖ := by
    have h := norm_le_norm_sub_add (freeDiscRelativeProduct b n z) (1 : ℂ)
    simp only [norm_one] at h
    linarith
  have he : deletedPairError a b n z = (freeSineQuotient n z)^2*
      ((freeDiscRelativeProduct a n z-1)*freeDiscRelativeProduct b n z+
        (freeDiscRelativeProduct b n z-1)) := by
    rw [deletedPairError,deletedSpectralPairProduct_eq_relative hp a b n z hz]
    ring
  rw [he,norm_mul,norm_pow,norm_deletedPairErrorMajorant_apply]
  have hq2 : ‖freeSineQuotient n z‖^2 ≤ C^2 := by
    simpa only [pow_two] using mul_le_mul hq hq (norm_nonneg _) hC
  apply mul_le_mul hq2 _ (norm_nonneg _) (sq_nonneg C)
  apply (norm_add_le _ _).trans
  rw [norm_mul]
  have h := add_le_add (mul_le_mul ha hprod (norm_nonneg _) (norm_nonneg _)) hb
  simpa only [mul_comm ‖A n‖] using h

/-- Maximum modulus extends the common majorant to the entire closed half-pi disc. -/
theorem norm_deletedPairError_le_on_disc (hp : p ≠ ⊤) (a b A B : Coeff p)
    {C : ℝ} (hC : 0 ≤ C)
    (hq : ∀ (n : ℤ) (z : ℂ), ‖z-(Real.pi : ℂ)*n‖ ≤ Real.pi/2 → ‖freeSineQuotient n z‖ ≤ C)
    (ha : ∀ (n : ℤ) (z : ℂ), ‖z-(Real.pi : ℂ)*n‖ ≤ Real.pi/2 →
      ‖freeDiscRelativeProduct a n z-1‖ ≤ ‖A n‖)
    (hb : ∀ (n : ℤ) (z : ℂ), ‖z-(Real.pi : ℂ)*n‖ ≤ Real.pi/2 →
      ‖freeDiscRelativeProduct b n z-1‖ ≤ ‖B n‖)
    (n : ℤ) (z : ℂ) (hz : ‖z-(Real.pi : ℂ)*n‖ ≤ Real.pi/2) :
    ‖deletedPairError a b n z‖ ≤ ‖deletedPairErrorMajorant C A B n‖ := by
  apply NLS.ComplexAnalysis.norm_le_of_sphere_bound (differentiable_deletedPairError hp a b n)
    ((Real.pi : ℂ)*n) (half_pos Real.pi_pos) _ _ hz
  intro w hw
  have hwd : ‖w-(Real.pi : ℂ)*n‖ ≤ Real.pi/2 :=
    (show ‖w-(Real.pi : ℂ)*n‖ = Real.pi/2 by simpa only [mem_sphere,dist_eq_norm] using hw).le
  exact norm_deletedPairError_le_offLattice hp a b A B hC n w
    (freeHalfSphere_notMem_freeLattice n hw) (hq n w hwd) (ha n w hwd) (hb n w hwd)

/-- Cauchy's estimate controls the derivative on the smaller source disc by the same coefficient. -/
theorem norm_deriv_deletedPairError_le_on_disc (hp : p ≠ ⊤) (a b A : Coeff p)
    (hA : ∀ (n : ℤ) (z : ℂ), ‖z-(Real.pi : ℂ)*n‖ ≤ Real.pi/2 → ‖deletedPairError a b n z‖ ≤ ‖A n‖)
    (n : ℤ) (z : ℂ) (hz : ‖z-(Real.pi : ℂ)*n‖ ≤ Real.pi/4) :
    ‖deriv (deletedPairError a b n) z‖ ≤ (4/Real.pi)*‖A n‖ := by
  have h := NLS.ComplexAnalysis.norm_deriv_le_of_closedDisc_bound (differentiable_deletedPairError hp a b n)
    ((Real.pi : ℂ)*n) (by linarith [Real.pi_pos] : Real.pi/4 < Real.pi/2) _ (hA n) hz
  convert h using 1
  ring

end NLS.ZakharovShabat
