import NLS.ZakharovShabat.BoundaryCharacteristicProducts
import NLS.ZakharovShabat.RestoredSineProductLp
import NLS.ZakharovShabat.FreeHalfDiscGeometry
import NLS.ComplexAnalysis.DiscBounds

/-!
# Locally uniform single-boundary-product errors on free discs

The generic restored sine product majorant is transferred to the actual
entire boundary characteristic. Maximum modulus fills the free center.
This is the product estimate used in Lemma D.9 and in Lemma 9.2(iii).
-/

noncomputable section
open Set Metric Complex
open NLS.Fourier
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The entire product of a displaced root sequence. -/
def displacedBoundaryProduct (a : Coeff p) : ℂ → ℂ :=
  boundaryCharacteristicProduct (fun k => (Real.pi : ℂ)*k+a k)

/-- Off the free lattice, the actual entire product is the local restored
sine product, for any selected free disc. -/
theorem displacedBoundaryProduct_eq_restored_offLattice
    (hp : p ≠ ⊤) (a : Coeff p) (n : ℤ) (z : ℂ) (hz : z ∉ freeLattice) :
    displacedBoundaryProduct a z = restoredSineProduct a n z := by
  have hξ : Memℓp (fun k : ℤ => ((Real.pi : ℂ)*k+a k)-(Real.pi : ℂ)*k) p := by
    simpa only [add_sub_cancel_left] using (lp.memℓp a)
  rw [displacedBoundaryProduct,boundaryCharacteristicProduct,
    entireSingleSpectralProduct_eq_offLattice hp _ hξ z hz,
    singleSpectralProductFormula]
  have he := restoredSineProduct_eq_offLattice hp a n z hz
  rw [he]
  simp only [spectralRelativeFactor]
  ring

/-- A single `ℓᵖ` majorant controls the actual entire boundary product
throughout every closed half-π disc, including its free center. -/
theorem norm_displacedBoundaryProduct_sub_sin_le
    (hp1 : 1 < p) (hp : p ≠ ⊤) (a : Coeff p)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ (n : ℤ) (z : ℂ),
      ‖z-(Real.pi : ℂ)*n‖ ≤ Real.pi/2 → ‖freeSineQuotient n z‖ ≤ C)
    (n : ℤ) (z : ℂ) (hz : ‖z-(Real.pi : ℂ)*n‖ ≤ Real.pi/2) :
    ‖displacedBoundaryProduct a z-sin z‖ ≤
      ‖restoredSineProductMajorant hp1 hp C a n‖ := by
  have hξ : Memℓp (fun k : ℤ => ((Real.pi : ℂ)*k+a k)-(Real.pi : ℂ)*k) p := by
    simpa only [add_sub_cancel_left] using (lp.memℓp a)
  have hf : Differentiable ℂ (fun w => displacedBoundaryProduct a w-sin w) := by
    intro w
    exact (analyticOnNhd_boundaryCharacteristicProduct hp _ hξ w (mem_univ _)).differentiableAt.sub
      (by fun_prop)
  apply Complex.norm_le_of_forall_mem_frontier_norm_le
    (isBounded_ball (x := (Real.pi : ℂ)*n) (r := Real.pi/2)) hf.diffContOnCl
  · intro w hw
    rw [frontier_ball _ (by positivity : Real.pi/2 ≠ 0)] at hw
    have hfree := freeHalfSphere_notMem_freeLattice n hw
    rw [displacedBoundaryProduct_eq_restored_offLattice hp a n w hfree]
    exact norm_restoredSineProduct_sub_sin_le hp1 hp hC hbound a n w
      (by simpa only [mem_sphere, dist_eq_norm] using hw.le)
  · simpa only [closure_ball ((Real.pi : ℂ)*n) (by positivity : Real.pi/2 ≠ 0), mem_closedBall,
      dist_eq_norm] using hz

/-- Cauchy's estimate controls the derivative error on every closed quarter-π disc. -/
theorem norm_deriv_displacedBoundaryProduct_sub_cos_le
    (hp1 : 1 < p) (hp : p ≠ ⊤) (a : Coeff p)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ (n : ℤ) (z : ℂ),
      ‖z-(Real.pi : ℂ)*n‖ ≤ Real.pi/2 → ‖freeSineQuotient n z‖ ≤ C)
    (n : ℤ) (z : ℂ) (hz : ‖z-(Real.pi : ℂ)*n‖ ≤ Real.pi/4) :
    ‖deriv (displacedBoundaryProduct a) z-cos z‖ ≤
      (4/Real.pi)*‖restoredSineProductMajorant hp1 hp C a n‖ := by
  have hξ : Memℓp (fun k : ℤ => ((Real.pi : ℂ)*k+a k)-(Real.pi : ℂ)*k) p := by
    simpa only [add_sub_cancel_left] using (lp.memℓp a)
  have hf : Differentiable ℂ (fun w => displacedBoundaryProduct a w-sin w) := by
    intro w
    exact (analyticOnNhd_boundaryCharacteristicProduct hp _ hξ w (mem_univ _)).differentiableAt.sub
      (by fun_prop)
  have hd := NLS.ComplexAnalysis.norm_deriv_le_of_closedDisc_bound hf ((Real.pi : ℂ)*n)
    (by linarith [Real.pi_pos] : Real.pi/4 < Real.pi/2) _
    (norm_displacedBoundaryProduct_sub_sin_le hp1 hp a hC hbound n) hz
  have hderiv : deriv (fun w => displacedBoundaryProduct a w-sin w) z =
      deriv (displacedBoundaryProduct a) z-cos z := by
    simpa only [displacedBoundaryProduct, Complex.deriv_sin] using
      (deriv_fun_sub ((analyticOnNhd_boundaryCharacteristicProduct hp _ hξ z
        (mem_univ _)).differentiableAt) (by fun_prop : DifferentiableAt ℂ sin z))
  rw [hderiv] at hd
  convert hd using 1
  ring

/-- A uniform displacement-norm ball has one bound for both the product and
its derivative error majorants. -/
theorem exists_uniform_displacedBoundaryProduct_majorants
    (hp1 : 1 < p) (hp : p ≠ ⊤) {R : ℝ} (hR : 0 ≤ R) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ a : Coeff p, ‖a‖ ≤ R →
      ∃ A : Coeff p, ‖A‖ ≤ K ∧
        (∀ (n : ℤ) (z : ℂ), ‖z-(Real.pi : ℂ)*n‖ ≤ Real.pi/2 →
          ‖displacedBoundaryProduct a z-sin z‖ ≤ ‖A n‖) ∧
        (∀ (n : ℤ) (z : ℂ), ‖z-(Real.pi : ℂ)*n‖ ≤ Real.pi/4 →
          ‖deriv (displacedBoundaryProduct a) z-cos z‖ ≤ (4/Real.pi)*‖A n‖) := by
  obtain ⟨C, hC, hbound⟩ := exists_bound_freeSineQuotient (Real.pi/2)
  let B := (hilbertTransformBound hp1 hp+‖hilbertSquareCoeffs‖)*(R/Real.pi)+
    Real.exp (absoluteSampledRowConstant hp*(R/Real.pi))*(absoluteSampledRowConstant hp*(R/Real.pi))^2
  have hB : 0 ≤ B := by
    have := hilbertTransformBound_nonneg hp1 hp
    dsimp [B]
    positivity
  refine ⟨C*((Real.pi/2+R)*B+R), by positivity, fun a ha =>
    ⟨restoredSineProductMajorant hp1 hp C a, ?_,
      norm_displacedBoundaryProduct_sub_sin_le hp1 hp a hC hbound,
      norm_deriv_displacedBoundaryProduct_sub_cos_le hp1 hp a hC hbound⟩⟩
  apply (norm_restoredSineProductMajorant_le hp1 hp hC a).trans
  apply mul_le_mul_of_nonneg_left _ hC
  exact add_le_add (mul_le_mul (add_le_add le_rfl ha)
    (norm_freeDiscProductMajorant_le hp1 hp a ha) (norm_nonneg _) (by positivity)) ha

/-- Arbitrary samples in the free quarter-discs give ℓᵖ value and derivative
errors for the entire boundary product. -/
theorem memℓp_displacedBoundaryProduct_errors
    (hp1 : 1 < p) (hp : p ≠ ⊤) (a : Coeff p) (z : ℤ → ℂ)
    (hz : ∀ n : ℤ, ‖z n-(Real.pi : ℂ)*n‖ ≤ Real.pi/4) :
    Memℓp (fun n => displacedBoundaryProduct a (z n)-sin (z n)) p ∧
      Memℓp (fun n => deriv (displacedBoundaryProduct a) (z n)-cos (z n)) p := by
  obtain ⟨C, hC, hbound⟩ := exists_bound_freeSineQuotient (Real.pi/2)
  let A := restoredSineProductMajorant hp1 hp C a
  constructor
  · exact (lp.memℓp A).mono' (fun n =>
      norm_displacedBoundaryProduct_sub_sin_le hp1 hp a hC hbound n (z n)
        (by linarith [Real.pi_pos, hz n]))
  · let B : Coeff p := ((4/Real.pi : ℝ) : ℂ) • A
    apply (lp.memℓp B).mono'
    intro n
    have hd := norm_deriv_displacedBoundaryProduct_sub_cos_le hp1 hp a hC hbound n
      (z n) (hz n)
    simpa only [B, A, lp.coeFn_smul, Pi.smul_apply, norm_smul, Complex.norm_real,
      Real.norm_of_nonneg (by positivity : 0 ≤ 4/Real.pi)] using hd

end NLS.ZakharovShabat
