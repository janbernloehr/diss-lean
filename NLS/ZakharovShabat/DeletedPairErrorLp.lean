import NLS.ZakharovShabat.DeletedPairErrorMajorants

/-!
# Uniform lp estimates for the deleted-product errors

On displacement norm balls, one common norm bound controls value majorants
on half-pi discs and derivative majorants on quarter-pi discs. Arbitrary
simultaneous samples in those discs therefore give lp error sequences.
-/

noncomputable section
open NLS.Fourier
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Values and derivatives of the remaining-product error have uniformly bounded lp majorants. -/
theorem exists_uniform_deletedPairError_majorants (hp1 : 1 < p) (hp : p ≠ ⊤)
    {R : ℝ} (hR : 0 ≤ R) : ∃ K : ℝ, 0 ≤ K ∧ ∀ a b : Coeff p, ‖a‖ ≤ R → ‖b‖ ≤ R →
      ∃ A : Coeff p, ‖A‖ ≤ K ∧
        (∀ (n : ℤ) (z : ℂ), ‖z-(Real.pi : ℂ)*n‖ ≤ Real.pi/2 → ‖deletedPairError a b n z‖ ≤ ‖A n‖) ∧
        (∀ (n : ℤ) (z : ℂ), ‖z-(Real.pi : ℂ)*n‖ ≤ Real.pi/4 →
          ‖deriv (deletedPairError a b n) z‖ ≤ (4/Real.pi)*‖A n‖) := by
  obtain ⟨C,hC,hquot⟩ := exists_bound_freeSineQuotient (Real.pi/2)
  let M := (hilbertTransformBound hp1 hp+‖hilbertSquareCoeffs‖)*(R/Real.pi)+
    Real.exp (absoluteSampledRowConstant hp*(R/Real.pi))*(absoluteSampledRowConstant hp*(R/Real.pi))^2
  have hM : 0 ≤ M := (norm_nonneg _).trans
    (norm_freeDiscProductMajorant_le hp1 hp (0 : Coeff p) (by simpa using hR))
  refine ⟨C^2*((1+M)*M+M),by positivity,fun a b ha hb => ?_⟩
  let A := freeDiscProductMajorant hp1 hp a
  let B := freeDiscProductMajorant hp1 hp b
  have hA : ‖A‖ ≤ M := norm_freeDiscProductMajorant_le hp1 hp a ha
  have hB : ‖B‖ ≤ M := norm_freeDiscProductMajorant_le hp1 hp b hb
  have hv := norm_deletedPairError_le_on_disc hp a b A B hC hquot
    (norm_freeDiscRelativeProduct_sub_one_le hp1 hp a) (norm_freeDiscRelativeProduct_sub_one_le hp1 hp b)
  refine ⟨deletedPairErrorMajorant C A B,?_,hv,norm_deriv_deletedPairError_le_on_disc hp a b _ hv⟩
  apply (norm_deletedPairErrorMajorant_le C A B).trans
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg C)
  exact add_le_add (mul_le_mul (add_le_add le_rfl hB) hA (norm_nonneg _) (by positivity)) hB

/-- Arbitrary half-pi-disc samples of the remaining-product error form an lp sequence. -/
theorem memℓp_deletedPairError (hp1 : 1 < p) (hp : p ≠ ⊤) (a b : Coeff p)
    (z : ℤ → ℂ) (hz : ∀ n, ‖z n-(Real.pi : ℂ)*n‖ ≤ Real.pi/2) :
    Memℓp (fun n => deletedPairError a b n (z n)) p := by
  obtain ⟨_,_,h⟩ := exists_uniform_deletedPairError_majorants hp1 hp
    ((norm_nonneg a).trans (le_max_left ‖a‖ ‖b‖))
  obtain ⟨A,_,hv,_⟩ := h a b (le_max_left _ _) (le_max_right _ _)
  exact (lp.memℓp A).mono' (fun n => hv n (z n) (hz n))

/-- Arbitrary quarter-pi-disc samples of the derivative error form an lp sequence. -/
theorem memℓp_deriv_deletedPairError (hp1 : 1 < p) (hp : p ≠ ⊤) (a b : Coeff p)
    (z : ℤ → ℂ) (hz : ∀ n, ‖z n-(Real.pi : ℂ)*n‖ ≤ Real.pi/4) :
    Memℓp (fun n => deriv (deletedPairError a b n) (z n)) p := by
  obtain ⟨_,_,h⟩ := exists_uniform_deletedPairError_majorants hp1 hp
    ((norm_nonneg a).trans (le_max_left ‖a‖ ‖b‖))
  obtain ⟨A,_,_,hd⟩ := h a b (le_max_left _ _) (le_max_right _ _)
  apply (lp.memℓp (((4/Real.pi : ℝ) : ℂ) • A)).mono'
  intro n
  simpa only [lp.coeFn_smul,Pi.smul_apply,norm_smul,Complex.norm_real,
    Real.norm_of_nonneg (by positivity : 0 ≤ 4/Real.pi)] using hd n (z n) (hz n)

end NLS.ZakharovShabat
