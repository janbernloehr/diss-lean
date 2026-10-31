import NLS.Fourier.SampledHilbert
import NLS.SequenceSpaces.ExponentEmbedding

/-! # The paired perturbations in the proof of Lemma D.4 -/
noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The perturbation of the nonzero-index normalized factor; its zero entry is totalized. -/
def appendixDZeroDeletedPerturbation (a : Coeff p) (z : ℂ) (m : ℤ) : ℂ :=
  (a m-z)/((Real.pi:ℂ)*m)

omit [Fact (1 ≤ p)] in
/-- Pairing opposite indices cancels the spectral parameter in the linear term. -/
theorem appendixDZeroDeletedPerturbation_add_neg (a : Coeff p) (z : ℂ) (m : ℤ) :
    appendixDZeroDeletedPerturbation a z m+appendixDZeroDeletedPerturbation a z (-m) =
      (a m-a (-m))/((Real.pi:ℂ)*m) := by
  simp only [appendixDZeroDeletedPerturbation,Int.cast_neg,mul_neg,div_neg]
  ring

omit [Fact (1 ≤ p)] in
/-- The paired quadratic term has exactly the source's square denominator. -/
theorem appendixDZeroDeletedPerturbation_mul_neg (a : Coeff p) (z : ℂ) (m : ℤ) :
    appendixDZeroDeletedPerturbation a z m*appendixDZeroDeletedPerturbation a z (-m) =
      (a m-z)*(z-a (-m))/((Real.pi:ℂ)*m)^2 := by
  simp only [appendixDZeroDeletedPerturbation,Int.cast_neg,mul_neg,div_neg]
  ring

/-- The paired linear term is absolutely summable, also at the p=1 endpoint. -/
theorem summable_norm_appendixDZeroDeletedPerturbation_add_neg (hp : p ≠ ⊤)
    (a : Coeff p) (z : ℂ) :
    Summable (fun m : ℤ => ‖appendixDZeroDeletedPerturbation a z m+
      appendixDZeroDeletedPerturbation a z (-m)‖) := by
  let q : ℝ≥0∞ := max p 2
  have hq1 : 1 < q := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  let : Fact (1 ≤ q) := ⟨hq1.le⟩
  have hq : q ≠ ⊤ := (max_lt hp.lt_top (by norm_num)).ne
  have h := NLS.Fourier.summable_norm_hilbertSeries_of_finite hq1 hq
    (Coeff.exponentInclusion (le_max_left p 2) a) 0
  have hbase : Summable (fun m : ℤ => ‖a m/(m:ℂ)‖) := by
    simpa only [Int.cast_zero,sub_zero,Coeff.exponentInclusion_apply] using h
  have hscaled : Summable (fun m : ℤ => ‖a m/((Real.pi:ℂ)*m)‖) := by
    apply (hbase.mul_right ‖(Real.pi:ℂ)‖⁻¹).congr
    intro m
    simp only [norm_mul,norm_inv,div_eq_mul_inv,mul_inv_rev]
    ring
  have hneg : Summable (fun m : ℤ => ‖a (-m)/((Real.pi:ℂ)*m)‖) := by
    simpa only [Function.comp_def,Int.cast_neg,mul_neg,div_neg,norm_neg] using
      hscaled.comp_injective (neg_injective : Function.Injective (fun m : ℤ => -m))
  apply (hscaled.add hneg).of_nonneg_of_le (fun _ => norm_nonneg _)
  intro m
  rw [appendixDZeroDeletedPerturbation_add_neg,sub_div]
  exact norm_sub_le _ _

/-- The paired quadratic term is absolutely summable by the reciprocal-square kernel. -/
theorem summable_norm_appendixDZeroDeletedPerturbation_mul_neg (a : Coeff p) (z : ℂ) :
    Summable (fun m : ℤ => ‖appendixDZeroDeletedPerturbation a z m*
      appendixDZeroDeletedPerturbation a z (-m)‖) := by
  have hs : Summable (fun m : ℤ => ‖NLS.Fourier.hilbertSquareCoeffs m‖) := by
    simpa using NLS.Fourier.hilbertSquareCoeffs.property.summable
      (by norm_num : 0 < (1:ℝ≥0∞).toReal)
  have he (m : ℤ) : ‖appendixDZeroDeletedPerturbation a z m*
      appendixDZeroDeletedPerturbation a z (-m)‖ =
      (Real.pi⁻¹)^2*(‖a m-z‖*‖a (-m)-z‖)*‖NLS.Fourier.hilbertSquareCoeffs m‖ := by
    simp only [appendixDZeroDeletedPerturbation,Int.cast_neg,mul_neg,norm_mul,norm_neg,
      Complex.norm_real,Real.norm_of_nonneg Real.pi_pos.le,NLS.Fourier.hilbertSquareCoeffs_apply,
      norm_pow,NLS.Fourier.hilbertKernel,norm_neg,norm_inv,div_eq_mul_inv,mul_inv_rev]
    ring
  have hb (m : ℤ) : ‖a m-z‖ ≤ ‖a‖+‖z‖ :=
    (norm_sub_le _ _).trans (add_le_add
      (lp.norm_apply_le_norm (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' a m) le_rfl)
  apply (hs.mul_left ((Real.pi⁻¹)^2*(‖a‖+‖z‖)^2)).of_nonneg_of_le (fun _ => norm_nonneg _)
  intro m
  rw [he]
  have hh : ‖a m-z‖*‖a (-m)-z‖ ≤ (‖a‖+‖z‖)^2 := by
    simpa only [pow_two] using mul_le_mul (hb m) (hb (-m)) (norm_nonneg _) (by positivity)
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh (sq_nonneg _)) (norm_nonneg _)

end NLS.ZakharovShabat
