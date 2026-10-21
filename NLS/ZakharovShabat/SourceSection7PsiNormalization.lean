import NLS.ZakharovShabat.SourceStandardRootOmittedProduct
import NLS.ZakharovShabat.SourcePsiFree

noncomputable section
open Filter Topology Complex
namespace NLS.ZakharovShabat

/-- The literal product printed on page46, with the fixed denominator pi_n in every factor. -/
def section7PrintedPsiPartial (n : ℤ) (N : ℕ) (roots : ℤ → ℂ) (z : ℂ) : ℂ :=
  (-2 / singleSpectralDenominator n) *
    ∏ m ∈ (Finset.Icc (-(N:ℤ)) (N:ℤ)).erase n, (roots m-z)/singleSpectralDenominator n

/-- The printed product specialized to the free source, omitted index zero and spectral parameter zero. -/
def section7PrintedPsiFreePartial (N : ℕ) : ℂ :=
  -2 * ∏ m ∈ (Finset.Icc (-(N:ℤ)) (N:ℤ)).erase 0, (Real.pi:ℂ)*m

/-- Each symmetric free pair has norm at least four under the printed normalization. -/
theorem section7PrintedPsiFreePair_norm_lower (j : ℕ) :
    (4:ℝ) ≤ ‖omittedSymmetricPairFactor (fun m : ℤ => (Real.pi:ℂ)*m) 0 j‖ := by
  have hp : (j:ℤ)+1 ≠ 0 := by omega
  have hn : -((j:ℤ)+1) ≠ 0 := by omega
  simp only [omittedSymmetricPairFactor,if_neg hp,if_neg hn,Int.cast_neg,mul_neg,
    norm_mul,norm_neg]
  have hk : ‖(((j:ℤ)+1 : ℤ) : ℂ)‖ = (j:ℝ)+1 := by
    norm_cast
  rw [hk,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  have hj : (0:ℝ) ≤ j := by positivity
  nlinarith [Real.pi_gt_three, sq_nonneg ((j:ℝ)+1),mul_self_nonneg Real.pi,
    mul_nonneg hj Real.pi_pos.le]

/-- The norms of the literal printed cutoffs grow at least geometrically. -/
theorem section7PrintedPsiFreePartial_norm_lower (N : ℕ) :
    2*(4:ℝ)^N ≤ ‖section7PrintedPsiFreePartial N‖ := by
  rw [section7PrintedPsiFreePartial,prod_Icc_erase_eq_omittedSymmetricPairs]
  simp only [if_true,one_mul,norm_mul,norm_neg,norm_ofNat,norm_prod]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  calc
    (4:ℝ)^N = ∏ j ∈ Finset.range N, (4:ℝ) := by simp
    _ ≤ _ := Finset.prod_le_prod (fun _ _ => by norm_num) (fun j _ => section7PrintedPsiFreePair_norm_lower j)

/-- The printed free product diverges to infinity in norm. -/
theorem section7PrintedPsiFreePartial_norm_tendsto :
    Tendsto (fun N => ‖section7PrintedPsiFreePartial N‖) atTop atTop := by
  apply tendsto_atTop_mono section7PrintedPsiFreePartial_norm_lower
  exact (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ) < 4)).const_mul_atTop (by norm_num)

/-- The printed free product cannot converge to any complex number. -/
theorem section7PrintedPsiFreePartial_no_limit (z : ℂ) :
    ¬ Tendsto section7PrintedPsiFreePartial atTop (𝓝 z) := by
  intro h
  exact not_tendsto_nhds_of_tendsto_atTop section7PrintedPsiFreePartial_norm_tendsto ‖z‖ h.norm

/-- The growth counterexample is exactly the source's printed root product. -/
theorem section7PrintedPsiPartial_zero (N : ℕ) :
    section7PrintedPsiPartial 0 N (displacedRoots (0 : Coeff 2)) 0 =
      section7PrintedPsiFreePartial N := by
  simp [section7PrintedPsiPartial,section7PrintedPsiFreePartial,singleSpectralDenominator,displacedRoots]

/-- The corrected mode-dependent denominator gives the exact free value at every cutoff. -/
theorem section7CorrectedPsiPartial_zero (N : ℕ) :
    -2 * jointDeletedSingleSpectralPartialProduct (p := 2) 0 N (0,0) = (-2:ℂ) := by
  have hf (m : ℤ) (hm : m ∈ (Finset.Icc (-(N:ℤ)) (N:ℤ)).erase 0) :
      singleSpectralFactor (displacedRoots (0:Coeff 2)) 0 m = 1 := by
    have hm0 := (Finset.mem_erase.mp hm).1
    simp [singleSpectralFactor,displacedRoots,singleSpectralDenominator,hm0,Real.pi_ne_zero]
  simp only [jointDeletedSingleSpectralPartialProduct,singleSpectralDenominator]
  rw [Finset.prod_congr rfl hf]
  simp

/-- In particular, the literal printed product cannot represent the normalized actual free psi-function. -/
theorem section7PrintedPsiPartial_not_free_psi :
    ¬ Tendsto (fun N => section7PrintedPsiPartial 0 N (displacedRoots (0:Coeff 2)) 0)
      atTop (𝓝 (sourcePsiFree 0 0)) := by
  simpa only [section7PrintedPsiPartial_zero] using
    section7PrintedPsiFreePartial_no_limit (sourcePsiFree 0 0)

end NLS.ZakharovShabat
