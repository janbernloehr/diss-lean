import NLS.ZakharovShabat.EntireSpectralPairLp
import NLS.ZakharovShabat.ParitySpectralFamilies
import NLS.ZakharovShabat.SpectralProductsVerticalLimit

/-!
# Common lp disc bounds for both spectral parity products

Affine rescaling transfers the entire paired-product estimate to the matching
even and odd free centers, with the original normalization signs retained.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The complete displacement coefficients after parity rescaling. -/
def parityDisplacement (hp : p ≠ ⊤) (ξ : ℤ → ℂ)
    (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p) (j : ℤ) : Coeff p :=
  ⟨_, memℓp_parityRescale hp ξ hξ j⟩

/-- Reconstructing the rescaled roots recovers the exact parity sequence. -/
theorem displacedRoots_parityDisplacement (hp : p ≠ ⊤) (ξ : ℤ → ℂ)
    (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p) (j : ℤ) :
    displacedRoots (parityDisplacement hp ξ hξ j) = parityRescale ξ j := by
  funext n
  simp [displacedRoots, parityDisplacement]

/-- Parity rescaling halves the distance to the corresponding free center. -/
theorem norm_parity_rescale_sub_center (z : ℂ) (n j : ℤ) :
    ‖(z-(Real.pi : ℂ)*j)/2-(Real.pi : ℂ)*n‖ =
      ‖z-(Real.pi : ℂ)*(2*n+j : ℤ)‖/2 := by
  have he : (z-(Real.pi : ℂ)*j)/2-(Real.pi : ℂ)*n =
      (z-(Real.pi : ℂ)*(2*n+j : ℤ))/2 := by push_cast; ring
  rw [he, norm_div, Complex.norm_ofNat]

/-- Both parity products have common lp error majorants, uniformly on displacement norm balls. -/
theorem exists_uniform_parityProduct_majorants (hp1 : 1 < p) (hp : p ≠ ⊤)
    {R : ℝ} (hR : 0 ≤ R) : ∃ K : ℝ, 0 ≤ K ∧ ∀ (ξ η : ℤ → ℂ)
      (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p)
      (hη : Memℓp (fun n => η n-(Real.pi : ℂ)*n) p),
      ‖(⟨_,hξ⟩ : Coeff p)‖ ≤ R → ‖(⟨_,hη⟩ : Coeff p)‖ ≤ R →
      ∃ A B : Coeff p, ‖A‖ ≤ K ∧ ‖B‖ ≤ K ∧
        (∀ (n : ℤ) (z : ℂ), ‖z-(Real.pi : ℂ)*(2*n : ℤ)‖ ≤ Real.pi →
          ‖evenSpectralPairProduct ξ η z-(freeDiscriminant z-2)‖ ≤ ‖A n‖) ∧
        (∀ (n : ℤ) (z : ℂ), ‖z-(Real.pi : ℂ)*(2*n+1 : ℤ)‖ ≤ Real.pi →
          ‖oddSpectralPairProduct ξ η z-(freeDiscriminant z+2)‖ ≤ ‖B n‖) := by
  obtain ⟨K, hK, h⟩ := exists_uniform_spectralPairError_majorants hp1 hp hR
  refine ⟨K, hK, fun ξ η hξ hη hRξ hRη => ?_⟩
  have hx (j : ℤ) : ‖parityDisplacement hp ξ hξ j‖ ≤ R :=
    (norm_parityRescale_displacement_le hp ξ hξ j).trans hRξ
  have hy (j : ℤ) : ‖parityDisplacement hp η hη j‖ ≤ R :=
    (norm_parityRescale_displacement_le hp η hη j).trans hRη
  obtain ⟨A, hA, he, _⟩ := h (parityDisplacement hp ξ hξ 0) (parityDisplacement hp η hη 0) (hx 0) (hy 0)
  obtain ⟨B, hB, ho, _⟩ := h (parityDisplacement hp ξ hξ 1) (parityDisplacement hp η hη 1) (hx 1) (hy 1)
  refine ⟨A, B, hA, hB, ?_, ?_⟩
  · intro n z hz
    have hd : ‖z/2-(Real.pi : ℂ)*n‖ ≤ Real.pi/2 := by
      have hh := norm_parity_rescale_sub_center z n 0
      simp only [Int.cast_zero, mul_zero, sub_zero, add_zero] at hh
      rw [hh]
      exact div_le_div_of_nonneg_right hz (by norm_num)
    have hv := he n (z/2) hd
    simpa only [spectralPairError, displacedRoots_parityDisplacement, freeDiscriminant_half_sq_sub_four,
      evenSpectralPairProduct] using hv
  · intro n z hz
    have hd : ‖(z-(Real.pi : ℂ))/2-(Real.pi : ℂ)*n‖ ≤ Real.pi/2 := by
      have hh := norm_parity_rescale_sub_center z n 1
      simp only [Int.cast_one, mul_one] at hh
      rw [hh]
      exact div_le_div_of_nonneg_right hz (by norm_num)
    have hv := ho n ((z-(Real.pi : ℂ))/2) hd
    simp only [spectralPairError, displacedRoots_parityDisplacement,
      freeDiscriminant_odd_half_sq_sub_four, sub_neg_eq_add] at hv
    change ‖-entireSpectralPairProduct (parityRescale ξ 1) (parityRescale η 1) ((z-(Real.pi : ℂ))/2)-
      (freeDiscriminant z+2)‖ ≤ _
    rw [show -entireSpectralPairProduct (parityRescale ξ 1) (parityRescale η 1) ((z-(Real.pi : ℂ))/2)-
      (freeDiscriminant z+2) = -(entireSpectralPairProduct (parityRescale ξ 1) (parityRescale η 1)
        ((z-(Real.pi : ℂ))/2)+(freeDiscriminant z+2)) by ring, norm_neg]
    exact hv

end NLS.ZakharovShabat
