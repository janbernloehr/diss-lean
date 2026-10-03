import NLS.ZakharovShabat.ClassicalSobolevDiscriminantError
import NLS.ZakharovShabat.ClassicalSobolevRemainderSequenceBounds
import NLS.ZakharovShabat.ClassicalHorizontalStripBounds
import NLS.ZakharovShabat.FreeCircleSeparation
import NLS.ZakharovShabat.FreeStripInverseBounds

/-! # Uniform discriminant quotient bounds on the distant G.7 contours

Free parity factors have bounded inverses on the separated circles.
The H¹ trace error is uniformly small after one cutoff, preserving a
positive lower bound on both factors and therefore on Δ²−4.
-/

noncomputable section
open Set Metric Complex
namespace NLS.ZakharovShabat

private theorem lower_of_inverse_bound (b : ℂ) (hb : b ≠ 0) (C : ℝ) (hC : 0 < C)
    (hi : ‖b⁻¹‖ ≤ C) : 1/C ≤ ‖b‖ := by
  apply (div_le_iff₀ hC).mpr
  calc
    1 = ‖b‖*‖b⁻¹‖ := by rw [← norm_mul,mul_inv_cancel₀ hb,norm_one]
    _ ≤ ‖b‖*C := mul_le_mul_of_nonneg_left hi (norm_nonneg _)

/-- Both parity factors retain a positive lower bound on every sufficiently distant contour. -/
theorem exists_classicalSobolev_contour_factor_lower
    (M : ℝ) (hM : 0 ≤ M) (r : ℝ) (hr : 0 < r) (hrπ : r ≤ Real.pi/2) :
    ∃ N : ℕ, 0 < N ∧ ∃ d : ℝ, 0 < d ∧
      ∀ (a : ScalarDomain 2 × ScalarDomain 2), ‖a‖ ≤ M → ∀ (n : ℤ), N ≤ n.natAbs →
      ∀ z : ℂ, z ∈ sphere ((Real.pi : ℂ)*(n : ℂ)) r →
      d ≤ ‖classicalDiscriminant (classicalSobolevPotential a) z-2‖ ∧
      d ≤ ‖classicalDiscriminant (classicalSobolevPotential a) z+2‖ := by
  obtain ⟨Cp,hCp,hp⟩ := exists_bound_freeDiscriminant_sub_inv_strip (2 : ℂ) (by norm_num) hr r
  obtain ⟨Cm,hCm,hm⟩ := exists_bound_freeDiscriminant_sub_inv_strip (-2 : ℂ) (by norm_num) hr r
  let C := 1+Cp+Cm
  have hC : 0 < C := by dsimp [C]; linarith
  let E := classicalSobolevErrorConstant M r
  have hE : 0 ≤ E := classicalSobolevErrorConstant_nonneg M r hM
  obtain ⟨N₀,hN₀,hcut⟩ := exists_near_free_frequency_cutoff r hr.le
  obtain ⟨N₁,hN₁⟩ := exists_nat_gt (4*E*C)
  refine ⟨max N₀ N₁,lt_of_lt_of_le hN₀ (le_max_left _ _),1/C/2,by positivity,?_⟩
  intro a ha n hn z hz
  have hzn : ‖z-(Real.pi : ℂ)*(n : ℂ)‖ = r := by simpa only [mem_sphere,dist_eq_norm] using hz
  have hsep := freeCircle_separated r hrπ n z hz
  have hfree : z ∉ freeLattice := notMem_freeLattice_of_separated hr hsep
  obtain ⟨him,_,hnorm⟩ := hcut n ((le_max_left N₀ N₁).trans hn) z hzn.le
  have hnpos : 0 < (n.natAbs : ℝ) := by
    exact_mod_cast lt_of_lt_of_le hN₀ ((le_max_left N₀ N₁).trans hn)
  have hnz : (n.natAbs : ℝ) ≤ ‖z‖ := by nlinarith [Real.two_le_pi]
  have hz0 : z ≠ 0 := norm_pos_iff.mp (hnpos.trans_le hnz)
  have hlarge : 4*E*C < (n.natAbs : ℝ) := hN₁.trans_le (by exact_mod_cast (le_max_right N₀ N₁).trans hn)
  have herr : ‖classicalDiscriminant (classicalSobolevPotential a) z-freeDiscriminant z‖ ≤ 1/C/2 := by
    apply (norm_classicalDiscriminant_sub_free_sobolev_strip_le M r a ha z hz0 him).trans
    apply (div_le_div_of_nonneg_left (by positivity : 0 ≤ 2*E) hnpos hnz).trans
    rw [div_div,div_le_div_iff₀ hnpos (by positivity)]
    nlinarith
  have hlow (b : ℂ) (hb : b^2 = 4) (hi : ‖(freeDiscriminant z-b)⁻¹‖ ≤ C) :
      1/C/2 ≤ ‖classicalDiscriminant (classicalSobolevPotential a) z-b‖ := by
    have hl := lower_of_inverse_bound (freeDiscriminant z-b)
      (freeDiscriminant_sub_ne_zero_of_sq_eq_four b hb z hfree) C hC hi
    have ht := norm_sub_norm_le (freeDiscriminant z-b) (classicalDiscriminant (classicalSobolevPotential a) z-b)
    rw [sub_sub_sub_cancel_right,norm_sub_rev (freeDiscriminant z)
      (classicalDiscriminant (classicalSobolevPotential a) z)] at ht
    linarith
  constructor
  · exact hlow 2 (by norm_num) ((hp z him hsep).trans (by dsimp [C]; linarith))
  · simpa only [sub_neg_eq_add] using hlow (-2) (by norm_num)
      ((hm z him hsep).trans (by dsimp [C]; linarith))

/-- The midpoint-gradient quotient is uniformly bounded on all distant contours and the whole H¹ ball. -/
theorem exists_classicalSobolev_contour_discriminant_quotient_bound
    (M : ℝ) (hM : 0 ≤ M) (r : ℝ) (hr : 0 < r) (hrπ : r ≤ Real.pi/2) :
    ∃ N : ℕ, 0 < N ∧ ∃ δ Q : ℝ, 0 < δ ∧ 0 ≤ Q ∧
      ∀ (a : ScalarDomain 2 × ScalarDomain 2), ‖a‖ ≤ M → ∀ (n : ℤ), N ≤ n.natAbs →
      ∀ z : ℂ, z ∈ sphere ((Real.pi : ℂ)*(n : ℂ)) r →
      δ ≤ ‖(classicalDiscriminant (classicalSobolevPotential a) z)^2-4‖ ∧
      ‖classicalDiscriminant (classicalSobolevPotential a) z/
        ((classicalDiscriminant (classicalSobolevPotential a) z)^2-4)‖ ≤ Q := by
  obtain ⟨N,hN,d,hd,hfactor⟩ := exists_classicalSobolev_contour_factor_lower M hM r hr hrπ
  refine ⟨N,hN,d^2,2*Real.exp (r+4*M)/(d^2),by positivity,by positivity,?_⟩
  intro a ha n hn z hz
  obtain ⟨hminus,hplus⟩ := hfactor a ha n hn z hz
  have hden : d^2 ≤ ‖(classicalDiscriminant (classicalSobolevPotential a) z)^2-4‖ := by
    rw [show (classicalDiscriminant (classicalSobolevPotential a) z)^2-4 =
      (classicalDiscriminant (classicalSobolevPotential a) z-2)*
      (classicalDiscriminant (classicalSobolevPotential a) z+2) by ring,norm_mul,pow_two]
    exact mul_le_mul hminus hplus hd.le (norm_nonneg _)
  have hnum := norm_classicalDiscriminant_le_of_bounds (classicalSobolevPotential a) z (4*M) r
    ((norm_classicalSobolevPotential_le a).trans (by gcongr)) (freeCircle_im_le r n z hz)
  refine ⟨hden,?_⟩
  rw [norm_div]
  exact (div_le_div_of_nonneg_left (norm_nonneg _) (by positivity : 0 < d^2) hden).trans
    (div_le_div_of_nonneg_right hnum (by positivity))

end NLS.ZakharovShabat
