import NLS.ZakharovShabat.SpectralProductsExteriorLimit

/-!
# Quantitative full and parity relative-product errors

Small absolute displacement sums control the paired product. An affine parity
rescaling selects a subsum of the original nonnegative series, so the same
bound controls the full, even, and odd normalizations simultaneously.
-/

noncomputable section
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Two absolute displacement sums bounded by δ give paired product error at most exp(2δ)-1. -/
theorem norm_spectralRelativePairProduct_sub_one_le_of_sums (hp : p ≠ ⊤) (ξ η : ℤ → ℂ)
    (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p)
    (hη : Memℓp (fun n => η n-(Real.pi : ℂ)*n) p) (z : ℂ) (hz : z ∉ freeLattice)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hbξ : (∑' n : ℤ, ‖(ξ n-(Real.pi : ℂ)*n)/(z-(Real.pi : ℂ)*n)‖) ≤ δ)
    (hbη : (∑' n : ℤ, ‖(η n-(Real.pi : ℂ)*n)/(z-(Real.pi : ℂ)*n)‖) ≤ δ) :
    ‖spectralRelativePairProduct ξ η z-1‖ ≤ Real.exp (2*δ)-1 := by
  let F := ∏' n, spectralRelativeFactor ξ z n
  let G := ∏' n, spectralRelativeFactor η z n
  have hF : ‖F-1‖ ≤ Real.exp δ-1 := (norm_spectralRelativeProduct_sub_one_le hp ξ hξ z hz).trans
    (sub_le_sub_right (Real.exp_le_exp.mpr hbξ) 1)
  have hG : ‖G-1‖ ≤ Real.exp δ-1 := (norm_spectralRelativeProduct_sub_one_le hp η hη z hz).trans
    (sub_le_sub_right (Real.exp_le_exp.mpr hbη) 1)
  have hGn : ‖G‖ ≤ Real.exp δ := by
    have h := norm_le_norm_sub_add G 1
    norm_num at h
    linarith
  have he : spectralRelativePairProduct ξ η z = F*G :=
    (multipliable_spectralRelativeFactor hp ξ hξ z hz).tprod_mul (multipliable_spectralRelativeFactor hp η hη z hz)
  rw [he, show F*G-1 = (F-1)*G+(G-1) by ring]
  calc
    _ ≤ ‖F-1‖*‖G‖+‖G-1‖ := by simpa only [norm_mul] using norm_add_le ((F-1)*G) (G-1)
    _ ≤ (Real.exp δ-1)*Real.exp δ+(Real.exp δ-1) :=
      add_le_add (mul_le_mul hF hGn (norm_nonneg _) (by linarith [Real.one_le_exp_iff.mpr hδ])) hG
    _ = Real.exp (2*δ)-1 := by rw [two_mul, Real.exp_add]; ring

/-- The absolute parity-rescaled displacement sum is bounded by the full original sum. -/
theorem tsum_norm_parity_relativeDisplacement_le (hp : p ≠ ⊤) (ξ : ℤ → ℂ)
    (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p) (z : ℂ) (hz : z ∉ freeLattice) (k : ℤ) :
    (∑' n : ℤ, ‖(parityRescale ξ k n-(Real.pi : ℂ)*n)/((z-(Real.pi : ℂ)*k)/2-(Real.pi : ℂ)*n)‖) ≤
      ∑' n : ℤ, ‖(ξ n-(Real.pi : ℂ)*n)/(z-(Real.pi : ℂ)*n)‖ := by
  have he (n : ℤ) :
      (parityRescale ξ k n-(Real.pi : ℂ)*n)/((z-(Real.pi : ℂ)*k)/2-(Real.pi : ℂ)*n) =
      (ξ (2*n+k)-(Real.pi : ℂ)*(2*n+k : ℤ))/(z-(Real.pi : ℂ)*(2*n+k : ℤ)) := by
    have hn : parityRescale ξ k n-(Real.pi : ℂ)*n = (ξ (2*n+k)-(Real.pi : ℂ)*(2*n+k : ℤ))/2 := by
      unfold parityRescale; push_cast; ring
    have hd : (z-(Real.pi : ℂ)*k)/2-(Real.pi : ℂ)*n = (z-(Real.pi : ℂ)*(2*n+k : ℤ))/2 := by
      push_cast; ring
    rw [hn, hd, div_div_div_cancel_right₀ (by norm_num : (2 : ℂ) ≠ 0)]
  simp only [he]
  exact tsum_comp_le_tsum_of_inj (summable_norm_spectralRelativeDisplacement hp ξ hξ z hz)
    (fun _ => norm_nonneg _) (fun a b h => by omega)

/-- The same displacement bound controls all three correctly normalized products. -/
theorem norm_spectralProducts_div_free_sub_one_le (hp : p ≠ ⊤) (ξ η : ℤ → ℂ)
    (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p)
    (hη : Memℓp (fun n => η n-(Real.pi : ℂ)*n) p) (z : ℂ)
    {r : ℝ} (hr : 0 < r) (hsep : ∀ n : ℤ, r ≤ ‖z-(Real.pi : ℂ)*n‖)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hbξ : (∑' n : ℤ, ‖(ξ n-(Real.pi : ℂ)*n)/(z-(Real.pi : ℂ)*n)‖) ≤ δ)
    (hbη : (∑' n : ℤ, ‖(η n-(Real.pi : ℂ)*n)/(z-(Real.pi : ℂ)*n)‖) ≤ δ) :
    ‖entireSpectralPairProduct ξ η z/((freeDiscriminant z)^2-4)-1‖ ≤ Real.exp (2*δ)-1 ∧
    ‖evenSpectralPairProduct ξ η z/(freeDiscriminant z-2)-1‖ ≤ Real.exp (2*δ)-1 ∧
    ‖oddSpectralPairProduct ξ η z/(freeDiscriminant z+2)-1‖ ≤ Real.exp (2*δ)-1 := by
  have hz := notMem_freeLattice_of_separated hr hsep
  have hpar (k : ℤ) := norm_spectralRelativePairProduct_sub_one_le_of_sums hp
    (parityRescale ξ k) (parityRescale η k) (memℓp_parityRescale hp ξ hξ k) (memℓp_parityRescale hp η hη k)
    ((z-(Real.pi : ℂ)*k)/2)
    (notMem_freeLattice_of_separated (half_pos hr) (separated_parity_rescale z hsep k)) hδ
    ((tsum_norm_parity_relativeDisplacement_le hp ξ hξ z hz k).trans hbξ)
    ((tsum_norm_parity_relativeDisplacement_le hp η hη z hz k).trans hbη)
  have he (k : ℤ) := entireSpectralPairProduct_div_free hp (parityRescale ξ k) (parityRescale η k)
    (memℓp_parityRescale hp ξ hξ k) (memℓp_parityRescale hp η hη k) ((z-(Real.pi : ℂ)*k)/2)
    (notMem_freeLattice_of_separated (half_pos hr) (separated_parity_rescale z hsep k))
  refine ⟨?_, ?_, ?_⟩
  · rw [entireSpectralPairProduct_div_free hp ξ η hξ hη z hz]
    exact norm_spectralRelativePairProduct_sub_one_le_of_sums hp ξ η hξ hη z hz hδ hbξ hbη
  · have h := hpar 0
    rw [← he 0] at h
    simpa only [Int.cast_zero, mul_zero, sub_zero, freeDiscriminant_half_sq_sub_four, evenSpectralPairProduct] using h
  · have h := hpar 1
    rw [← he 1] at h
    simpa only [Int.cast_one, mul_one, freeDiscriminant_odd_half_sq_sub_four, oddSpectralPairProduct,
      div_neg, neg_div] using h

end NLS.ZakharovShabat
