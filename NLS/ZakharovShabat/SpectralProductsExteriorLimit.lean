import NLS.ZakharovShabat.RelativeProductsExteriorLimit
import NLS.ZakharovShabat.SpectralProductsVerticalLimit

/-!
# Full and parity product normalizations outside free spectral discs

Affine parity rescaling halves the omitted-disc radius and preserves escape
to infinity. The corrected even and odd free factors retain their signs.
-/

noncomputable section
open Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem tendsto_entireSpectralPairProduct_div_free_of_separated {α : Type*} {l : Filter α}
    (hp : p ≠ ⊤) (ξ η : ℤ → ℂ)
    (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p)
    (hη : Memℓp (fun n => η n-(Real.pi : ℂ)*n) p)
    (z : α → ℂ) (hescape : Tendsto (fun i => ‖z i‖) l atTop)
    {r : ℝ} (hr : 0 < r) (hrπ : r ≤ Real.pi/4)
    (hsep : ∀ i (n : ℤ), r ≤ ‖z i-(Real.pi : ℂ)*n‖) :
    Tendsto (fun i => entireSpectralPairProduct ξ η (z i)/((freeDiscriminant (z i))^2-4))
      l (𝓝 1) := by
  apply (tendsto_spectralRelativePairProduct_of_separated hp ξ η hξ hη z hescape hr hrπ hsep).congr
  intro i
  exact (entireSpectralPairProduct_div_free hp ξ η hξ hη (z i)
    (notMem_freeLattice_of_separated hr (hsep i))).symm

theorem norm_parity_rescale_denominator (z : ℂ) (k n : ℤ) :
    ‖(z-(Real.pi : ℂ)*k)/2-(Real.pi : ℂ)*n‖ =
      ‖z-(Real.pi : ℂ)*(2*n+k : ℤ)‖/2 := by
  have he : (z-(Real.pi : ℂ)*k)/2-(Real.pi : ℂ)*n =
      (z-(Real.pi : ℂ)*(2*n+k : ℤ))/2 := by push_cast; ring
  rw [he, norm_div]
  norm_num

theorem separated_parity_rescale {r : ℝ} (z : ℂ)
    (hz : ∀ n : ℤ, r ≤ ‖z-(Real.pi : ℂ)*n‖) (k n : ℤ) :
    r/2 ≤ ‖(z-(Real.pi : ℂ)*k)/2-(Real.pi : ℂ)*n‖ := by
  rw [norm_parity_rescale_denominator]
  exact div_le_div_of_nonneg_right (hz (2*n+k)) (by norm_num)

theorem tendsto_norm_parity_rescale_atTop {α : Type*} {l : Filter α}
    (z : α → ℂ) (hz : Tendsto (fun i => ‖z i‖) l atTop) (k : ℤ) :
    Tendsto (fun i => ‖(z i-(Real.pi : ℂ)*k)/2‖) l atTop := by
  have h := (tendsto_norm_free_denominator_atTop z hz k).atTop_div_const (by norm_num : (0 : ℝ) < 2)
  simpa only [norm_div, Complex.norm_ofNat] using h

theorem tendsto_evenSpectralPairProduct_div_free_of_separated {α : Type*} {l : Filter α}
    (hp : p ≠ ⊤) (ξ η : ℤ → ℂ)
    (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p)
    (hη : Memℓp (fun n => η n-(Real.pi : ℂ)*n) p)
    (z : α → ℂ) (hescape : Tendsto (fun i => ‖z i‖) l atTop)
    {r : ℝ} (hr : 0 < r) (hrπ : r ≤ Real.pi/4)
    (hsep : ∀ i (n : ℤ), r ≤ ‖z i-(Real.pi : ℂ)*n‖) :
    Tendsto (fun i => evenSpectralPairProduct ξ η (z i)/(freeDiscriminant (z i)-2))
      l (𝓝 1) := by
  have h := tendsto_entireSpectralPairProduct_div_free_of_separated hp
    (parityRescale ξ 0) (parityRescale η 0)
    (memℓp_parityRescale hp ξ hξ 0) (memℓp_parityRescale hp η hη 0)
    (fun i => (z i-(Real.pi : ℂ)*(0 : ℤ))/2) (tendsto_norm_parity_rescale_atTop z hescape 0)
    (div_pos hr (by norm_num)) (by linarith)
    (fun i n => separated_parity_rescale (z i) (hsep i) 0 n)
  simpa only [Int.cast_zero, mul_zero, sub_zero, freeDiscriminant_half_sq_sub_four,
    evenSpectralPairProduct] using h

theorem tendsto_oddSpectralPairProduct_div_free_of_separated {α : Type*} {l : Filter α}
    (hp : p ≠ ⊤) (ξ η : ℤ → ℂ)
    (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p)
    (hη : Memℓp (fun n => η n-(Real.pi : ℂ)*n) p)
    (z : α → ℂ) (hescape : Tendsto (fun i => ‖z i‖) l atTop)
    {r : ℝ} (hr : 0 < r) (hrπ : r ≤ Real.pi/4)
    (hsep : ∀ i (n : ℤ), r ≤ ‖z i-(Real.pi : ℂ)*n‖) :
    Tendsto (fun i => oddSpectralPairProduct ξ η (z i)/(freeDiscriminant (z i)+2))
      l (𝓝 1) := by
  have h := tendsto_entireSpectralPairProduct_div_free_of_separated hp
    (parityRescale ξ 1) (parityRescale η 1)
    (memℓp_parityRescale hp ξ hξ 1) (memℓp_parityRescale hp η hη 1)
    (fun i => (z i-(Real.pi : ℂ)*(1 : ℤ))/2) (tendsto_norm_parity_rescale_atTop z hescape 1)
    (div_pos hr (by norm_num)) (by linarith)
    (fun i n => separated_parity_rescale (z i) (hsep i) 1 n)
  simpa only [Int.cast_one, mul_one, freeDiscriminant_odd_half_sq_sub_four,
    oddSpectralPairProduct, div_neg, neg_div] using h

end NLS.ZakharovShabat
