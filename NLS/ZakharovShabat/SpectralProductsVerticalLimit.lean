import NLS.ZakharovShabat.RelativeProductsVerticalLimit
import NLS.ZakharovShabat.ParitySpectralProducts
import Mathlib.Tactic.LinearCombination

/-!
# Vertical normalization of the entire spectral products

The full paired product divided by its free characteristic function tends to
one at vertical infinity. Rescaling gives the same exact normalization for
the even and odd products, with the corrected source prefactors retained.
-/

noncomputable section
open Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Off the free lattice, division by the free characteristic function is the relative pair product. -/
theorem entireSpectralPairProduct_div_free (hp : p ≠ ⊤) (ξ η : ℤ → ℂ)
    (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p)
    (hη : Memℓp (fun n => η n-(Real.pi : ℂ)*n) p) (z : ℂ) (hz : z ∉ freeLattice) :
    entireSpectralPairProduct ξ η z/((freeDiscriminant z)^2-4) = spectralRelativePairProduct ξ η z := by
  rw [entireSpectralPairProduct_eq_offLattice hp ξ η hξ hη z hz]
  change (((freeDiscriminant z)^2-4)*spectralRelativePairProduct ξ η z)/((freeDiscriminant z)^2-4) = _
  exact mul_div_cancel_left₀ _ (freeDiscriminant_sq_sub_four_ne_zero z hz)

/-- The correctly normalized full paired product is asymptotic to its free characteristic function vertically. -/
theorem tendsto_entireSpectralPairProduct_div_free_vertical {α : Type*} {l : Filter α} {y : α → ℝ}
    (hy : Tendsto (fun a => |y a|) l atTop) (hp : p ≠ ⊤) (ξ η : ℤ → ℂ)
    (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p)
    (hη : Memℓp (fun n => η n-(Real.pi : ℂ)*n) p) (x : ℝ) :
    Tendsto (fun a => entireSpectralPairProduct ξ η (verticalSpectralPoint x (y a))/
      ((freeDiscriminant (verticalSpectralPoint x (y a)))^2-4)) l (𝓝 1) := by
  apply (tendsto_spectralRelativePairProduct_vertical hy hp ξ η hξ hη x).congr'
  filter_upwards [eventually_verticalSpectralPoint_notMem_freeLattice hy x] with a ha
  exact (entireSpectralPairProduct_div_free hp ξ η hξ hη _ ha).symm

/-- The free characteristic function at half the parameter is the even free factor. -/
theorem freeDiscriminant_half_sq_sub_four (z : ℂ) :
    (freeDiscriminant (z/2))^2-4 = freeDiscriminant z-2 := by
  have h : cos z = 2*(cos (z/2))^2-1 := by
    have he : 2*(z/2) = z := by ring
    simpa only [he] using Complex.cos_two_mul (z/2)
  unfold freeDiscriminant
  linear_combination -2*h

/-- Translating and halving gives the negative odd free factor. -/
theorem freeDiscriminant_odd_half_sq_sub_four (z : ℂ) :
    (freeDiscriminant ((z-(Real.pi : ℂ))/2))^2-4 = -(freeDiscriminant z+2) := by
  rw [freeDiscriminant_half_sq_sub_four]
  simp [freeDiscriminant,Complex.cos_sub]
  ring

/-- Affine parity rescaling preserves vertical lines and halves the imaginary height. -/
theorem verticalSpectralPoint_parity_rescale (x y : ℝ) (r : ℤ) :
    (verticalSpectralPoint x y-(Real.pi : ℂ)*r)/2 = verticalSpectralPoint ((x-Real.pi*r)/2) (y/2) := by
  simp only [verticalSpectralPoint]
  push_cast
  ring

/-- Halving a diverging absolute imaginary height preserves divergence. -/
theorem tendsto_abs_half_atTop {α : Type*} {l : Filter α} {y : α → ℝ}
    (hy : Tendsto (fun a => |y a|) l atTop) : Tendsto (fun a => |y a/2|) l atTop := by
  simpa only [abs_div,abs_of_pos (by norm_num : (0 : ℝ) < 2)] using hy.atTop_div_const (by norm_num : (0 : ℝ) < 2)

/-- The even spectral product has its free shifted-trace normalization on both vertical ends. -/
theorem tendsto_evenSpectralPairProduct_div_free_vertical {α : Type*} {l : Filter α} {y : α → ℝ}
    (hy : Tendsto (fun a => |y a|) l atTop) (hp : p ≠ ⊤) (ξ η : ℤ → ℂ)
    (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p)
    (hη : Memℓp (fun n => η n-(Real.pi : ℂ)*n) p) (x : ℝ) :
    Tendsto (fun a => evenSpectralPairProduct ξ η (verticalSpectralPoint x (y a))/
      (freeDiscriminant (verticalSpectralPoint x (y a))-2)) l (𝓝 1) := by
  have h := tendsto_entireSpectralPairProduct_div_free_vertical (tendsto_abs_half_atTop hy) hp
    (parityRescale ξ 0) (parityRescale η 0) (memℓp_parityRescale hp ξ hξ 0) (memℓp_parityRescale hp η hη 0) (x/2)
  have he (a : α) : verticalSpectralPoint (x/2) (y a/2) = verticalSpectralPoint x (y a)/2 := by
    simpa using (verticalSpectralPoint_parity_rescale x (y a) 0).symm
  simpa only [he,freeDiscriminant_half_sq_sub_four,evenSpectralPairProduct] using h

/-- The odd spectral product retains the positive free shifted-trace normalization on both vertical ends. -/
theorem tendsto_oddSpectralPairProduct_div_free_vertical {α : Type*} {l : Filter α} {y : α → ℝ}
    (hy : Tendsto (fun a => |y a|) l atTop) (hp : p ≠ ⊤) (ξ η : ℤ → ℂ)
    (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p)
    (hη : Memℓp (fun n => η n-(Real.pi : ℂ)*n) p) (x : ℝ) :
    Tendsto (fun a => oddSpectralPairProduct ξ η (verticalSpectralPoint x (y a))/
      (freeDiscriminant (verticalSpectralPoint x (y a))+2)) l (𝓝 1) := by
  have h := tendsto_entireSpectralPairProduct_div_free_vertical (tendsto_abs_half_atTop hy) hp
    (parityRescale ξ 1) (parityRescale η 1) (memℓp_parityRescale hp ξ hξ 1) (memℓp_parityRescale hp η hη 1) ((x-Real.pi)/2)
  have he (a : α) : verticalSpectralPoint ((x-Real.pi)/2) (y a/2) =
      (verticalSpectralPoint x (y a)-(Real.pi : ℂ))/2 := by
    simpa using (verticalSpectralPoint_parity_rescale x (y a) 1).symm
  simpa only [he,freeDiscriminant_odd_half_sq_sub_four,oddSpectralPairProduct,div_neg,neg_div] using h

end NLS.ZakharovShabat
