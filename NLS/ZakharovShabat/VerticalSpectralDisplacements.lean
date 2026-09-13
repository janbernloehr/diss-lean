import NLS.ZakharovShabat.RelativeSpectralProducts
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Summable relative displacements on vertical spectral lines

At fixed real part, increasing the absolute imaginary part increases every
free denominator. A single off-lattice resolvent supplies a summable majorant,
so the total absolute relative displacement tends to zero at vertical infinity.
-/

noncomputable section
open Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- A spectral point on the vertical line with real part `x`. -/
def verticalSpectralPoint (x y : ℝ) : ℂ := (x : ℂ)+(y : ℂ)*I

@[simp] theorem verticalSpectralPoint_re (x y : ℝ) : (verticalSpectralPoint x y).re = x := by
  simp [verticalSpectralPoint]

@[simp] theorem verticalSpectralPoint_im (x y : ℝ) : (verticalSpectralPoint x y).im = y := by
  simp [verticalSpectralPoint]

/-- Every nonreal vertical point avoids the free spectral lattice. -/
theorem verticalSpectralPoint_notMem_freeLattice (x y : ℝ) (hy : y ≠ 0) :
    verticalSpectralPoint x y ∉ freeLattice := notMem_freeLattice_of_im_ne_zero (by simpa using hy)

/-- The squared free denominator separates the real offset and imaginary height. -/
theorem norm_vertical_free_denominator_sq (x y : ℝ) (n : ℤ) :
    ‖verticalSpectralPoint x y-(Real.pi : ℂ)*n‖^2 = (x-Real.pi*n)^2+y^2 := by
  rw [Complex.sq_norm,Complex.normSq_apply]
  simp [verticalSpectralPoint,pow_two]

/-- Outside the horizontal strip of height one, each denominator dominates its height-one value. -/
theorem norm_vertical_free_denominator_le (x y : ℝ) (hy : 1 ≤ |y|) (n : ℤ) :
    ‖verticalSpectralPoint x 1-(Real.pi : ℂ)*n‖ ≤ ‖verticalSpectralPoint x y-(Real.pi : ℂ)*n‖ := by
  have h₁ := norm_vertical_free_denominator_sq x 1 n
  have h₂ := norm_vertical_free_denominator_sq x y n
  have hab := sq_abs y
  have hn := norm_nonneg (verticalSpectralPoint x y-(Real.pi : ℂ)*n)
  nlinarith

/-- The relative displacement is bounded by one fixed summable sequence on both ends of a vertical line. -/
theorem norm_vertical_relativeDisplacement_le (ξ : ℤ → ℂ) (x y : ℝ) (hy : 1 ≤ |y|) (n : ℤ) :
    ‖(ξ n-(Real.pi : ℂ)*n)/(verticalSpectralPoint x y-(Real.pi : ℂ)*n)‖ ≤
      ‖(ξ n-(Real.pi : ℂ)*n)/(verticalSpectralPoint x 1-(Real.pi : ℂ)*n)‖ := by
  rw [norm_div,norm_div]
  apply div_le_div_of_nonneg_left (norm_nonneg _)
    (norm_pos_iff.mpr (free_denominator_ne_zero (verticalSpectralPoint_notMem_freeLattice x 1 one_ne_zero) n))
    (norm_vertical_free_denominator_le x y hy n)

/-- A fixed relative displacement tends to zero whenever the absolute imaginary height tends to infinity. -/
theorem tendsto_norm_vertical_relativeDisplacement {α : Type*} {l : Filter α} {y : α → ℝ}
    (hy : Tendsto (fun a => |y a|) l atTop) (ξ : ℤ → ℂ) (x : ℝ) (n : ℤ) :
    Tendsto (fun a => ‖(ξ n-(Real.pi : ℂ)*n)/(verticalSpectralPoint x (y a)-(Real.pi : ℂ)*n)‖) l (𝓝 0) := by
  have hden : Tendsto (fun a => ‖verticalSpectralPoint x (y a)-(Real.pi : ℂ)*n‖) l atTop := by
    apply tendsto_atTop_mono _ hy
    intro a
    simpa using Complex.abs_im_le_norm (verticalSpectralPoint x (y a)-(Real.pi : ℂ)*n)
  simpa only [norm_div] using hden.const_div_atTop ‖ξ n-(Real.pi : ℂ)*n‖

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- At every finite Banach exponent, the total absolute relative displacement vanishes along both vertical ends. -/
theorem tendsto_tsum_norm_vertical_relativeDisplacement {α : Type*} {l : Filter α} {y : α → ℝ}
    (hy : Tendsto (fun a => |y a|) l atTop) (hp : p ≠ ⊤) (ξ : ℤ → ℂ)
    (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p) (x : ℝ) :
    Tendsto (fun a => ∑' n : ℤ, ‖(ξ n-(Real.pi : ℂ)*n)/(verticalSpectralPoint x (y a)-(Real.pi : ℂ)*n)‖)
      l (𝓝 0) := by
  have hsum := summable_norm_spectralRelativeDisplacement hp ξ hξ (verticalSpectralPoint x 1)
    (verticalSpectralPoint_notMem_freeLattice x 1 one_ne_zero)
  have h := tendsto_tsum_of_dominated_convergence hsum
    (fun n => tendsto_norm_vertical_relativeDisplacement hy ξ x n) (by
      filter_upwards [hy.eventually (eventually_ge_atTop (1 : ℝ))] with a ha n
      simpa only [norm_norm] using norm_vertical_relativeDisplacement_le ξ x (y a) ha n)
  simpa only [tsum_zero] using h

end NLS.ZakharovShabat
