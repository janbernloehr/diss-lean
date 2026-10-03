import NLS.ZakharovShabat.SourceCanonicalRootExterior
import Mathlib.Analysis.SpecialFunctions.Exp

/-! # Upper vertical normalization of the canonical root

The exterior product normalization fixes the sign of the root along the
upper imaginary ray. This holds at every finite exponent greater than one.
-/
noncomputable section
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Exact free-root normalization along the upper imaginary ray. -/
theorem exp_neg_mul_freeRoot_vertical (y : ℝ) :
    exp (-(y : ℂ)) * (-2*I*sin ((y : ℂ)*I)) = 1 - exp (-(2*y : ℂ)) := by
  rw [sin_mul_I]
  have he : -2*I*(sinh (y : ℂ)*I) = 2*sinh (y : ℂ) := by
    calc
      _ = -2*sinh (y : ℂ)*(I*I) := by ring
      _ = _ := by rw [I_mul_I]; ring
  rw [he, two_sinh, mul_sub, ← exp_add, neg_add_cancel, exp_zero, ← exp_add]
  congr 2
  ring

/-- The actual canonical root has the positive free normalization at the
upper vertical end; the proof fixes its sign using the exterior product. -/
theorem tendsto_sourceCanonicalRoot_upper_normalized (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) :
    Tendsto (fun y : ℝ => exp (-(y : ℂ))*sourceCanonicalRoot hp hp1 φ ((y : ℂ)*I))
      atTop (𝓝 1) := by
  let r : ℝ := Real.pi/4
  have hr : 0 < r := by dsimp [r]; positivity
  let z := fun y : ℝ => ((max y r : ℝ) : ℂ)*I
  have him (y : ℝ) : (z y).im = max y r := by simp [z]
  have hnorm : Tendsto (fun y => ‖z y‖) atTop atTop := by
    apply tendsto_atTop_mono _ tendsto_id
    intro y
    exact (le_max_left y r).trans ((le_abs_self _).trans (by simpa only [him] using abs_im_le_norm (z y)))
  have hsep (y : ℝ) (m : ℤ) : r ≤ ‖z y - (Real.pi : ℂ)*m‖ := by
    have h := abs_im_le_norm (z y - (Real.pi : ℂ)*m)
    simp only [sub_im, mul_im, ofReal_re, ofReal_im, intCast_re, intCast_im, mul_zero,
      zero_mul, add_zero, sub_zero, him] at h
    exact (le_max_right y r).trans ((le_abs_self _).trans h)
  have hratio := tendsto_sourceCanonicalRoot_div_free_of_separated hp hp1 φ z hnorm hr le_rfl hsep
  have he : Tendsto (fun y : ℝ => exp (-(2*y : ℂ))) atTop (𝓝 0) := by
    apply Complex.tendsto_exp_nhds_zero_iff.mpr
    simpa [Function.comp_def] using
      tendsto_neg_atTop_atBot.comp (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
  have hfree : Tendsto (fun y : ℝ => exp (-(y : ℂ)) * (-2*I*sin ((y : ℂ)*I))) atTop (𝓝 1) := by
    simpa only [exp_neg_mul_freeRoot_vertical, sub_zero] using he.const_sub 1
  have hrat : Tendsto (fun y : ℝ => sourceCanonicalRoot hp hp1 φ ((y : ℂ)*I) /
      (-2*I*sin ((y : ℂ)*I))) atTop (𝓝 1) := by
    apply hratio.congr'
    filter_upwards [eventually_ge_atTop r] with y hy
    simp only [z, max_eq_left hy]
  have h := hfree.mul hrat
  simp only [mul_one] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop r] with y hy
  have hs : sin ((y : ℂ)*I) ≠ 0 := by
    have ht := sin_ne_zero_of_notMem_freeLattice
      (notMem_freeLattice_of_separated hr (hsep y))
    simpa only [z, max_eq_left hy] using ht
  field_simp

end NLS.ZakharovShabat
