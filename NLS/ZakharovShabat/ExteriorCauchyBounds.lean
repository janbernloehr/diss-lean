import NLS.ZakharovShabat.EntireFreeDiscBounds
import Mathlib.Analysis.Complex.Liouville

/-!
# Cauchy estimates on the free-disc exterior

A circle of half the separation radius stays outside the smaller free discs.
Its imaginary height differs by at most that half radius, allowing an
exponential value bound to control the derivative at its center.
-/

noncomputable section
open Set Complex Metric
namespace NLS.ZakharovShabat

/-- A half-radius circle preserves half of the center's free-lattice separation. -/
theorem sphere_half_separated {r : ℝ} {z w : ℂ}
    (hsep : ∀ n : ℤ, r ≤ ‖z-(Real.pi : ℂ)*n‖) (hw : w ∈ sphere z (r/2)) (n : ℤ) :
    r/2 ≤ ‖w-(Real.pi : ℂ)*n‖ := by
  have hd : ‖z-w‖ = r/2 := by simpa only [mem_sphere, dist_eq_norm, norm_sub_rev] using hw
  have ht : ‖z-(Real.pi : ℂ)*n‖ ≤ ‖z-w‖+‖w-(Real.pi : ℂ)*n‖ := by
    calc
      _ = ‖(z-w)+(w-(Real.pi : ℂ)*n)‖ := by congr 1; abel
      _ ≤ _ := norm_add_le _ _
  rw [hd] at ht
  linarith [hsep n]

/-- Imaginary height changes by at most the complex distance. -/
theorem abs_im_le_abs_im_add_norm_sub (w z : ℂ) : |w.im| ≤ |z.im|+‖w-z‖ := by
  calc
    |w.im| = |(w-z).im+z.im| := by simp
    _ ≤ |(w-z).im|+|z.im| := abs_add_le _ _
    _ ≤ ‖w-z‖+|z.im| := add_le_add (abs_im_le_norm _) le_rfl
    _ = _ := add_comm _ _

/-- An exponential exterior value bound gives a derivative bound on the smaller circle. -/
theorem norm_deriv_le_of_exterior_exp_bound {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {r : ℝ} (hr : 0 < r) (R ε : ℝ) (hε : 0 ≤ ε)
    (hb : ∀ w : ℂ, R ≤ ‖w‖ → (∀ n : ℤ, r/2 ≤ ‖w-(Real.pi : ℂ)*n‖) →
      ‖f w‖ ≤ ε*Real.exp |w.im|)
    (z : ℂ) (hR : R+r/2 ≤ ‖z‖) (hsep : ∀ n : ℤ, r ≤ ‖z-(Real.pi : ℂ)*n‖) :
    ‖deriv f z‖ ≤ (ε*Real.exp (|z.im|+r/2))/(r/2) := by
  apply Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (half_pos hr) hf.diffContOnCl
  intro w hw
  have hd : ‖w-z‖ = r/2 := by simpa only [mem_sphere, dist_eq_norm] using hw
  have ht : ‖z‖ ≤ ‖z-w‖+‖w‖ := by
    calc
      ‖z‖ = ‖(z-w)+w‖ := by rw [sub_add_cancel]
      _ ≤ _ := norm_add_le _ _
  rw [norm_sub_rev z w, hd] at ht
  have hwR : R ≤ ‖w‖ := by linarith
  have hi : |w.im| ≤ |z.im|+r/2 := by
    simpa only [hd] using abs_im_le_abs_im_add_norm_sub w z
  exact (hb w hwR (sphere_half_separated hsep hw)).trans
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hi) hε)

end NLS.ZakharovShabat
