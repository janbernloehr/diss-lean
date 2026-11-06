import NLS.SequenceSpaces.RealActionLifting

/-! The full real coordinate norm is controlled by the action norm, uniformly
at zero and at all closed coordinates. This gives actual coordinate balls
from action balls without choosing a new phase or inverse. -/
noncomputable section
set_option autoImplicit false
open Set Complex
open scoped ENNReal
namespace NLS.Coeff
variable {p q : ℝ≥0∞} [Fact (1≤p)] [Fact (1≤q)] [p.HolderTriple p q]

/-- EVERY real pair, with its original phases, obeys the norm-square bound.
No finite-support or nonzero-coordinate premise is needed. -/
theorem norm_sq_le_two_norm_quadraticActions (hp : p≠⊤)
    (z : Coeff p × Coeff p) (hz : z∈realPairLocus p) :
    ‖z‖^2≤2*‖quadraticActionsExponent (q := q) z‖ := by
  have hnorm (j : ℤ) : ‖quadraticActionsExponent (q := q) z j‖=
      ((z.1 j).re^2+(z.2 j).re^2)/2 := by
    have he : quadraticActionsExponent (q := q) z j=
        (((z.1 j).re^2+(z.2 j).re^2)/2 : ℝ) := by
      rw [quadraticActionsExponent_apply]
      apply Complex.ext <;> simp [pow_two,mul_re,mul_im,hz.1 j,hz.2 j]
    rw [he,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  let e : Coeff q := (2 : ℂ) • quadraticActionsExponent z
  have he (j : ℤ) : ‖e j‖=2*‖quadraticActionsExponent (q := q) z j‖ := by
    simp only [e,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,norm_mul,Complex.norm_ofNat]
  have hx : ‖z.1‖^2≤2*‖quadraticActionsExponent (q := q) z‖ := by
    have hb := norm_sq_le_of_norm_sq_le hp z.1 e (fun j => by
      rw [he j,hnorm j,Complex.sq_norm,Complex.normSq_apply,hz.1 j]
      nlinarith [sq_nonneg (z.2 j).re])
    simpa only [e,norm_smul,Complex.norm_ofNat] using hb
  have hy : ‖z.2‖^2≤2*‖quadraticActionsExponent (q := q) z‖ := by
    have hb := norm_sq_le_of_norm_sq_le hp z.2 e (fun j => by
      rw [he j,hnorm j,Complex.sq_norm,Complex.normSq_apply,hz.2 j]
      nlinarith [sq_nonneg (z.1 j).re])
    simpa only [e,norm_smul,Complex.norm_ofNat] using hb
  rw [Prod.norm_def]
  rcases le_total ‖z.1‖ ‖z.2‖ with hh | hh
  · simpa only [max_eq_right hh] using hy
  · simpa only [max_eq_left hh] using hx

end NLS.Coeff
