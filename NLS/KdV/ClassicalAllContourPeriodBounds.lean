import NLS.KdV.ClassicalAllContourPeriods
import NLS.KdV.ClassicalUniformPeriodBounds

/-! # Full all-mode bounds for the actual period matrix

The diagonal and every off-diagonal entry, including low modes, have a
single summable convolution majorant on the constructed neighborhood.
-/
noncomputable section
open Set Metric Complex
namespace NLS.KdV

private theorem sq_sqrt_energy (z : ℂ) : (Complex.sqrt z)^2 = z := by
  have h := Complex.cpow_nat_inv_pow z (Nat.succ_ne_zero 1)
  norm_num at h
  simpa only [Complex.sqrt,one_div] using h

namespace ClassicalAllContourPeriodData
variable {N : ℕ} {V : Set (NLS.LinearVolterra.Curve ℂ)} {A : ℝ}
variable (D : ClassicalAllContourPeriodData N V A)
include D

theorem diagonal_separation (n : ℕ+) (q : NLS.LinearVolterra.Curve ℂ) (hq : q ∈ V)
    (z : ℂ) (hz : z ∈ sphere ((Real.pi : ℂ)*(n : ℕ)) (Real.pi/4)) :
    Real.pi^2/8*(n : ℝ) ≤ ‖z^2-classicalHillUniformCriticalPoint N n q‖ := by
  have h := highEnergyContour_diagonal_separation n z
    (Complex.sqrt (classicalHillUniformCriticalPoint N n q)) hz
    (mem_closedBall_iff_norm.mpr (D.critical_close n q hq).le)
  simpa only [sq_sqrt_energy] using h

theorem offDiagonal_separation (n k : ℕ+) (hnk : n ≠ k)
    (q : NLS.LinearVolterra.Curve ℂ) (hq : q ∈ V)
    (z : ℂ) (hz : z ∈ sphere ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4)) :
    Real.pi^2/4*|(k : ℝ)^2-(n : ℝ)^2| ≤ ‖z^2-classicalHillUniformCriticalPoint N n q‖ := by
  have hw : Complex.sqrt (classicalHillUniformCriticalPoint N n q) ∈
      closedBall ((Real.pi : ℂ)*(n : ℕ)) (Real.pi/4) := by
    apply mem_closedBall_iff_norm.mpr
    exact (D.critical_close n q hq).le.trans (by linarith [Real.pi_pos])
  simpa only [sq_sqrt_energy] using highEnergyContour_separation n k hnk z _ hz hw

theorem norm_diagonal_period_le (n : ℕ+) (q : NLS.LinearVolterra.Curve ℂ) (hq : q ∈ V) :
    ‖classicalHillUniformHighPeriod N n n q‖ ≤ (80/Real.pi)*A := by
  have hA := D.amplitude_pos
  let d : ℝ := Real.pi^2/8*(n : ℝ)
  have hd : 0 < d := by dsimp only [d]; positivity
  have hden := D.diagonal_separation n q hq
  have hne (z : ℂ) (hz : z ∈ sphere ((Real.pi : ℂ)*(n : ℕ)) (Real.pi/4)) :
      z^2-classicalHillUniformCriticalPoint N n q ≠ 0 :=
    norm_pos_iff.mp (hd.trans_le (hden z hz))
  rw [classicalHillUniformHighPeriod_eq_primitive N n n q (I*(n : ℂ)*Real.pi)
    (D.numerator_factor n q hq) (D.cover n q hq) hne,norm_mul]
  have hi : ‖∮ z in C((Real.pi : ℂ)*(n : ℕ),Real.pi/4),
      (classicalHillContinuedPrimitive (z^2,q)+I*(n : ℂ)*Real.pi)*(2*z)/
        (z^2-classicalHillUniformCriticalPoint N n q)^2‖ ≤
      2*Real.pi*(Real.pi/4)*(A*((5*Real.pi/2)*(n : ℝ))/d^2) := by
    apply circleIntegral.norm_integral_le_of_norm_le_const (by positivity)
    intro z hz
    have hzc : ‖z-(Real.pi : ℂ)*(n : ℕ)‖ = Real.pi/4 := mem_sphere_iff_norm.mp hz
    have hcn : ‖(Real.pi : ℂ)*(n : ℕ)‖ = Real.pi*(n : ℝ) := by
      simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos,
        Complex.norm_natCast]
    have ht := norm_add_le (z-(Real.pi : ℂ)*(n : ℕ)) ((Real.pi : ℂ)*(n : ℕ))
    rw [sub_add_cancel,hzc,hcn] at ht
    have hn : (1 : ℝ) ≤ n := by exact_mod_cast n.property
    have htwo : ‖(2 : ℂ)*z‖ ≤ (5*Real.pi/2)*(n : ℝ) := by
      rw [norm_mul]
      norm_num only [norm_ofNat]
      nlinarith [Real.pi_pos]
    rw [norm_div,norm_mul,norm_pow]
    gcongr
    · exact D.primitive_bound n q hq z hz
    · exact hden z hz
  have hn : ‖(n : ℂ)‖ = (n : ℝ) := by simp only [Complex.norm_natCast]
  rw [hn]
  calc
    _ ≤ (n : ℝ)*(2*Real.pi*(Real.pi/4)*(A*((5*Real.pi/2)*(n : ℝ))/d^2)) :=
      mul_le_mul_of_nonneg_left hi (by positivity)
    _ = _ := by
      dsimp only [d]
      field_simp
      ring

theorem norm_offDiagonal_period_le (n k : ℕ+) (hnk : n ≠ k)
    (q : NLS.LinearVolterra.Curve ℂ) (hq : q ∈ V) :
    ‖classicalHillUniformHighPeriod N n k q‖ ≤ ((5/Real.pi)*A)/|(k : ℝ)-(n : ℝ)|^2 := by
  have hA := D.amplitude_pos
  have hb := norm_classicalHillUniformHighPeriod_le N n k hnk q (I*(k : ℂ)*Real.pi) A
    D.amplitude_pos.le (D.numerator_factor n q hq) (D.cover k q hq)
    (D.offDiagonal_separation n k hnk q hq) (D.primitive_bound k q hq)
  calc
    _ ≤ ((20/Real.pi)*A)*((n : ℝ)*(k : ℝ)/|(k : ℝ)^2-(n : ℝ)^2|^2) := by
      convert hb using 1
      ring
    _ ≤ ((20/Real.pi)*A)*(1/(4*|(k : ℝ)-(n : ℝ)|^2)) :=
      mul_le_mul_of_nonneg_left (positiveIndex_squared_energy_kernel_le n k hnk) (by positivity)
    _ = _ := by ring

/-- Every matrix entry is bounded on the same neighborhood. The kernel
is one on the diagonal and reciprocal-square off the diagonal. -/
theorem norm_period_le (n k : ℕ+) (q : NLS.LinearVolterra.Curve ℂ) (hq : q ∈ V) :
    ‖classicalHillUniformHighPeriod N n k q‖ ≤
      if n = k then (80/Real.pi)*A else ((80/Real.pi)*A)/|(k : ℝ)-(n : ℝ)|^2 := by
  have hA := D.amplitude_pos
  by_cases hnk : n = k
  · subst n
    rw [if_pos rfl]
    exact D.norm_diagonal_period_le k q hq
  rw [if_neg hnk]
  apply (D.norm_offDiagonal_period_le n k hnk q hq).trans
  gcongr
  norm_num

end ClassicalAllContourPeriodData
end NLS.KdV
