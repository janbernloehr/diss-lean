import NLS.KdV.HillHminusOneUniformPrimitiveBounds
import NLS.ComplexAnalysis.CriticalBasisPeriodBounds
import NLS.KdV.ClassicalUniformPeriodBounds
import NLS.KdV.PositiveEnergyResolventKernel

/-! # Full actual rough Hill period matrix bounds -/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
namespace NLS.KdV
namespace HillHminusUniformPeriodData
variable {C : HillHminusMiuraChart} {N : ℕ} {V : Set PeriodOneHminusOne} {A : ℝ}
variable (D : HillHminusUniformPeriodData C N V A)
include D

theorem mono {U : Set PeriodOneHminusOne} (hUV : U ⊆ V) (hU : IsOpen U) (h0U : 0 ∈ U) :
    HillHminusUniformPeriodData C N U A :=
  ⟨D.toHillHminusAllContourPeriodData.mono hUV hU h0U,D.amplitude_pos,
    fun n q hq => D.critical_close n q (hUV hq),fun k q hq z hz => D.primitive_bound k q (hUV hq) z hz⟩

theorem diagonal_separation (n : ℕ+) (q : PeriodOneHminusOne) (hq : q ∈ V)
    (z : ℂ) (hz : z ∈ sphere ((Real.pi : ℂ)*(n : ℕ)) (Real.pi/4)) :
    Real.pi^2/8*(n : ℝ) ≤ ‖z^2-hillHminusUniformCriticalPoint C N n q‖ := by
  have h := highEnergyContour_diagonal_separation n z
    (sqrt (hillHminusUniformCriticalPoint C N n q)) hz
    (mem_closedBall_iff_norm.mpr (D.critical_close n q hq).le)
  simpa only [complex_sqrt_sq] using h

theorem offDiagonal_separation (n k : ℕ+) (hnk : n ≠ k) (q : PeriodOneHminusOne) (hq : q ∈ V)
    (z : ℂ) (hz : z ∈ sphere ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4)) :
    Real.pi^2/4*|(k : ℝ)^2-(n : ℝ)^2| ≤ ‖z^2-hillHminusUniformCriticalPoint C N n q‖ := by
  have hw : sqrt (hillHminusUniformCriticalPoint C N n q) ∈
      closedBall ((Real.pi : ℂ)*(n : ℕ)) (Real.pi/4) :=
    mem_closedBall_iff_norm.mpr ((D.critical_close n q hq).le.trans (by linarith [Real.pi_pos]))
  simpa only [complex_sqrt_sq] using highEnergyContour_separation n k hnk z _ hz hw

theorem period_eq_primitive (n k : ℕ+) (q : PeriodOneHminusOne) (hq : q ∈ V) (shift : ℂ)
    (hne : ∀ z ∈ sphere ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4),
      z^2-hillHminusUniformCriticalPoint C N n q ≠ 0) :
    hillHminusPeriodEntry C N n k q = (n : ℂ) *
      ∮ z in C((Real.pi : ℂ)*(k : ℕ),Real.pi/4),
        (hillHminusContinuedPrimitive (z^2,q)+shift)*(2*z)/(z^2-hillHminusUniformCriticalPoint C N n q)^2 := by
  let H : ℂ → ℂ := fun z => hillHminusContinuedPrimitive (z^2,q)+shift
  have hH : AnalyticOnNhd ℂ H (sphere ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4)) := by
    intro z hz
    exact ((analyticOnNhd_hillHminusContinuedPrimitive (z^2,q) (D.cover k q hq z hz)).comp
      (f := fun w : ℂ => (w^2,q)) ((analyticAt_id.pow 2).prod analyticAt_const)).add analyticAt_const
  have hDH (z : ℂ) (hz : z ∈ sphere ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4)) :
      deriv H z = (deriv (hillHminusDiscriminant q) (z^2)/hillHminusContinuedRoot (z^2,q))*(2*z) := by
    have hsq : HasDerivAt (fun w : ℂ => w^2) (2*z) z := by simpa using! (hasDerivAt_id z).pow 2
    exact ((hasDerivAt_hillHminusContinuedPrimitive (z^2,q) (D.cover k q hq z hz)).comp z hsq |>.add_const shift).deriv
  exact critical_basis_period_eq_primitive H
    (fun lambda => hillHminusUniformNumerator C N n (lambda,q))
    (fun lambda => hillHminusContinuedRoot (lambda,q)) (deriv (hillHminusDiscriminant q))
    (hillHminusUniformCriticalPoint C N n q) (n : ℂ) _ _ (by positivity) hH
    (D.numerator_factor n q hq) hDH hne

theorem norm_diagonal_period_le (n : ℕ+) (q : PeriodOneHminusOne) (hq : q ∈ V) :
    ‖hillHminusPeriodEntry C N n n q‖ ≤ (80/Real.pi)*A := by
  let d : ℝ := Real.pi^2/8*(n : ℝ)
  have hd : 0 < d := by dsimp only [d];positivity
  have hsep := D.diagonal_separation n q hq
  have hne (z : ℂ) (hz : z ∈ sphere ((Real.pi : ℂ)*(n : ℕ)) (Real.pi/4)) :
      z^2-hillHminusUniformCriticalPoint C N n q ≠ 0 := norm_pos_iff.mp (hd.trans_le (hsep z hz))
  rw [D.period_eq_primitive n n q hq (I*(n : ℂ)*Real.pi) hne,norm_mul,Complex.norm_natCast]
  have hi := norm_frequency_primitive_resolvent_integral_le
    (fun z => hillHminusContinuedPrimitive (z^2,q)+I*(n : ℂ)*Real.pi)
    (hillHminusUniformCriticalPoint C N n q) n A d D.amplitude_pos.le hd
    (D.primitive_bound n q hq) hsep
  apply (mul_le_mul_of_nonneg_left hi (show (0 : ℝ) ≤ n by positivity)).trans_eq
  dsimp only [d]
  field_simp
  ring

theorem norm_offDiagonal_period_le (n k : ℕ+) (hnk : n ≠ k) (q : PeriodOneHminusOne) (hq : q ∈ V) :
    ‖hillHminusPeriodEntry C N n k q‖ ≤ ((5/Real.pi)*A)/|(k : ℝ)-(n : ℝ)|^2 := by
  have hA := D.amplitude_pos
  let d : ℝ := Real.pi^2/4*|(k : ℝ)^2-(n : ℝ)^2|
  have hd : 0 < d := by
    dsimp only [d]
    exact mul_pos (by positivity) (abs_pos.mpr (positiveIndex_squared_sub_ne_zero k n (Ne.symm hnk)))
  have hsep := D.offDiagonal_separation n k hnk q hq
  have hne (z : ℂ) (hz : z ∈ sphere ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4)) :
      z^2-hillHminusUniformCriticalPoint C N n q ≠ 0 := norm_pos_iff.mp (hd.trans_le (hsep z hz))
  rw [D.period_eq_primitive n k q hq (I*(k : ℂ)*Real.pi) hne,norm_mul,Complex.norm_natCast]
  have hi := norm_frequency_primitive_resolvent_integral_le
    (fun z => hillHminusContinuedPrimitive (z^2,q)+I*(k : ℂ)*Real.pi)
    (hillHminusUniformCriticalPoint C N n q) k A d hA.le hd (D.primitive_bound k q hq) hsep
  calc
    _ ≤ (n : ℝ)*(2*Real.pi*(Real.pi/4)*(A*((5*Real.pi/2)*(k : ℝ))/d^2)) :=
      mul_le_mul_of_nonneg_left hi (by positivity)
    _ = ((20/Real.pi)*A)*((n : ℝ)*(k : ℝ)/|(k : ℝ)^2-(n : ℝ)^2|^2) := by
      dsimp only [d]
      field_simp
      ring
    _ ≤ ((20/Real.pi)*A)*(1/(4*|(k : ℝ)-(n : ℝ)|^2)) :=
      mul_le_mul_of_nonneg_left (positiveIndex_squared_energy_kernel_le n k hnk) (by positivity)
    _ = _ := by ring

theorem norm_period_le (n k : ℕ+) (q : PeriodOneHminusOne) (hq : q ∈ V) :
    ‖hillHminusPeriodEntry C N n k q‖ ≤
      (80/Real.pi)*A*(if n = k then 1 else |(k : ℝ)-(n : ℝ)|⁻¹^2) := by
  have hA := D.amplitude_pos
  by_cases hnk : n = k
  · subst n
    simpa only [ite_true,mul_one] using D.norm_diagonal_period_le k q hq
  · rw [if_neg hnk]
    apply (D.norm_offDiagonal_period_le n k hnk q hq).trans
    rw [div_eq_mul_inv,inv_pow]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (by norm_num) Real.pi_pos.le) hA.le) (by positivity)

end HillHminusUniformPeriodData
end NLS.KdV
