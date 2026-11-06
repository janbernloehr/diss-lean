import NLS.SequenceSpaces.SeparatedReciprocalEnvelope
import NLS.KdV.FreeHill

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal Classical

namespace NLS.KdV



/-- The complete off-diagonal free-energy separation kernel, including
positive gaps arbitrarily close to the deleted index. -/
def hillOffDiagonalPeriodKernel (n : ℕ) (m : ℤ) : ℝ :=
  if 0<m ∧ m≠(n : ℤ) then
    (n : ℝ)/((m : ℝ)*|freeHillValue m-freeHillValue n|) else 0

theorem hillOffDiagonalPeriodKernel_nonneg (n : ℕ) (m : ℤ) :
    0≤hillOffDiagonalPeriodKernel n m := by
  unfold hillOffDiagonalPeriodKernel
  split_ifs with hm
  · have hm0 : (0:ℝ)<m := by exact_mod_cast hm.1
    positivity
  · rfl

/-- A single translated reciprocal l1 envelope controls all off-diagonal
positions, without a cutoff such as k>=2*n. -/
theorem hillOffDiagonalPeriodKernel_le_envelope (n : ℕ) (m : ℤ) :
    hillOffDiagonalPeriodKernel n m≤(Real.pi^2)⁻¹*‖Coeff.separatedReciprocalEnvelope (n : ℤ) m‖ := by
  unfold hillOffDiagonalPeriodKernel
  split_ifs with hm
  · have hm0 : (0:ℝ)<m := by exact_mod_cast hm.1
    have hn0 : (0:ℝ)≤n := Nat.cast_nonneg n
    have hsum : 0<(m : ℝ)+(n : ℝ) := by positivity
    have hd : (m : ℝ)-(n : ℝ)≠0 := sub_ne_zero.mpr (by exact_mod_cast hm.2)
    have he : freeHillValue m-freeHillValue n=Real.pi^2*((m : ℝ)-(n : ℝ))*((m : ℝ)+(n : ℝ)) := by
      simp only [freeHillValue,Int.cast_natCast]
      ring
    rw [Coeff.separatedReciprocalEnvelope_apply,norm_mul,norm_inv,norm_inv,Complex.norm_intCast,
      Complex.norm_intCast,Int.cast_sub,Int.cast_natCast,abs_of_pos hm0,he,abs_mul,abs_mul,
      abs_of_pos (sq_pos_of_pos Real.pi_pos),abs_of_pos hsum]
    have halg : (n : ℝ)/((m : ℝ)*(Real.pi^2*|((m : ℝ)-(n : ℝ))| *((m : ℝ)+(n : ℝ)))) =
        ((Real.pi^2)⁻¹*((m : ℝ))⁻¹*|((m : ℝ)-(n : ℝ))|⁻¹)*((n : ℝ)/((m : ℝ)+(n : ℝ))) := by
      field_simp
    rw [halg]
    have hratio : (n : ℝ)/((m : ℝ)+(n : ℝ))≤1 := (div_le_one hsum).mpr (by linarith)
    apply (mul_le_mul_of_nonneg_left hratio (by positivity : 0≤(Real.pi^2)⁻¹*(m : ℝ)⁻¹*|((m : ℝ)-(n : ℝ))|⁻¹)).trans_eq
    ring
  · exact mul_nonneg (by positivity) (norm_nonneg _)

theorem summable_hillOffDiagonalPeriodKernel (n : ℕ) :
    Summable (hillOffDiagonalPeriodKernel n) := by
  have he := (lp.hasSum_norm (p := 1) (by simp) (Coeff.separatedReciprocalEnvelope (n : ℤ))).summable
  simp only [ENNReal.toReal_one,Real.rpow_one] at he
  exact (he.mul_left ((Real.pi^2)⁻¹)).of_nonneg_of_le (hillOffDiagonalPeriodKernel_nonneg n)
    (hillOffDiagonalPeriodKernel_le_envelope n)

theorem tsum_hillOffDiagonalPeriodKernel_le (n : ℕ) :
    (∑' m : ℤ, hillOffDiagonalPeriodKernel n m)≤4/Real.pi^2 := by
  have he := (lp.hasSum_norm (p := 1) (by simp) (Coeff.separatedReciprocalEnvelope (n : ℤ)))
  simp only [ENNReal.toReal_one,Real.rpow_one] at he
  have hh := (summable_hillOffDiagonalPeriodKernel n).tsum_le_tsum
    (hillOffDiagonalPeriodKernel_le_envelope n) (he.summable.mul_left ((Real.pi^2)⁻¹))
  rw [tsum_mul_left,he.tsum_eq] at hh
  exact hh.trans ((mul_le_mul_of_nonneg_left (Coeff.norm_separatedReciprocalEnvelope_le (n : ℤ))
    (by positivity)).trans_eq (by ring))

/-- The complete separation-kernel mass vanishes at high deleted index. -/
theorem tendsto_tsum_hillOffDiagonalPeriodKernel_zero :
    Tendsto (fun n : ℕ => ∑' m : ℤ, hillOffDiagonalPeriodKernel n m) atTop (𝓝 0) := by
  have ht := Coeff.tendsto_norm_separatedReciprocalEnvelope_zero.comp
    (show Tendsto (fun n : ℕ => (n : ℤ)) atTop cofinite from
      Int.ofNat_injective.tendsto_cofinite.mono_left atTop_le_cofinite)
  have hu := (tendsto_const_nhds (x := (Real.pi^2)⁻¹)).mul ht
  simp only [mul_zero] at hu
  apply squeeze_zero (fun n => tsum_nonneg (hillOffDiagonalPeriodKernel_nonneg n)) _ hu
  intro n
  have he := (lp.hasSum_norm (p := 1) (by simp) (Coeff.separatedReciprocalEnvelope (n : ℤ)))
  simp only [ENNReal.toReal_one,Real.rpow_one] at he
  have hh := (summable_hillOffDiagonalPeriodKernel n).tsum_le_tsum
    (hillOffDiagonalPeriodKernel_le_envelope n) (he.summable.mul_left ((Real.pi^2)⁻¹))
  simpa only [tsum_mul_left,he.tsum_eq,Function.comp_def] using hh

end NLS.KdV
