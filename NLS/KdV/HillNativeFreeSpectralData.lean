import NLS.KdV.HillNativeCartesianOrigin
import NLS.KdV.ClassicalHillFreeFlow

/-! Exact intrinsic free midpoint, Dirichlet energy, norming multiplier
and prescribed sheet values, retaining EVERY original positive index.
These are the actual data needed for Cartesian first variations. -/
noncomputable section
open Set Complex
open scoped Classical
namespace NLS.KdV

theorem hillHminusCanonicalEnergyMidpoint_zero (n : ℕ+) :
    hillHminusCanonicalEnergyMidpoint n 0 = (freeHillValue (n:ℕ):ℂ) := by
  have hr : IsRealPeriodOneHminusOne (0 : PeriodOneHminusOne) := by intro k; simp
  have hp := hillHminusLabels_free_pair hr n
  rw [hillHminusCanonicalEnergyMidpoint_real n 0 hr,hp.1,hp.2]
  ring

theorem hillHminusCanonicalDirichlet_zero_eq_free (n : ℕ+) :
    hillHminusCanonicalDirichlet n 0 = (freeHillValue (n:ℕ):ℂ) := by
  rw [hillHminusCanonicalDirichlet_zero]
  simp only [freeHillValue,Int.cast_natCast,Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_natCast]
  ring

theorem hillHminusCanonicalDirichlet_eq_midpoint_zero (n : ℕ+) :
    hillHminusCanonicalDirichlet n 0 = hillHminusCanonicalEnergyMidpoint n 0 := by
  rw [hillHminusCanonicalDirichlet_zero_eq_free,hillHminusCanonicalEnergyMidpoint_zero]

theorem hillHminusCanonicalCartesianWeight_zero (n : ℕ+) :
    hillHminusCanonicalCartesianWeight n 0 = 0 := by
  rw [hillHminusCanonicalCartesianWeight,hillHminusCanonicalGapSquare_zero,norm_zero,Real.sqrt_zero,
    hillHminusCanonicalDirichlet_eq_midpoint_zero,sub_self,norm_zero,add_zero]

theorem hillHminusDirichletNorming_zero (n : ℕ+) :
    hillHminusDirichletNorming n 0 = (-1:ℂ)^(n:ℕ) := by
  have hr : IsRealPeriodOneHminusOne (0 : PeriodOneHminusOne) := by intro k; simp
  have hq := real_mem_hillHminusCanonicalDirichletDomain 0 hr
  have h := hillHminusDirichletNorming_eq_hillL2 n (0 : Coeff 2) (by simpa only [map_zero] using hq)
  simp only [map_zero] at h
  rw [h,hillHminusCanonicalDirichlet_zero]
  have hz : (Real.pi:ℂ)*((n:ℕ):ℂ) ≠ 0 := mul_ne_zero
    (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) (by exact_mod_cast n.ne_zero)
  rw [show (((Real.pi*(n:ℝ))^2:ℝ):ℂ) = ((Real.pi:ℂ)*(n:ℕ))^2 by push_cast; rfl,
    hillL2DirichletTerminal_free_sq _ hz,mul_comm (Real.pi:ℂ) ((n:ℕ):ℂ)]
  have hc := congrArg Complex.ofReal (Real.cos_nat_mul_pi (n:ℕ))
  simpa only [Complex.ofReal_cos,Complex.ofReal_mul,Complex.ofReal_natCast,Complex.ofReal_pow,
    Complex.ofReal_neg,Complex.ofReal_one] using hc

theorem hillHminusDirichletSheet_zero (n : ℕ+) : hillHminusDirichletSheet n 0 = 0 := by
  rw [hillHminusDirichletSheet,hillHminusDirichletNorming_zero,← inv_pow,inv_neg,inv_one,sub_self]

end NLS.KdV
