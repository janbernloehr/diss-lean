import NLS.KdV.HillFreePeriodJacobian
import Mathlib.Topology.Algebra.Order.Field

/-! The literal inverse-index Hill equation weight tends to 2*pi
for a fixed physical row when the omitted numerator index escapes. -/
noncomputable section
open Filter Topology Complex
open scoped ENNReal Classical
namespace NLS.KdV

theorem eventually_fixed_pnat_ne_escaping (n : ℕ → ℕ+)
    (hn : Tendsto (fun j => (n j:ℕ)) atTop atTop) (m : ℕ+) :
    ∀ᶠ j in atTop, m ≠ n j := by
  filter_upwards [hn.eventually (eventually_ge_atTop ((m:ℕ)+1))] with j hj
  intro he
  have hv := congrArg (fun k : ℕ+ => (k:ℕ)) he
  omega

theorem hillPeriodEquationWeight_eq_inverse (n m : ℕ+) :
    hillPeriodEquationWeight n m = (2*Real.pi:ℂ)*(1-(((m:ℕ):ℂ)*((n:ℕ):ℂ)⁻¹)^2) := by
  have hn : ((n:ℕ):ℂ) ≠ 0 := by exact_mod_cast n.ne_zero
  unfold hillPeriodEquationWeight
  field_simp [hn]

theorem tendsto_hillPeriodEquationWeight_escaping (n : ℕ → ℕ+)
    (hn : Tendsto (fun j => (n j:ℕ)) atTop atTop) (m : ℕ+) :
    Tendsto (fun j => hillPeriodEquationWeight (n j) m) atTop (𝓝 (2*Real.pi:ℂ)) := by
  have hnr : Tendsto (fun j => ((n j:ℕ):ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hn
  have hr := tendsto_inv_atTop_zero.comp hnr
  have hc : Tendsto (fun j => (((n j:ℕ):ℂ))⁻¹) atTop (𝓝 (0:ℂ)) := by
    simpa only [Function.comp_def,ofReal_inv,ofReal_natCast,ofReal_zero] using Complex.continuous_ofReal.continuousAt.tendsto.comp hr
  simp_rw [hillPeriodEquationWeight_eq_inverse]
  simpa only [mul_zero,zero_pow (by norm_num : (2:ℕ) ≠ 0),sub_zero,mul_one] using
    ((tendsto_const_nhds (x := (1:ℂ))).sub ((hc.const_mul ((m:ℕ):ℂ)).pow 2)).const_mul (2*Real.pi:ℂ)

end NLS.KdV
