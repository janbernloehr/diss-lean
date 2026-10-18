import NLS.ZakharovShabat.SourceStandardRootAlgebra
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Analysis.Complex.SqrtDeriv
import Mathlib.Tactic.FunProp

/-! # Normalization of the standard root at complex infinity

The normalized standard root divided by the spectral parameter tends to
minus one, with no restriction on the complex center or squared gap.
-/

noncomputable section
open Filter Topology Complex
namespace NLS.ZakharovShabat

theorem normalizedStandardRoot_div_tendsto (t g : ℂ) :
    Tendsto (fun z : ℂ => normalizedStandardRoot t g z / z)
      (Bornology.cobounded ℂ) (𝓝 (-1)) := by
  let q : ℂ → ℂ := fun w => 1-g*w^2/(4*(t*w-1)^2)
  have hq : ContinuousAt q 0 := by unfold q; fun_prop (disch := norm_num)
  have hs : ContinuousAt (fun w => Complex.sqrt (q w)) 0 :=
    (Complex.continuousAt_sqrt (by left; norm_num [q])).comp hq
  have hc : ContinuousAt (fun w : ℂ => (t*w-1)*Complex.sqrt (q w)) 0 := by
    exact (continuousAt_const.mul continuousAt_id |>.sub continuousAt_const).mul hs
  have hlim := hc.tendsto.comp (tendsto_inv₀_cobounded (α := ℂ))
  simp only [mul_zero,zero_sub,q,zero_pow (by norm_num : (2:ℕ) ≠ 0),zero_div,
    sub_zero,Complex.sqrt_one,neg_mul,one_mul] at hlim
  apply hlim.congr'
  filter_upwards [tendsto_norm_cobounded_atTop.eventually (eventually_gt_atTop (max ‖t‖ 0))] with z hz
  have hz0 : z ≠ 0 := norm_pos_iff.mp ((le_max_right ‖t‖ 0).trans_lt hz)
  have htz : t-z ≠ 0 := by
    intro h
    have he := sub_eq_zero.mp h
    rw [← he] at hz
    exact (not_lt_of_ge (le_max_left ‖t‖ 0)) hz
  have htw : t*z⁻¹-1 ≠ 0 := by
    intro h
    have he : t-z = 0 := by
      have hh := congrArg (fun a : ℂ => a*z) h
      simp only [sub_mul,mul_assoc,inv_mul_cancel₀ hz0,mul_one,one_mul,zero_mul] at hh
      exact hh
    exact htz he
  have hrad : 1-g*z⁻¹^2/(4*(t*z⁻¹-1)^2) = 1-g/(4*(t-z)^2) := by
    field_simp
  dsimp only [Function.comp_def]
  rw [hrad]
  unfold normalizedStandardRoot
  field_simp

end NLS.ZakharovShabat
