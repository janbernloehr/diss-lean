import NLS.ComplexAnalysis.NormalizedLogarithmicPrimitive
import NLS.ComplexAnalysis.ContinuousLogarithmUnique
import Mathlib.Topology.Algebra.Field

/-! # Recovering a trace from a normalized logarithmic primitive

On any connected open set, an analytic root of `D² - 4` determines
the logarithmic derivative of `(D + R)/2`. One exponential value of a
primitive of `D'/R` fixes both its hyperbolic trace identities.
-/

noncomputable section
open Set Filter Topology Complex
open scoped ComplexConjugate
namespace NLS.ComplexAnalysis

theorem hasDerivAt_traceRoot_multiplier
    (D R : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U)
    (hD : AnalyticOnNhd ℂ D U) (hR : AnalyticOnNhd ℂ R U)
    (hsq : ∀ z ∈ U, R z ^ 2 = D z ^ 2 - 4)
    (z : ℂ) (hz : z ∈ U) (hne : R z ≠ 0) :
    HasDerivAt (fun w => (D w + R w)/2)
      (((D z + R z)/2) * (deriv D z/R z)) z := by
  have he : (fun w => R w ^ 2) =ᶠ[𝓝 z] (fun w => D w ^ 2 - 4) := by
    filter_upwards [hU.mem_nhds hz] with w hw
    exact hsq w hw
  have hd := ((hR z hz).differentiableAt.hasDerivAt.pow 2).unique
    ((((hD z hz).differentiableAt.hasDerivAt.pow 2).sub_const 4).congr_of_eventuallyEq he)
  simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one] at hd
  convert! ((hD z hz).differentiableAt.hasDerivAt.add
    (hR z hz).differentiableAt.hasDerivAt).div_const 2 using 1
  field_simp [hne]
  linear_combination -hd/2

theorem exp_primitive_of_traceRoot
    (D R F : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U) (hconn : IsPreconnected U)
    (hD : AnalyticOnNhd ℂ D U) (hR : AnalyticOnNhd ℂ R U)
    (hsq : ∀ z ∈ U, R z ^ 2 = D z ^ 2 - 4)
    (hne : ∀ z ∈ U, R z ≠ 0)
    (hF : ∀ z ∈ U, HasDerivAt F (deriv D z/R z) z)
    (a : ℂ) (ha : a ∈ U) (hFa : exp (F a) = (D a + R a)/2) :
    ∀ z ∈ U, exp (F z) = (D z + R z)/2 := by
  let M : ℂ → ℂ := fun z => (D z + R z)/2
  have hM (z : ℂ) (hz : z ∈ U) :
      HasDerivAt M (M z * (deriv D z/R z)) z :=
    hasDerivAt_traceRoot_multiplier D R U hU hD hR hsq z hz (hne z hz)
  have : NeBot (𝓝[U] a) := by rw [hU.nhdsWithin_eq ha]; infer_instance
  have hnorm (z : ℂ) (hz : z ∈ U) :
      HasDerivAt (fun w => F w - F a) (deriv D z/R z) z := (hF z hz).sub_const _
  have hlim : Tendsto (fun z => F z - F a) (𝓝[U] a) (𝓝 0) := by
    simpa only [sub_self] using
      ((hF a ha).continuousAt.tendsto.mono_left nhdsWithin_le_nhds).sub
        (tendsto_const_nhds (x := F a))
  have hm := multiplier_eq_exp_of_normalized_primitive
    (fun z => deriv D z/R z) (fun z => F z - F a) M U a (M a)
    hU hconn hnorm hM hlim (hM a ha).continuousAt.continuousWithinAt
  intro z hz
  change exp (F z) = M z
  change exp (F a) = M a at hFa
  rw [hm z hz, ← hFa, ← exp_add]
  congr 1
  ring

theorem exp_neg_primitive_of_traceRoot
    (D R F : ℂ → ℂ) (z : ℂ)
    (hsq : R z ^ 2 = D z ^ 2 - 4)
    (he : exp (F z) = (D z + R z)/2) :
    exp (-F z) = (D z - R z)/2 := by
  have hp : ((D z + R z)/2)*((D z - R z)/2) = 1 := by
    linear_combination -hsq/4
  apply mul_left_cancel₀ (exp_ne_zero (F z))
  rw [← exp_add, add_neg_cancel, exp_zero, he, hp]

theorem traceRoot_identities_of_exp
    (D R F : ℂ → ℂ) (z : ℂ)
    (hsq : R z ^ 2 = D z ^ 2 - 4)
    (he : exp (F z) = (D z + R z)/2) :
    2*cosh (F z) = D z ∧ 2*sinh (F z) = R z := by
  have hn := exp_neg_primitive_of_traceRoot D R F z hsq he
  constructor
  · rw [cosh, he, hn]; ring
  · rw [sinh, he, hn]; ring

/-- The free-sheet minus-conjugate sign at one real anchor determines
reflection on a connected conjugation-invariant domain. -/
theorem traceRoot_primitive_reflection
    (D R F : ℂ → ℂ) (U : Set ℂ) (hconn : IsPreconnected U)
    (hU : ∀ z ∈ U, conj z ∈ U)
    (hD : ∀ z ∈ U, D (conj z) = conj (D z))
    (hR : ContinuousOn R U) (hF : ContinuousOn F U)
    (hsq : ∀ z ∈ U, R z ^ 2 = D z ^ 2 - 4)
    (hne : ∀ z ∈ U, R z ≠ 0)
    (hexp : ∀ z ∈ U, exp (F z) = (D z + R z)/2)
    (a : ℂ) (ha : a ∈ U) (hRa : R a = -conj (R (conj a)))
    (hFa : F a = -conj (F (conj a))) :
    ∀ z ∈ U, R (conj z) = -conj (R z) ∧ F (conj z) = -conj (F z) := by
  let S : ℂ → ℂ := fun z => -conj (R (conj z))
  let G : ℂ → ℂ := fun z => -conj (F (conj z))
  have hS : ContinuousOn S U :=
    (continuous_conj.comp_continuousOn (hR.comp continuous_conj.continuousOn hU)).neg
  have hG : ContinuousOn G U :=
    (continuous_conj.comp_continuousOn (hF.comp continuous_conj.continuousOn hU)).neg
  have hsqS : EqOn (S^2) (R^2) U := by
    intro z hz
    change (-conj (R (conj z)))^2 = R z^2
    rw [neg_sq, ← map_pow, hsq _ (hU z hz), map_sub, map_pow, hD z hz,
      conj_conj, hsq z hz]
    simp only [map_ofNat]
  have hSR : EqOn S R U := hconn.eq_of_sq_eq hS hR hsqS
    (fun {z} hz => hne z hz) ha hRa.symm
  have hr (z : ℂ) (hz : z ∈ U) : R (conj z) = -conj (R z) := by
    have he := congrArg (fun w : ℂ => -conj w) (hSR hz)
    simpa only [S, map_neg, conj_conj, neg_neg] using he
  have hGF : EqOn G F U := by
    apply continuousLogarithms_eqOn G F U hconn hG hF _ a ha hFa.symm
    intro z hz
    change exp (-conj (F (conj z))) = exp (F z)
    calc
      _ = conj (exp (-F (conj z))) := by rw [← exp_conj, map_neg]
      _ = conj ((D (conj z) - R (conj z))/2) := congrArg conj
        (exp_neg_primitive_of_traceRoot D R F _ (hsq _ (hU z hz)) (hexp _ (hU z hz)))
      _ = (D z + R z)/2 := by
        rw [hD z hz, hr z hz]
        simp only [map_div₀, sub_neg_eq_add, map_add, conj_conj, map_ofNat]
      _ = exp (F z) := (hexp z hz).symm
  intro z hz
  refine ⟨hr z hz,?_⟩
  have he := congrArg (fun w : ℂ => -conj w) (hGF hz)
  simpa only [G, map_neg, conj_conj, neg_neg] using he

/-- A finite limit at a characteristic endpoint has zero hyperbolic
sine and exponential equal to half the endpoint trace. This does not
choose the integer multiple of `π i` represented by that limit. -/
theorem traceRoot_primitive_boundary_values
    (D R F : ℂ → ℂ) (U : Set ℂ) (c A : ℂ) [NeBot (𝓝[U] c)]
    (hD : ContinuousAt D c) (hc : D c ^ 2 = 4)
    (hsq : ∀ z ∈ U, R z ^ 2 = D z ^ 2 - 4)
    (hexp : ∀ z ∈ U, exp (F z) = (D z + R z)/2)
    (hlim : Tendsto F (𝓝[U] c) (𝓝 A)) :
    exp A = D c/2 ∧ 2*cosh A = D c ∧ sinh A = 0 ∧
      Tendsto R (𝓝[U] c) (𝓝 0) := by
  have htrace (z : ℂ) (hz : z ∈ U) :=
    traceRoot_identities_of_exp D R F z (hsq z hz) (hexp z hz)
  have hclim : Tendsto (fun z => 2*cosh (F z)) (𝓝[U] c) (𝓝 (2*cosh A)) :=
    tendsto_const_nhds.mul (continuous_cosh.tendsto A |>.comp hlim)
  have hr : Tendsto R (𝓝[U] c) (𝓝 (2*sinh A)) := by
    apply (tendsto_const_nhds.mul (continuous_sinh.tendsto A |>.comp hlim)).congr'
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact (htrace z hz).2
  have hcosh : 2*cosh A = D c := by
    apply tendsto_nhds_unique hclim
    apply (hD.tendsto.mono_left nhdsWithin_le_nhds).congr'
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact (htrace z hz).1.symm
  have hzero : (2*sinh A)^2 = 0 := by
    apply tendsto_nhds_unique (hr.pow 2)
    have hd : Tendsto (fun z => D z^2 - 4) (𝓝[U] c) (𝓝 (D c^2 - 4)) :=
      ((hD.tendsto.mono_left nhdsWithin_le_nhds).pow 2).sub_const 4
    rw [hc,sub_self] at hd
    apply hd.congr'
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact (hsq z hz).symm
  have hsinh : sinh A = 0 :=
    (mul_eq_zero.mp (sq_eq_zero_iff.mp hzero)).resolve_left (by norm_num)
  refine ⟨?_,hcosh,hsinh,?_⟩
  · rw [← cosh_add_sinh,hsinh,add_zero]
    linear_combination hcosh/2
  · simpa only [hsinh,mul_zero] using hr

end NLS.ComplexAnalysis
