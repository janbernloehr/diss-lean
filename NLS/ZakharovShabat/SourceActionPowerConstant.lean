import NLS.ZakharovShabat.SourceBirkhoffGlobalInverse
import Mathlib.Analysis.Convex.SpecificFunctions.Pow

set_option autoImplicit false
noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The sharp coordinate bound below exponent two has constant two. -/
theorem real_pair_power_le_two_action (r : ℝ) (hr : 0 < r) (hr2 : r ≤ 2) (x y : ℝ) :
    |x|^r+|y|^r ≤ 2*((x^2+y^2)/2)^(r/2) := by
  have he (z : ℝ) : (z^2)^(r/2) = |z|^r := by
    rw [← sq_abs,← Real.rpow_two,← Real.rpow_mul (abs_nonneg z)]
    congr 1
    ring
  have hc := (Real.concaveOn_rpow (by linarith : 0 ≤ r/2) (by linarith : r/2 ≤ 1)).2
    (show x^2 ∈ Ici 0 from sq_nonneg x) (show y^2 ∈ Ici 0 from sq_nonneg y)
    (by norm_num : 0 ≤ (1:ℝ)/2) (by norm_num : 0 ≤ (1:ℝ)/2) (by norm_num : (1:ℝ)/2+1/2=1)
  simp only [smul_eq_mul,he] at hc
  have havg : (1:ℝ)/2*x^2+1/2*y^2=(x^2+y^2)/2 := by ring
  rw [havg] at hc
  linarith

/-- The printed smaller constant is strictly insufficient for balanced coordinates. -/
theorem printed_action_power_constant_lt_two (r : ℝ) (hr2 : r < 2) :
    (2:ℝ)^(r/2) < 2 := by
  have h := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1:ℝ)<2)
    (by linarith : r/2<1)
  simpa only [Real.rpow_one] using h

namespace SourceBirkhoffMapComplexData
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
  {W₀ B W : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- An actual original source realizes balanced coordinates and refutes the
printed norm-to-action constant at every exponent strictly between one and two. -/
theorem printed_action_power_constant_counterexample
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s) (hp2 : p < 2) :
    ∃ φ : realTypeSourceSubmodule p,
      (sourceRealBirkhoffMap hp hp1 s φ).1 0 = 1 ∧
      (sourceRealBirkhoffMap hp hp1 s φ).2 0 = 1 ∧
      (sourceRealAction hp hp1 φ.val φ.property 0).re = 1 ∧
      (2:ℝ)^(p.toReal/2)*(sourceRealAction hp hp1 φ.val φ.property 0).re^(p.toReal/2) <
        |(sourceRealBirkhoffMap hp hp1 s φ).1 0|^p.toReal+
          |(sourceRealBirkhoffMap hp hp1 s φ).2 0|^p.toReal := by
  let z : RealCoeff p × RealCoeff p := (lp.single p 0 1,lp.single p 0 1)
  let φ := (D.realHomeomorph hp2.le).symm z
  have hout : sourceRealBirkhoffMap hp hp1 s φ = z := (D.realHomeomorph hp2.le).apply_symm_apply z
  have hx : (sourceRealBirkhoffMap hp hp1 s φ).1 0=1 := by rw [hout]; simp [z]
  have hy : (sourceRealBirkhoffMap hp hp1 s φ).2 0=1 := by rw [hout]; simp [z]
  have hact : (sourceRealAction hp hp1 φ.val φ.property 0).re=1 := by
    have h := D.real_map_action_radius φ 0
    rw [hx,hy] at h
    linarith
  refine ⟨φ,hx,hy,hact,?_⟩
  rw [hx,hy,hact]
  simpa only [abs_one,Real.one_rpow,mul_one,one_add_one_eq_two] using printed_action_power_constant_lt_two p.toReal
    (by simpa using (ENNReal.toReal_lt_toReal hp (by norm_num : (2:ℝ≥0∞)≠⊤)).mpr hp2)

/-- The literal summed inequality on p.79 fails at an actual one-mode balanced image. -/
theorem printed_action_power_sum_counterexample
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s) (hp2 : p < 2) :
    ∃ φ : realTypeSourceSubmodule p,
      (∑' n : ℤ, (|(sourceRealBirkhoffMap hp hp1 s φ).1 n|^p.toReal+
        |(sourceRealBirkhoffMap hp hp1 s φ).2 n|^p.toReal)) = 2 ∧
      (∑' n : ℤ, |(sourceRealAction hp hp1 φ.val φ.property n).re|^(p.toReal/2)) = 1 ∧
      ¬(∑' n : ℤ, (|(sourceRealBirkhoffMap hp hp1 s φ).1 n|^p.toReal+
          |(sourceRealBirkhoffMap hp hp1 s φ).2 n|^p.toReal)) ≤
        (2:ℝ)^(p.toReal/2)*
          (∑' n : ℤ, |(sourceRealAction hp hp1 φ.val φ.property n).re|^(p.toReal/2)) := by
  let z : RealCoeff p × RealCoeff p := (lp.single p 0 1,lp.single p 0 1)
  let φ := (D.realHomeomorph hp2.le).symm z
  have hout : sourceRealBirkhoffMap hp hp1 s φ = z := (D.realHomeomorph hp2.le).apply_symm_apply z
  have hr : 0 < p.toReal := ENNReal.toReal_pos (zero_lt_one.trans hp1).ne' hp
  have hxy (n : ℤ) : (sourceRealBirkhoffMap hp hp1 s φ).1 n = (if n=0 then 1 else 0) ∧
      (sourceRealBirkhoffMap hp hp1 s φ).2 n = (if n=0 then 1 else 0) := by
    rw [hout]
    by_cases hn : n=0 <;> simp [z,lp.single_apply,hn]
  have ha (n : ℤ) : (sourceRealAction hp hp1 φ.val φ.property n).re = (if n=0 then 1 else 0) := by
    have h := D.real_map_action_radius φ n
    rw [(hxy n).1,(hxy n).2] at h
    split_ifs at h ⊢ <;> linarith
  have he : (∑' n : ℤ, (|(sourceRealBirkhoffMap hp hp1 s φ).1 n|^p.toReal+
      |(sourceRealBirkhoffMap hp hp1 s φ).2 n|^p.toReal)) = 2 := by
    have heq (n : ℤ) : |(sourceRealBirkhoffMap hp hp1 s φ).1 n|^p.toReal+
        |(sourceRealBirkhoffMap hp hp1 s φ).2 n|^p.toReal = (if n=0 then 2 else 0) := by
      rw [(hxy n).1,(hxy n).2]
      split_ifs <;> norm_num [Real.zero_rpow hr.ne']
    calc
      _ = ∑' n : ℤ, if n=0 then (2:ℝ) else 0 := tsum_congr heq
      _ = 2 := by simp
  have hi : (∑' n : ℤ, |(sourceRealAction hp hp1 φ.val φ.property n).re|^(p.toReal/2)) = 1 := by
    simp_rw [ha]
    simp [apply_ite,Real.zero_rpow (by positivity : p.toReal/2≠0)]
  refine ⟨φ,he,hi,?_⟩
  rw [he,hi,mul_one]
  exact not_le_of_gt (printed_action_power_constant_lt_two p.toReal
    (by simpa using (ENNReal.toReal_lt_toReal hp (by norm_num : (2:ℝ≥0∞)≠⊤)).mpr hp2))

end SourceBirkhoffMapComplexData
end NLS.ZakharovShabat
