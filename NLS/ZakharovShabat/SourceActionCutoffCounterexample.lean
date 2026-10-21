import NLS.ZakharovShabat.SourceActionPowerSum
import NLS.ZakharovShabat.Section17EnumerationCutoff

set_option autoImplicit false
noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceBirkhoffMapComplexData
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
  {W₀ B W : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- An actual one-mode image has zero absolute-index tail at N=1 but a nonzero
tail after the first enumeration position. Its selected zeroth action is already zero. -/
theorem printed_action_cutoff_counterexample
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s) (hp2 : p ≤ 2) :
    ∃ φ : realTypeSourceSubmodule p,
      (sourceRealAction hp hp1 φ.val φ.property (section17Mode 1)).re = 0 ∧
      (∑' n : ℤ, if 1 < n.natAbs then
        |(sourceRealAction hp hp1 φ.val φ.property n).re|^(p.toReal/2) else 0) = 0 ∧
      (∑' k : ℕ, if 1 < k then
        |(sourceRealAction hp hp1 φ.val φ.property (section17Mode k)).re|^(p.toReal/2) else 0) = 1 := by
  let z : RealCoeff p × RealCoeff p := (lp.single p 1 1,lp.single p 1 1)
  let φ := (D.realHomeomorph hp2).symm z
  have hout : sourceRealBirkhoffMap hp hp1 s φ = z := (D.realHomeomorph hp2).apply_symm_apply z
  have hr : 0 < p.toReal/2 := by
    exact half_pos (ENNReal.toReal_pos (zero_lt_one.trans hp1).ne' hp)
  have ha (n : ℤ) : (sourceRealAction hp hp1 φ.val φ.property n).re = (if n=1 then 1 else 0) := by
    have h := D.real_map_action_radius φ n
    rw [hout] at h
    by_cases hn : n=1 <;> simp [z,lp.single_apply,hn] at h ⊢ <;> linarith
  refine ⟨φ,?_,?_,?_⟩
  · rw [ha]
    norm_num [section17Mode]
  · calc
      _ = ∑' _n : ℤ, (0:ℝ) := by
        apply tsum_congr
        intro n
        rw [ha]
        by_cases hn : n=1 <;> simp [hn,Real.zero_rpow hr.ne']
      _ = 0 := by simp
  · have he (k : ℕ) : (if 1<k then
        |(sourceRealAction hp hp1 φ.val φ.property (section17Mode k)).re|^(p.toReal/2) else 0) =
        (if k=3 then 1 else 0) := by
      rw [ha]
      by_cases hk : k=3
      · subst k
        norm_num [section17Mode]
      · have hm : section17Mode k ≠ 1 := fun h => hk ((section17Mode_eq_one_iff k).mp h)
        simp [hk,hm,Real.zero_rpow hr.ne']
    calc
      _ = ∑' k : ℕ, if k=3 then (1:ℝ) else 0 := tsum_congr he
      _ = 1 := by simp

end NLS.ZakharovShabat.SourceBirkhoffMapComplexData
