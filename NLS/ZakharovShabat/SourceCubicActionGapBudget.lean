import NLS.ZakharovShabat.SourcePrimitivePowerCubicLowerBound
import NLS.ZakharovShabat.SourceRenormalizedHamiltonian
import NLS.ZakharovShabat.SourceActionExponentDifferential

/-! # Summable action-gap contributions to the cubic-moment budget -/
noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- The cubic action divided by the squared gap, equal to zero at a collapsed gap. -/
def sourceCubicActionGapTerm (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (n : ℤ) : ℝ :=
  ‖sourceComplexAction hp hp1 n ψ‖^3 /
    ‖canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n‖^2

theorem sourceCubicActionGapTerm_nonneg (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (n : ℤ) :
    0 ≤ sourceCubicActionGapTerm hp hp1 ψ n := by unfold sourceCubicActionGapTerm; positivity

theorem sourceCubicActionGapTerm_of_collapsed (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (n : ℤ)
    (hg : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n = 0) :
    sourceCubicActionGapTerm hp hp1 ψ n = 0 := by
  simp only [sourceCubicActionGapTerm,hg,norm_zero,zero_pow (by norm_num : (2:ℕ) ≠ 0),div_zero]

/-- For real sources the correction detects precisely the open gaps. -/
theorem sourceCubicActionGapTerm_pos_iff (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (n : ℤ) :
    0 < sourceCubicActionGapTerm hp hp1 φ.val n ↔
      canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0 := by
  constructor
  · intro h hg
    rw [sourceCubicActionGapTerm_of_collapsed hp hp1 φ.val n hg] at h
    exact lt_irrefl 0 h
  · intro hg
    have ha : sourceComplexAction hp hp1 n φ.val ≠ 0 := by
      rw [sourceComplexAction_eq_sourceRealAction hp hp1 n φ.val φ.property]
      intro hz
      have h := (sourceRealAction_nonneg_and_eq_zero_iff_gap_zero hp hp1 φ.val φ.property n).2.2.mp hz
      exact hg (by simpa only [sourcePeriodicGapDisplacement_apply] using h)
    exact div_pos (pow_pos (norm_pos_iff.mpr ha) _) (pow_pos (norm_pos_iff.mpr hg) _)

/-- The quotient is independent of the coefficient-space exponent. -/
theorem sourceCubicActionGapTerm_exponent (hp : p ≠ ⊤) (hq : q ≠ ⊤) (hp1 : 1 < p) (hq1 : 1 < q)
    (hpq : p ≤ q) (φ : realTypeSourceSubmodule p) (n : ℤ) :
    sourceCubicActionGapTerm hp hp1 φ.val n =
      sourceCubicActionGapTerm hq hq1 (CoeffPair.exponentInclusion hpq φ.val) n := by
  unfold sourceCubicActionGapTerm
  rw [sourceComplexAction_real_exponent hp hq hp1 hq1 hpq n ⟨φ.val,φ.property⟩,
    canonicalPeriodicGap_source_exponent hp hq hp1 hq1 hpq φ.val n]

namespace SourcePrimitivePowerAtlas
local instance : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩
variable {W : Set (CoeffPair 4)} (A : SourcePrimitivePowerAtlas (by simp) (by norm_num) W)
include A

/-- Cubic moments dominate the quotient series, proving convergence even near closed gaps. -/
theorem real_cubicActionGapTerm_summable (φ : realTypeSourceSubmodule 4) :
    Summable (sourceCubicActionGapTerm (by simp) (by norm_num) φ.val) := by
  apply ((A.summable_real_cubic_moments φ).div_const (Real.pi^2/4)).of_nonneg_of_le
  · exact sourceCubicActionGapTerm_nonneg (by simp) (by norm_num) φ.val
  · intro n
    apply (le_div_iff₀ (by positivity : 0 < Real.pi^2/4)).mpr
    simpa only [sourceCubicActionGapTerm,mul_comm] using A.real_action_cube_div_gap_sq_le_cubic φ n

/-- The total correction is strictly positive for every nonzero real source. -/
theorem real_cubicActionGapTerm_sum_pos_iff (φ : realTypeSourceSubmodule 4) :
    0 < (∑' n : ℤ, sourceCubicActionGapTerm (by simp) (by norm_num) φ.val n) ↔ φ ≠ 0 := by
  constructor
  · intro h hz
    have hg := (real_source_all_gaps_closed_iff_zero (by simp) (by norm_num) φ).mpr hz
    have he (n : ℤ) := sourceCubicActionGapTerm_of_collapsed (by simp) (by norm_num) φ.val n (hg n)
    simp only [he,tsum_zero,lt_self_iff_false] at h
  · intro hφ
    have hg : ¬ ∀ n, canonicalPeriodicGap (by simp) (by norm_num)
        (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n = 0 :=
      fun h => hφ ((real_source_all_gaps_closed_iff_zero (by simp) (by norm_num) φ).mp h)
    obtain ⟨n,hn⟩ := not_forall.mp hg
    exact (A.real_cubicActionGapTerm_summable φ).tsum_pos
      (sourceCubicActionGapTerm_nonneg (by simp) (by norm_num) φ.val) n
      ((sourceCubicActionGapTerm_pos_iff (by simp) (by norm_num) φ n).mpr hn)

/-- The full convergent action-gap sum supplies a quantitative lower bound for cubic moments. -/
theorem real_cubicActionGapTerm_sum_le (φ : realTypeSourceSubmodule 4) :
    (Real.pi^2/4)*(∑' n : ℤ, sourceCubicActionGapTerm (by simp) (by norm_num) φ.val n) ≤
      ∑' n : ℤ, (A.moment n 3 φ.val).re := by
  rw [← tsum_mul_left]
  exact ((A.real_cubicActionGapTerm_summable φ).mul_left _).tsum_le_tsum
    (A.real_action_cube_div_gap_sq_le_cubic φ) (A.summable_real_cubic_moments φ)

/-- A quantitative improvement of nonpositivity for the actual renormalized Hamiltonian. -/
theorem real_renormalizedHamiltonian_le_cubicActionGapBudget (φ : realTypeSourceSubmodule 4) :
    (A.renormalizedHamiltonian φ.val).re ≤
      -(Real.pi^2/3)*(∑' n : ℤ, sourceCubicActionGapTerm (by simp) (by norm_num) φ.val n) := by
  rw [A.real_renormalizedHamiltonian_eq_real_tsum φ,Complex.ofReal_re]
  nlinarith [A.real_cubicActionGapTerm_sum_le φ]

end SourcePrimitivePowerAtlas
end NLS.ZakharovShabat
