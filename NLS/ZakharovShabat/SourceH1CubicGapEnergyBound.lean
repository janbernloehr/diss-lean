import NLS.ZakharovShabat.SourceCubicActionGapBudget
import NLS.ZakharovShabat.SourceH1EndpointMomentCriterion

/-! # Retaining a quantitative cubic contribution in the H¹ energy estimate

These bounds use the original Hilbert-space actions and gaps. They strengthen
the mass budget without asserting the still unresolved unrestricted endpoint.
-/
noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
local instance : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩

/-- The actual action-gap budget at H¹ regularity. -/
def sourceH1CubicActionGapBudget (a : realTypeSobolevSourceLocus) : ℝ :=
  ∑' n : ℤ, sourceCubicActionGapTerm (by simp) (by norm_num) (sobolevSourceInclusion a.val) n

/-- Inclusion into FL⁴ leaves every quotient unchanged. -/
theorem sourceH1CubicActionGapTerm_eq_FL4 (a : realTypeSobolevSourceLocus) (n : ℤ) :
    sourceCubicActionGapTerm (by simp) (by norm_num) (sobolevSourceInclusion a.val) n =
      sourceCubicActionGapTerm (by simp) (by norm_num) (sobolevSourceFL4 a.val) n :=
  sourceCubicActionGapTerm_exponent (by simp) (by simp) (by norm_num) (by norm_num)
    (by norm_num : (2:ℝ≥0∞) ≤ 4) (sourceH1RealSource a) n

theorem sourceH1CubicActionGapTerm_summable (a : realTypeSobolevSourceLocus) :
    Summable (sourceCubicActionGapTerm (by simp) (by norm_num) (sobolevSourceInclusion a.val)) := by
  obtain ⟨W,_,_,⟨A⟩⟩ := exists_sourcePrimitivePowerAtlas (by simp : (4:ℝ≥0∞) ≠ ⊤) (by norm_num)
  exact (A.real_cubicActionGapTerm_summable
    ⟨sobolevSourceFL4 a.val,(realSobolevSourceFL4 a).property⟩).congr
      (fun n => (sourceH1CubicActionGapTerm_eq_FL4 a n).symm)

theorem sourceH1CubicActionGapBudget_nonneg (a : realTypeSobolevSourceLocus) :
    0 ≤ sourceH1CubicActionGapBudget a :=
  tsum_nonneg (sourceCubicActionGapTerm_nonneg (by simp) (by norm_num) _)

/-- The strengthened energy estimate retains kinetic slack and a convergent spectral correction. -/
theorem sourceH1_energy_le_mass_budget_sub_cubic_gap (a : realTypeSobolevSourceLocus) :
    (periodOneSobolevHamiltonian a.val).re ≤
      (∑' n : ℤ, sourceWeightedActionTerm (sourceH1RealSource a) 1 n)-
      (∑' n : ℤ, sourceWeightedActionTerm (sourceH1RealSource a) 0 n)+
      2*(∑' n : ℤ, sourceWeightedActionTerm (sourceH1RealSource a) 0 n)^2-
      sourceH1KineticActionSlack a-(Real.pi^2/3)*sourceH1CubicActionGapBudget a := by
  obtain ⟨W,_,_,⟨A⟩⟩ := exists_sourcePrimitivePowerAtlas (by simp : (4:ℝ≥0∞) ≠ ⊤) (by norm_num)
  have hb := A.real_cubicActionGapTerm_sum_le
    ⟨sobolevSourceFL4 a.val,(realSobolevSourceFL4 a).property⟩
  have he : sourceH1CubicActionGapBudget a =
      ∑' n : ℤ, sourceCubicActionGapTerm (by simp) (by norm_num) (sobolevSourceFL4 a.val) n :=
    tsum_congr (sourceH1CubicActionGapTerm_eq_FL4 a)
  rw [← he] at hb
  rw [A.sourceH1_energy_eq_mass_budget_sub_moments a]
  nlinarith

/-- Any finite set of observed gaps already gives a valid energy correction. -/
theorem sourceH1_energy_le_mass_budget_sub_finite_cubic_gap
    (a : realTypeSobolevSourceLocus) (s : Finset ℤ) :
    (periodOneSobolevHamiltonian a.val).re ≤
      (∑' n : ℤ, sourceWeightedActionTerm (sourceH1RealSource a) 1 n)-
      (∑' n : ℤ, sourceWeightedActionTerm (sourceH1RealSource a) 0 n)+
      2*(∑' n : ℤ, sourceWeightedActionTerm (sourceH1RealSource a) 0 n)^2-
      sourceH1KineticActionSlack a-(Real.pi^2/3)*
        (∑ n ∈ s, sourceCubicActionGapTerm (by simp) (by norm_num) (sobolevSourceInclusion a.val) n) := by
  have hs := (sourceH1CubicActionGapTerm_summable a).sum_le_tsum s
    (fun n _ => sourceCubicActionGapTerm_nonneg (by simp) (by norm_num) _ n)
  have h := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ Real.pi^2/3)
  have hb := sourceH1_energy_le_mass_budget_sub_cubic_gap a
  change (Real.pi^2/3)*(∑ n ∈ s, sourceCubicActionGapTerm (by simp) (by norm_num)
    (sobolevSourceInclusion a.val) n) ≤ (Real.pi^2/3)*sourceH1CubicActionGapBudget a at h
  linarith

/-- A sufficient condition for the printed endpoint expressed solely through actions and gaps. -/
theorem sourceH1_energy_le_lemma272_of_cubic_gap_budget (a : realTypeSobolevSourceLocus)
    (h : 2*(∑' n : ℤ, sourceWeightedActionTerm (sourceH1RealSource a) 0 n)^2-
        (∑' n : ℤ, sourceWeightedActionTerm (sourceH1RealSource a) 0 n)-
        (∑' n : ℤ, sourceWeightedActionTerm (sourceH1RealSource a) 1 n)-
        (∑' n : ℤ, sourceWeightedActionTerm (sourceH1RealSource a) 1 n)^2 ≤
      sourceH1KineticActionSlack a+(Real.pi^2/3)*sourceH1CubicActionGapBudget a) :
    (periodOneSobolevHamiltonian a.val).re ≤
      (∑' n : ℤ, sourceWeightedActionTerm (sourceH1RealSource a) 1 n)+
      (1+∑' n : ℤ, sourceWeightedActionTerm (sourceH1RealSource a) 1 n)*
        (∑' n : ℤ, sourceWeightedActionTerm (sourceH1RealSource a) 1 n) := by
  nlinarith [sourceH1_energy_le_mass_budget_sub_cubic_gap a]

end NLS.ZakharovShabat
