import NLS.ZakharovShabat.SourceM1WeightedActionEstimate
import NLS.ZakharovShabat.M1ComplexGlobalGapEstimate
import NLS.ZakharovShabat.SourceNormalizedActionRootAnalytic

/-! # Complex weighted actions controlled by their normalized factors -/
noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Exact factorization gives a gap-square majorant, including collapsed gaps. -/
theorem sourceComplexAction_le_gap_sq_of_normalized_bound (ψ : CoeffPair 2) (K : ℝ)
    (hf : ∀ n : ℤ, sourceComplexAction (by simp) (by norm_num) n ψ =
      (sourcePeriodicGapDisplacement (by simp) (by norm_num) ψ n)^2 *
        sourceNormalizedActionComplexExtension (by simp) (by norm_num) n ψ)
    (hb : ∀ n : ℤ, ‖sourceNormalizedActionComplexExtension (by simp) (by norm_num) n ψ‖ ≤ K)
    (n : ℤ) :
    ‖sourceComplexAction (by simp) (by norm_num) n ψ‖ ≤
      K*‖sourcePeriodicGapDisplacement (by simp) (by norm_num) ψ n‖^2 := by
  rw [hf n,norm_mul,norm_pow,mul_comm]
  exact mul_le_mul_of_nonneg_right (hb n) (sq_nonneg _)

/-- A uniform action-gap bound yields the complex M₁ action budget. -/
theorem sourceM1_complex_actions_summable_and_le (w : SpectralWeight) (hw : w.HasLinearFactor)
    (a : CoeffPair 2)
    (ha : normalizedWeightedSource w a ∈ sourceSpectralStripNeighborhood (by simp))
    (K : ℝ) (hK : 0 ≤ K)
    (hb : ∀ n : ℤ, ‖sourceComplexAction (by simp) (by norm_num) n (normalizedWeightedSource w a)‖ ≤
      K*‖sourcePeriodicGapDisplacement (by simp) (by norm_num) (normalizedWeightedSource w a) n‖^2) :
    Summable (sourceM1ActionTerm w (normalizedWeightedSource w a)) ∧
    (∑' n : ℤ, sourceM1ActionTerm w (normalizedWeightedSource w a) n) ≤
      K*(265*Real.pi^2*(w.realExtension (16*‖a‖^2))^2*(1+‖a‖^2)*‖a‖^2) := by
  obtain ⟨hgs,hgb⟩ := M1_source_canonicalGap_global_summable_and_le
    (normalizedWeightedSource w a) ha w hw (normalizedWeightedPeriodOne w a)
    (weightedBaseToPair_normalizedWeightedPeriodOne w a)
  simp only [norm_normalizedWeightedPeriodOne] at hgb
  let g : ℤ → ℝ := fun n => (w (2*n)*‖canonicalPeriodicGap (by simp) (by norm_num)
    (periodOnePotential (normalizedWeightedSource w a))
    (periodOnePotential_mem (normalizedWeightedSource w a)) n‖)^2
  have hmajor (n : ℤ) : sourceM1ActionTerm w (normalizedWeightedSource w a) n ≤ K*g n := by
    have h := hb n
    rw [sourcePeriodicGapDisplacement_apply] at h
    have hh := mul_le_mul_of_nonneg_left h (sq_nonneg (w (2*n)))
    simp only [sourceM1ActionTerm,g]
    calc
      _ ≤ (w (2*n))^2*(K*‖canonicalPeriodicGap (by simp) (by norm_num)
        (periodOnePotential (normalizedWeightedSource w a))
        (periodOnePotential_mem (normalizedWeightedSource w a)) n‖^2) := hh
      _ = _ := by ring
  have hs := (hgs.mul_left K).of_nonneg_of_le
    (fun n => by unfold sourceM1ActionTerm; positivity) hmajor
  refine ⟨hs,?_⟩
  calc
    _ ≤ ∑' n, K*g n := hs.tsum_le_tsum hmajor (hgs.mul_left K)
    _ = K*(∑' n, g n) := tsum_mul_left
    _ ≤ _ := mul_le_mul_of_nonneg_left hgb hK

/-- The complex coefficient whose ℓ¹ norm is the weighted action norm. -/
def sourceM1ActionCoefficient (w : SpectralWeight) (ψ : CoeffPair 2) (n : ℤ) : ℂ :=
  (w (2*n) : ℂ)^2 * sourceComplexAction (by simp) (by norm_num) n ψ

@[simp] theorem norm_sourceM1ActionCoefficient (w : SpectralWeight) (ψ : CoeffPair 2) (n : ℤ) :
    ‖sourceM1ActionCoefficient w ψ n‖ = sourceM1ActionTerm w ψ n := by
  simp only [sourceM1ActionCoefficient,sourceM1ActionTerm,norm_mul,norm_pow,
    Complex.norm_real,Real.norm_eq_abs,sq_abs]

/-- Summability produces the actual complex ℓ¹ sequence. -/
def sourceM1ActionSequence (w : SpectralWeight) (ψ : CoeffPair 2)
    (hs : Summable (sourceM1ActionTerm w ψ)) : Coeff 1 :=
  ⟨sourceM1ActionCoefficient w ψ,by
    change Memℓp (sourceM1ActionCoefficient w ψ) 1
    rw [memℓp_gen_iff (by norm_num : 0 < (1:ℝ≥0∞).toReal)]
    simpa only [ENNReal.toReal_one,Real.rpow_one,norm_sourceM1ActionCoefficient] using hs⟩

@[simp] theorem sourceM1ActionSequence_apply (w : SpectralWeight) (ψ : CoeffPair 2)
    (hs : Summable (sourceM1ActionTerm w ψ)) (n : ℤ) :
    sourceM1ActionSequence w ψ hs n = sourceM1ActionCoefficient w ψ n := rfl

/-- Its norm is the literal absolute weighted action sum. -/
theorem sourceM1ActionSequence_norm (w : SpectralWeight) (ψ : CoeffPair 2)
    (hs : Summable (sourceM1ActionTerm w ψ)) :
    ‖sourceM1ActionSequence w ψ hs‖ = ∑' n : ℤ, sourceM1ActionTerm w ψ n := by
  rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (1:ℝ≥0∞).toReal)]
  simp only [ENNReal.toReal_one,Real.rpow_one,one_div_one,
    sourceM1ActionSequence_apply,norm_sourceM1ActionCoefficient]

end NLS.ZakharovShabat
