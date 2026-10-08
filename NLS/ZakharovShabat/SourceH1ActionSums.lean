import NLS.ZakharovShabat.SourceActionSobolevUpperBound
import NLS.ZakharovShabat.SourceMassActionDifferential
import NLS.ZakharovShabat.SourceSobolevEnergyCoercivity

/-! # Real action sums and physical mass at H¹ regularity -/
noncomputable section
namespace NLS.ZakharovShabat

/-- The original real Hilbert source of a real H¹ potential. -/
def sourceH1RealSource (a : realTypeSobolevSourceLocus) : realTypeSourceSubmodule 2 :=
  ⟨sobolevSourceInclusion a.val,a.property⟩

/-- Exact bracket-weighted action series at H¹ regularity. -/
theorem sourceH1_weightedActions_summable (a : realTypeSobolevSourceLocus) :
    Summable (sourceWeightedActionTerm (sourceH1RealSource a) 1) := by
  let b : realTypeHigherSobolevSourceLocus 1 := ⟨higherSobolevSourceOneEquiv a.val, by
    change IsRealType (CoeffPair.toMax 2 (higherSobolevSourceInclusion 1 (higherSobolevSourceOneEquiv a.val)))
    rw [higherSobolevSourceInclusion_one]
    exact a.property⟩
  have he : (⟨higherSobolevSourceInclusion 1 b.val,b.property⟩ : realTypeSourceSubmodule 2) =
      sourceH1RealSource a := by
    apply Subtype.ext
    exact higherSobolevSourceInclusion_one a.val
  simpa only [he] using sourceWeightedAction_summable_on_Hm 1 le_rfl b

/-- The unweighted absolute action sum is the physical mass. -/
theorem sourceH1_sum_actions_eq_mass (a : realTypeSobolevSourceLocus) :
    (∑' n : ℤ, sourceWeightedActionTerm (sourceH1RealSource a) 0 n) =
      (periodOneSobolevMass a.val).re := by
  simp only [sourceWeightedActionTerm, Nat.mul_zero, pow_zero, one_mul, norm_sourceRealAction]
  rw [sourceHilbert_sum_actions_eq_half_norm_sq, periodOneSobolevMass_eq_sourceHilbertMass,
    sourceHilbertMass_eq_half_norm_sq_of_realType _ a.property, Complex.ofReal_re]
  rfl

/-- The real part of the kinetic action is the literal nonnegative weighted real action. -/
theorem sourceSobolevWeightedAction_re (a : realTypeSobolevSourceLocus) (n : ℤ) :
    (sourceSobolevWeightedAction a.val n).re = (2*Real.pi*(n:ℝ))^2*
      (sourceRealAction (by simp) (by norm_num) (sourceH1RealSource a).val
        (sourceH1RealSource a).property n).re := by
  rw [sourceSobolevWeightedAction, sourceComplexAction_eq_sourceRealAction _ _ _ _ a.property]
  have he : (2*(Real.pi:ℂ)*n)^2 = (((2*Real.pi*(n:ℝ))^2:ℝ):ℂ) := by push_cast; rfl
  rw [he]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rfl

/-- Adding mass to kinetic actions is bounded by the bracket-weighted action norm. -/
theorem sourceH1_kinetic_actions_add_mass_le (a : realTypeSobolevSourceLocus) :
    (∑' n : ℤ, (sourceSobolevWeightedAction a.val n).re)+(periodOneSobolevMass a.val).re ≤
      ∑' n : ℤ, sourceWeightedActionTerm (sourceH1RealSource a) 1 n := by
  have hK : Summable (fun n : ℤ => (sourceSobolevWeightedAction a.val n).re) :=
    Complex.reCLM.summable (summable_norm_sourceSobolevWeightedAction a.val a.property).of_norm
  have hI := sourceRealActions_summable (sourceH1RealSource a)
  have hW := sourceH1_weightedActions_summable a
  have hm : (periodOneSobolevMass a.val).re =
      ∑' n : ℤ, (sourceRealAction (by simp) (by norm_num) (sourceH1RealSource a).val
        (sourceH1RealSource a).property n).re := by
    rw [← sourceH1_sum_actions_eq_mass]
    simp only [sourceWeightedActionTerm, Nat.mul_zero, pow_zero, one_mul, norm_sourceRealAction]
  rw [hm, ← hK.tsum_add hI]
  apply (hK.add hI).tsum_le_tsum _ hW
  intro n
  rw [sourceSobolevWeightedAction_re, sourceWeightedActionTerm, norm_sourceRealAction]
  have hpos := (sourceRealAction_nonneg_and_eq_zero_iff_gap_zero (by simp) (by norm_num)
    (sourceH1RealSource a).val (sourceH1RealSource a).property n).1
  have he : |((2*n:ℤ):ℝ)*Real.pi| = |2*Real.pi*(n:ℝ)| := by
    congr 1
    push_cast
    ring
  rw [he]
  have ht : 1+(2*Real.pi*(n:ℝ))^2 ≤ (1+|2*Real.pi*(n:ℝ)|)^2 := by
    nlinarith [abs_nonneg (2*Real.pi*(n:ℝ)), sq_abs (2*Real.pi*(n:ℝ))]
  have hh := mul_le_mul_of_nonneg_right ht hpos
  norm_num only [Nat.mul_one] 
  nlinarith

end NLS.ZakharovShabat
