import NLS.ZakharovShabat.SourcePrimitivePowerPositive
import Mathlib.MeasureTheory.Integral.IntervalIntegral.MeanValue

/-! # Real higher-level actions from Section 24

Index `k` denotes the dissertation's level `k+1`: the integrand is the
spectral variable to power `k` times the arcosh gap profile. These are
spectrally weighted actions, not powers of the Abelian primitive.
-/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The real gap representation of the level `k+1` action, in cosine coordinates. -/
def sourceRealHigherAction (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (n : ℤ) (k : ℕ) : ℝ :=
  (canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n).re / Real.pi *
    ∫ θ in (0 : ℝ)..Real.pi, (realGapAffinePoint hp hp1 φ.val n (Real.cos θ))^k *
      (Real.sin θ * sourceRealGapCosineProfile hp hp1 φ.val n θ)

/-- At level one the real gap formula is the original contour-defined action. -/
@[simp] theorem sourceRealHigherAction_zero (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (n : ℤ) :
    sourceRealHigherAction hp hp1 φ n 0 = (sourceRealAction hp hp1 φ.val φ.property n).re := by
  obtain ⟨W,_,_,⟨A⟩⟩ := exists_sourcePrimitivePowerAtlas hp hp1
  have he := A.real_odd_moment_eq_cosineIntegral φ n 0
  rw [show 2*0+1 = 1 from rfl,A.moment_one n (A.realType_subset_domain φ.property),
    sourceComplexAction_eq_sourceRealAction hp hp1 n φ.val φ.property] at he
  have hr := congrArg Complex.re he
  simpa only [sourceRealHigherAction,pow_zero,one_mul,pow_one,ofReal_re] using hr.symm

/-- Collapsed gaps contribute zero at every level. -/
theorem sourceRealHigherAction_of_collapsed (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (n : ℤ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n = 0)
    (k : ℕ) : sourceRealHigherAction hp hp1 φ n k = 0 := by
  simp only [sourceRealHigherAction,hgap,zero_re,zero_div,zero_mul]

/-- The mean-value comparison (5.6), in fact valid at every natural spectral power.
It includes collapsed gaps and does not divide by the ordinary action. -/
theorem sourceRealHigherAction_eq_power_mul_action (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (n : ℤ) (k : ℕ) :
    ∃ ζ ∈ Icc
      (canonicalPeriodicLeft hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n).re
      (canonicalPeriodicRight hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n).re,
      sourceRealHigherAction hp hp1 φ n k = ζ^k * (sourceRealAction hp hp1 φ.val φ.property n).re := by
  have hc : Continuous (fun θ => (realGapAffinePoint hp hp1 φ.val n (Real.cos θ))^k) := by
    unfold realGapAffinePoint
    fun_prop
  have hg := Real.continuous_sin.mul (sourceRealGapCosineProfile_continuous hp hp1 φ n)
  have hnonneg : ∀ θ ∈ uIoc (0 : ℝ) Real.pi,
      0 ≤ Real.sin θ * sourceRealGapCosineProfile hp hp1 φ.val n θ := by
    intro θ hθ
    rw [uIoc_of_le Real.pi_pos.le] at hθ
    exact mul_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hθ.1.le hθ.2)
      (sourceRealGapCosineProfile_nonneg hp hp1 φ n θ)
  obtain ⟨θ,_,he⟩ := exists_eq_const_mul_intervalIntegral_of_nonneg (μ := MeasureTheory.volume) hc.continuousOn
    (hg.intervalIntegrable 0 Real.pi) hnonneg
  refine ⟨realGapAffinePoint hp hp1 φ.val n (Real.cos θ),realGapAffinePoint_cos_mem_Icc hp hp1 φ n θ,?_⟩
  rw [← sourceRealHigherAction_zero hp hp1 φ n]
  simp only [sourceRealHigherAction,pow_zero,one_mul]
  simp only [Pi.mul_apply] at he
  rw [he]
  ring

/-- Every odd-level action is nonnegative. -/
theorem sourceRealHigherAction_even_nonneg (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (n : ℤ) (m : ℕ) :
    0 ≤ sourceRealHigherAction hp hp1 φ n (2*m) := by
  obtain ⟨ζ,_,he⟩ := sourceRealHigherAction_eq_power_mul_action hp hp1 φ n (2*m)
  rw [he]
  exact mul_nonneg (by rw [pow_mul]; exact pow_nonneg (sq_nonneg ζ) m)
    (sourceRealAction_nonneg_and_eq_zero_iff_gap_zero hp hp1 φ.val φ.property n).1

/-- Any pointwise spectral-power bounds on the closed gap transfer to its higher action. -/
theorem sourceRealHigherAction_bounds (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (n : ℤ) (k : ℕ) (a b : ℝ)
    (hbound : ∀ ζ ∈ Icc
      (canonicalPeriodicLeft hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n).re
      (canonicalPeriodicRight hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n).re,
      a ≤ ζ^k ∧ ζ^k ≤ b) :
    a * (sourceRealAction hp hp1 φ.val φ.property n).re ≤ sourceRealHigherAction hp hp1 φ n k ∧
      sourceRealHigherAction hp hp1 φ n k ≤ b * (sourceRealAction hp hp1 φ.val φ.property n).re := by
  obtain ⟨ζ,hζ,he⟩ := sourceRealHigherAction_eq_power_mul_action hp hp1 φ n k
  have hI := (sourceRealAction_nonneg_and_eq_zero_iff_gap_zero hp hp1 φ.val φ.property n).1
  rw [he]
  exact ⟨mul_le_mul_of_nonneg_right (hbound ζ hζ).1 hI,
    mul_le_mul_of_nonneg_right (hbound ζ hζ).2 hI⟩

end NLS.ZakharovShabat
