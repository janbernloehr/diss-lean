import NLS.Articles.KdVConvexity.OriginalWeightedActionSpace
import NLS.SequenceSpaces.WeightedSingle

/-! # The exact linear KdV energy on the original weighted action Banach space -/
noncomputable section
set_option autoImplicit false
open Set Complex
open scoped ENNReal
namespace NLS.Articles.KdVConvexity

def originalActionLinearSymbol (k : ℤ) : ℂ :=
  ((8*(actionIndexEquiv k : ℝ)^3*Real.pi^3 : ℝ) : ℂ)

theorem originalActionLinearSymbol_bound (k : ℤ) :
    Weight.one k * ‖originalActionLinearSymbol k‖ ≤ (8*Real.pi^3)*originalActionWeight k := by
  change 1*‖((8*(actionIndexEquiv k : ℝ)^3*Real.pi^3 : ℝ) : ℂ)‖ ≤
    (8*Real.pi^3)*(1+(actionIndexEquiv k : ℝ))^3
  rw [norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity),one_mul]
  have hp : (actionIndexEquiv k : ℝ)^3 ≤ (1+(actionIndexEquiv k : ℝ))^3 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 3
  nlinarith [mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 8*Real.pi^3)]

def originalActionLinearSequence : OriginalActionSpace →L[ℂ] Coeff 1 :=
  (WeightedCoeff.weightIsometry Weight.one 1).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (WeightedCoeff.weightedMultiplierCLM originalActionWeight Weight.one originalActionLinearSymbol
      (8*Real.pi^3) (by positivity) originalActionLinearSymbol_bound)

@[simp] theorem originalActionLinearSequence_apply (b : OriginalActionSpace) (k : ℤ) :
    originalActionLinearSequence b k=originalActionLinearSymbol k*b.val k := by
  change (Weight.one k : ℂ)*_= _
  simp only [Weight.one_apply,ofReal_one,one_mul]
  rfl

/-- The original homogeneous linear Hamiltonian coefficient, as a bounded
functional for the exact inhomogeneous norm weight (1+n)^3. -/
def originalActionLinearEnergy : OriginalActionSpace →L[ℂ] ℂ :=
  (lp.tsumCLM ℂ ℤ ℂ).comp originalActionLinearSequence

theorem summable_norm_originalActionLinearEnergy (b : OriginalActionSpace) :
    Summable (fun n : ℕ+ => ‖((8*(n : ℝ)^3*Real.pi^3 : ℝ) : ℂ)*(originalActionInclusion b) n‖) := by
  have hs := (lp.memℓp (originalActionLinearSequence b)).summable
    (by norm_num : 0 < (1 : ℝ≥0∞).toReal)
  simp only [ENNReal.toReal_one,Real.rpow_one,originalActionLinearSequence_apply] at hs
  have he (k : ℤ) : originalActionLinearSymbol k*b.val k =
      ((8*(actionIndexEquiv k : ℝ)^3*Real.pi^3 : ℝ) : ℂ)*(originalActionInclusion b) (actionIndexEquiv k) := by
    simp only [originalActionInclusion_apply,Equiv.symm_apply_apply,originalActionLinearSymbol]
  have ht := hs.congr (fun k => congrArg norm (he k))
  exact actionIndexEquiv.summable_iff.mp ht

theorem originalActionLinearEnergy_eq_tsum (b : OriginalActionSpace) :
    originalActionLinearEnergy b =
      ∑' n : ℕ+, ((8*(n : ℝ)^3*Real.pi^3 : ℝ) : ℂ)*(originalActionInclusion b) n := by
  change (∑' k : ℤ, originalActionLinearSequence b k)=_
  simp only [originalActionLinearSequence_apply]
  have he (k : ℤ) : originalActionLinearSymbol k*b.val k =
      ((8*(actionIndexEquiv k : ℝ)^3*Real.pi^3 : ℝ) : ℂ)*(originalActionInclusion b) (actionIndexEquiv k) := by
    simp only [originalActionInclusion_apply,Equiv.symm_apply_apply,originalActionLinearSymbol]
  simp_rw [he]
  exact actionIndexEquiv.tsum_eq (fun n : ℕ+ =>
    ((8*(n : ℝ)^3*Real.pi^3 : ℝ) : ℂ)*(originalActionInclusion b) n)

theorem originalActionInclusion_single (n : ℕ+) (c : ℂ) :
    originalActionInclusion (WeightedCoeff.single originalActionWeight (actionIndexEquiv.symm n) c) =
      lp.single 2 n c := by
  ext m
  simp only [originalActionInclusion_apply,WeightedCoeff.single_val,Pi.single_apply,lp.single_apply]
  simp only [Equiv.symm_apply_eq,Equiv.apply_symm_apply]

@[simp] theorem originalActionLinearEnergy_single (n : ℕ+) (c : ℂ) :
    originalActionLinearEnergy (WeightedCoeff.single originalActionWeight (actionIndexEquiv.symm n) c) =
      ((8*(n : ℝ)^3*Real.pi^3 : ℝ) : ℂ)*c := by
  rw [originalActionLinearEnergy_eq_tsum,originalActionInclusion_single]
  simp only [lp.single_apply]
  rw [tsum_eq_single n]
  · simp
  · intro m hmn
    simp [hmn]

end NLS.Articles.KdVConvexity
