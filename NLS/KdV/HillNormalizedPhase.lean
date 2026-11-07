import NLS.KdV.HillHalfSandwich
import NLS.FunctionalAnalysis.NeumannCompositionBound

/-! The actual normalized free phase and its inverse on all source Fourier
modes. These are genuine coefficient Hilbert-space operators of norm at most one. -/
noncomputable section
open Set Metric
open scoped ENNReal
namespace NLS.KdV

/-- The literal source diagonal I_lambda. -/
def hillPhaseRaw (z : ℂ) (k : ℤ) : ℂ := (z-(freeHillValue k:ℂ))/(‖z-(freeHillValue k:ℂ)‖:ℂ)

/-- Its literal inverse diagonal on every nonzero source denominator. -/
def hillPhaseInverseRaw (z : ℂ) (k : ℤ) : ℂ := (‖z-(freeHillValue k:ℂ)‖:ℂ)*(z-(freeHillValue k:ℂ))⁻¹

/-- The phase symbol is bounded by one even at totalized free poles. -/
theorem norm_hillPhaseRaw_le (z : ℂ) (k : ℤ) : ‖hillPhaseRaw z k‖ ≤ 1 := by
  rw [hillPhaseRaw,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)]
  by_cases h : ‖z-(freeHillValue k:ℂ)‖ = 0
  · simp [h]
  · rw [div_self h]

/-- The inverse phase symbol has the same exact global bound. -/
theorem norm_hillPhaseInverseRaw_le (z : ℂ) (k : ℤ) : ‖hillPhaseInverseRaw z k‖ ≤ 1 := by
  rw [hillPhaseInverseRaw,norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)]
  by_cases h : ‖z-(freeHillValue k:ℂ)‖ = 0
  · simp [h]
  · rw [mul_inv_cancel₀ h]

/-- Bounded original normalized phase coefficients. -/
def hillPhaseSymbol (z : ℂ) : Coeff ⊤ := Coeff.ofFunctionOrZero ⊤ (hillPhaseRaw z)

/-- Bounded original inverse normalized phase coefficients. -/
def hillPhaseInverseSymbol (z : ℂ) : Coeff ⊤ := Coeff.ofFunctionOrZero ⊤ (hillPhaseInverseRaw z)

/-- Every original phase coefficient is retained at every parameter. -/
theorem hillPhaseSymbol_apply (z : ℂ) (k : ℤ) : hillPhaseSymbol z k = hillPhaseRaw z k := by
  apply Coeff.ofFunctionOrZero_apply_of_mem
  exact memℓp_infty ⟨1,by rintro _ ⟨j,rfl⟩;exact norm_hillPhaseRaw_le z j⟩

/-- Every inverse phase coefficient is likewise retained. -/
theorem hillPhaseInverseSymbol_apply (z : ℂ) (k : ℤ) :
    hillPhaseInverseSymbol z k = hillPhaseInverseRaw z k := by
  apply Coeff.ofFunctionOrZero_apply_of_mem
  exact memℓp_infty ⟨1,by rintro _ ⟨j,rfl⟩;exact norm_hillPhaseInverseRaw_le z j⟩

/-- The actual phase on ALL coefficient Hilbert data. -/
def hillNormalizedPhase (z : ℂ) : Coeff 2 →L[ℂ] Coeff 2 := Coeff.multiplierCLM (hillPhaseSymbol z)

/-- The actual inverse phase on the SAME full coefficient Hilbert space. -/
def hillNormalizedPhaseInverse (z : ℂ) : Coeff 2 →L[ℂ] Coeff 2 :=
  Coeff.multiplierCLM (hillPhaseInverseSymbol z)

/-- The actual phase operator has norm at most ONE. -/
theorem norm_hillNormalizedPhase_le (z : ℂ) : ‖hillNormalizedPhase z‖ ≤ 1 := by
  have hS : ‖hillPhaseSymbol z‖ ≤ 1 := by
    apply lp.norm_le_of_forall_le zero_le_one
    intro k
    rw [hillPhaseSymbol_apply]
    exact norm_hillPhaseRaw_le z k
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  exact (Coeff.norm_multiplier_le _ x).trans
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hS (norm_nonneg x))

/-- The actual inverse phase has norm at most ONE as well. -/
theorem norm_hillNormalizedPhaseInverse_le (z : ℂ) : ‖hillNormalizedPhaseInverse z‖ ≤ 1 := by
  have hS : ‖hillPhaseInverseSymbol z‖ ≤ 1 := by
    apply lp.norm_le_of_forall_le zero_le_one
    intro k
    rw [hillPhaseInverseSymbol_apply]
    exact norm_hillPhaseInverseRaw_le z k
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  exact (Coeff.norm_multiplier_le _ x).trans
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hS (norm_nonneg x))

/-- No original phase coefficient vanishes on a literal source circle. -/
theorem hillPhaseRaw_mul_inverse (n : ℕ) (hn : 1 ≤ n) (z : ℂ)
    (hz : z ∈ sphere (freeHillValue n:ℂ) (n:ℝ)) (k : ℤ) :
    hillPhaseRaw z k*hillPhaseInverseRaw z k = 1 := by
  have hd : 0 < ‖z-(freeHillValue k:ℂ)‖ :=
    (by exact_mod_cast hn : (0:ℝ) < n).trans_le (freeHillSourceCircle_denominator_ge n hn z hz k)
  have hzn : z-(freeHillValue k:ℂ) ≠ 0 := norm_ne_zero_iff.mp hd.ne'
  have hdc : (‖z-(freeHillValue k:ℂ)‖:ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  simp only [hillPhaseRaw,hillPhaseInverseRaw]
  field_simp [hdc,hzn]

/-- The actual inverse is a LEFT and RIGHT inverse on the ENTIRE Hilbert space. -/
theorem hillNormalizedPhase_inverse_spec (n : ℕ) (hn : 1 ≤ n) (z : ℂ)
    (hz : z ∈ sphere (freeHillValue n:ℂ) (n:ℝ)) :
    (hillNormalizedPhase z).comp (hillNormalizedPhaseInverse z) = ContinuousLinearMap.id ℂ (Coeff 2) ∧
    (hillNormalizedPhaseInverse z).comp (hillNormalizedPhase z) = ContinuousLinearMap.id ℂ (Coeff 2) := by
  constructor
  · apply ContinuousLinearMap.ext
    intro x
    ext k
    change hillPhaseSymbol z k*(hillPhaseInverseSymbol z k*x k) = x k
    rw [hillPhaseSymbol_apply,hillPhaseInverseSymbol_apply,← mul_assoc,hillPhaseRaw_mul_inverse n hn z hz,one_mul]
  · apply ContinuousLinearMap.ext
    intro x
    ext k
    change hillPhaseInverseSymbol z k*(hillPhaseSymbol z k*x k) = x k
    rw [hillPhaseSymbol_apply,hillPhaseInverseSymbol_apply,← mul_assoc,
      mul_comm (hillPhaseInverseRaw z k),hillPhaseRaw_mul_inverse n hn z hz,one_mul]

end NLS.KdV
