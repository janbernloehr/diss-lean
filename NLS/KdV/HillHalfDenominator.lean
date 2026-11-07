import NLS.KdV.HillSourceReciprocal
import NLS.SequenceSpaces.LocallyBoundedRealization
import NLS.SequenceSpaces.Multiplier

/-! Actual half-denominator Fourier symbols on the literal source circles.
Both resonances are retained. The square-summable symbol has logarithmic
norm-square decay; its supremum has exact inverse-square-root-index decay. -/
noncomputable section
open Set Metric
open scoped ENNReal
namespace NLS.KdV

/-- The raw source half-denominator, without a complex square-root branch. -/
def hillHalfDenominatorRaw (z : ℂ) (k : ℤ) : ℂ :=
  ((Real.sqrt ‖z-(freeHillValue k:ℂ)‖)⁻¹:ℝ)

/-- Its squared modulus is exactly the full original reciprocal denominator. -/
theorem norm_sq_hillHalfDenominatorRaw (z : ℂ) (k : ℤ) :
    ‖hillHalfDenominatorRaw z k‖^2 = ‖z-(freeHillValue k:ℂ)‖⁻¹ := by
  simp only [hillHalfDenominatorRaw,Complex.norm_real,Real.norm_eq_abs,abs_inv,
    abs_of_nonneg (Real.sqrt_nonneg _),inv_pow,Real.sq_sqrt (norm_nonneg _)]

/-- The actual raw symbol belongs to l2 on every original source circle. -/
theorem memlp_hillHalfDenominatorRaw (n : ℕ) (hn : 1 ≤ n) (z : ℂ)
    (hz : z ∈ sphere (freeHillValue n:ℂ) (n:ℝ)) : Memℓp (hillHalfDenominatorRaw z) 2 := by
  rw [memℓp_gen_iff (by norm_num : 0 < (2:ℝ≥0∞).toReal)]
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two,norm_sq_hillHalfDenominatorRaw] using
    summable_freeHillSourceCircle_reciprocal n hn z hz

/-- A total family; the source-circle theorem recovers every actual coefficient. -/
def hillHalfDenominatorSymbol (z : ℂ) : Coeff 2 := Coeff.ofFunctionOrZero 2 (hillHalfDenominatorRaw z)

/-- Every raw half-denominator is retained on the full source circle. -/
theorem hillHalfDenominatorSymbol_apply (n : ℕ) (hn : 1 ≤ n) (z : ℂ)
    (hz : z ∈ sphere (freeHillValue n:ℂ) (n:ℝ)) (k : ℤ) :
    hillHalfDenominatorSymbol z k = hillHalfDenominatorRaw z k :=
  Coeff.ofFunctionOrZero_apply_of_mem 2 _ (memlp_hillHalfDenominatorRaw n hn z hz) k

/-- Exact norm-square sum of all original half-denominator modes. -/
theorem norm_sq_hillHalfDenominatorSymbol (n : ℕ) (hn : 1 ≤ n) (z : ℂ)
    (hz : z ∈ sphere (freeHillValue n:ℂ) (n:ℝ)) :
    ‖hillHalfDenominatorSymbol z‖^2 = ∑' k : ℤ, ‖z-(freeHillValue k:ℂ)‖⁻¹ := by
  have hs := lp.hasSum_norm (p := 2) (by norm_num) (hillHalfDenominatorSymbol z)
  simp only [ENNReal.toReal_ofNat,Real.rpow_two,hillHalfDenominatorSymbol_apply n hn z hz,
    norm_sq_hillHalfDenominatorRaw] at hs
  exact hs.tsum_eq.symm

/-- The logarithmic factor needed for the physical continuous-output half-resolvent. -/
theorem norm_sq_hillHalfDenominatorSymbol_le_log (n : ℕ) (hn : 1 ≤ n)
    (hlog : 1 < Real.log (n:ℝ)) (z : ℂ)
    (hz : z ∈ sphere (freeHillValue n:ℂ) (n:ℝ)) :
    ‖hillHalfDenominatorSymbol z‖^2 ≤ (8*Real.exp 1+2)*Real.log (n:ℝ)/(n:ℝ) := by
  rw [norm_sq_hillHalfDenominatorSymbol n hn z hz]
  exact tsum_freeHillSourceCircle_reciprocal_le_log n hn hlog z hz

/-- Every single half-denominator has the exact n^(-1/2) bound. -/
theorem norm_hillHalfDenominatorRaw_le (n : ℕ) (hn : 1 ≤ n) (z : ℂ)
    (hz : z ∈ sphere (freeHillValue n:ℂ) (n:ℝ)) (k : ℤ) :
    ‖hillHalfDenominatorRaw z k‖ ≤ (Real.sqrt (n:ℝ))⁻¹ := by
  simp only [hillHalfDenominatorRaw,Complex.norm_real,Real.norm_eq_abs,abs_inv,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  apply inv_anti₀ (Real.sqrt_pos.mpr (by exact_mod_cast hn))
  exact Real.sqrt_le_sqrt (freeHillSourceCircle_denominator_ge n hn z hz k)

/-- The SAME actual half-denominators as a bounded Fourier symbol. -/
def hillHalfDenominatorBoundedSymbol (z : ℂ) : Coeff ⊤ :=
  Coeff.ofFunctionOrZero ⊤ (hillHalfDenominatorRaw z)

/-- Full agreement of the bounded symbol with the original raw denominator. -/
theorem hillHalfDenominatorBoundedSymbol_apply (n : ℕ) (hn : 1 ≤ n) (z : ℂ)
    (hz : z ∈ sphere (freeHillValue n:ℂ) (n:ℝ)) (k : ℤ) :
    hillHalfDenominatorBoundedSymbol z k = hillHalfDenominatorRaw z k := by
  apply Coeff.ofFunctionOrZero_apply_of_mem
  exact memℓp_infty ⟨(Real.sqrt (n:ℝ))⁻¹,by
    rintro _ ⟨j,rfl⟩
    exact norm_hillHalfDenominatorRaw_le n hn z hz j⟩

/-- Its exact source supremum bound, uniform on the entire literal source circle. -/
theorem norm_hillHalfDenominatorBoundedSymbol_le (n : ℕ) (hn : 1 ≤ n) (z : ℂ)
    (hz : z ∈ sphere (freeHillValue n:ℂ) (n:ℝ)) :
    ‖hillHalfDenominatorBoundedSymbol z‖ ≤ (Real.sqrt (n:ℝ))⁻¹ := by
  apply lp.norm_le_of_forall_le (by positivity)
  intro k
  rw [hillHalfDenominatorBoundedSymbol_apply n hn z hz]
  exact norm_hillHalfDenominatorRaw_le n hn z hz k

end NLS.KdV
