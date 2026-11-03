import NLS.KdV.HillWeightedReciprocal

/-! Original H1/base normalized half-denominator symbols, retaining every
original mode. Their inverse symbols grow by exactly one derivative. -/
noncomputable section
open Set Metric
open scoped ENNReal
namespace NLS.KdV

/-- The original H1-normalized inverse square-root denominator. -/
def hillHalfDomainRaw (z : ℂ) (k : ℤ) : ℂ :=
  (Weight.sobolev 1 k:ℂ)*hillHalfDenominatorRaw z k

/-- Exact derivative-weighted source-circle bound for the actual raw symbol. -/
theorem norm_hillHalfDomainRaw_le (n : ℕ) (hn : 1 ≤ n) (z : ℂ)
    (hz : z ∈ sphere (freeHillValue n:ℂ) (n:ℝ)) (k : ℤ) :
    ‖hillHalfDomainRaw z k‖ ≤ 4*Real.sqrt (n:ℝ) := by
  have h := freeHillSourceCircle_weighted_reciprocal_le 1 (by norm_num) le_rfl n hn z hz k
  norm_num only [mul_one,sub_self,add_zero,one_mul,show (2:ℝ)-1=1 by norm_num,Real.rpow_one] at h
  have he : ‖hillHalfDomainRaw z k‖^2 =
      (Weight.sobolev 1 k)^2*‖z-(freeHillValue k:ℂ)‖⁻¹ := by
    simp only [hillHalfDomainRaw,norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos ((Weight.sobolev 1).positive k),mul_pow,norm_sq_hillHalfDenominatorRaw]
  have hs := Real.sq_sqrt (Nat.cast_nonneg n)
  have hs0 := Real.sqrt_nonneg (n:ℝ)
  rw [← he] at h
  nlinarith [norm_nonneg (hillHalfDomainRaw z k)]

/-- A total coefficient family, with every source-circle coefficient recovered below. -/
def hillHalfDomainSymbol (z : ℂ) : Coeff ⊤ := Coeff.ofFunctionOrZero ⊤ (hillHalfDomainRaw z)

/-- No original H1-normalized source coefficient is lost. -/
theorem hillHalfDomainSymbol_apply (n : ℕ) (hn : 1 ≤ n) (z : ℂ)
    (hz : z ∈ sphere (freeHillValue n:ℂ) (n:ℝ)) (k : ℤ) :
    hillHalfDomainSymbol z k = hillHalfDomainRaw z k := by
  apply Coeff.ofFunctionOrZero_apply_of_mem
  exact memℓp_infty ⟨4*Real.sqrt (n:ℝ),by rintro _ ⟨j,rfl⟩;exact norm_hillHalfDomainRaw_le n hn z hz j⟩

/-- The original domain/base half maps have a genuine derivative norm bound. -/
theorem norm_hillHalfDomainSymbol_le (n : ℕ) (hn : 1 ≤ n) (z : ℂ)
    (hz : z ∈ sphere (freeHillValue n:ℂ) (n:ℝ)) :
    ‖hillHalfDomainSymbol z‖ ≤ 4*Real.sqrt (n:ℝ) := by
  apply lp.norm_le_of_forall_le (by positivity)
  intro k
  rw [hillHalfDomainSymbol_apply n hn z hz]
  exact norm_hillHalfDomainRaw_le n hn z hz k

/-- The actual positive square-root denominator. -/
def hillRootDenominatorRaw (z : ℂ) (k : ℤ) : ℂ := Real.sqrt ‖z-(freeHillValue k:ℂ)‖

/-- The square-root and inverse square-root cancel at EVERY original mode
on the entire literal source circle. -/
theorem hillRootDenominatorRaw_mul_half (n : ℕ) (hn : 1 ≤ n) (z : ℂ)
    (hz : z ∈ sphere (freeHillValue n:ℂ) (n:ℝ)) (k : ℤ) :
    hillRootDenominatorRaw z k*hillHalfDenominatorRaw z k = 1 := by
  have hd : 0 < ‖z-(freeHillValue k:ℂ)‖ :=
    (by exact_mod_cast hn : (0:ℝ) < n).trans_le (freeHillSourceCircle_denominator_ge n hn z hz k)
  have hs : Real.sqrt ‖z-(freeHillValue k:ℂ)‖ ≠ 0 := (Real.sqrt_pos.mpr hd).ne'
  simp only [hillRootDenominatorRaw,hillHalfDenominatorRaw,Complex.ofReal_inv]
  exact mul_inv_cancel₀ (by exact_mod_cast hs)

/-- The exact scalar upper bound needed for the inverse derivative maps. -/
theorem hillRootDenominatorRaw_le_weight (z : ℂ) (k : ℤ) :
    ‖hillRootDenominatorRaw z k‖ ≤ (1+‖z‖+Real.pi^2)*Weight.sobolev 1 k := by
  have hk : (k:ℝ)^2 ≤ (1+|(k:ℝ)|)^2 := by nlinarith [sq_abs (k:ℝ),abs_nonneg (k:ℝ)]
  have hw : 1 ≤ (1+|(k:ℝ)|)^2 := by nlinarith [abs_nonneg (k:ℝ)]
  have hd : ‖z-(freeHillValue k:ℂ)‖ ≤ (1+‖z‖+Real.pi^2)*(1+|(k:ℝ)|)^2 := by
    have ht := norm_sub_le z (freeHillValue k:ℂ)
    have hn : ‖(freeHillValue k:ℂ)‖ = Real.pi^2*(k:ℝ)^2 := by
      rw [Complex.norm_real,Real.norm_eq_abs,freeHillValue]
      exact abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    rw [hn] at ht
    have hs := mul_le_mul_of_nonneg_left hk (sq_nonneg Real.pi)
    have hz := mul_le_mul_of_nonneg_left hw (norm_nonneg z)
    nlinarith
  have hC : 1 ≤ 1+‖z‖+Real.pi^2 := by nlinarith [norm_nonneg z,sq_nonneg Real.pi]
  have hC2 : 1+‖z‖+Real.pi^2 ≤ (1+‖z‖+Real.pi^2)^2 := by nlinarith
  have hbig := mul_le_mul_of_nonneg_right hC2 (sq_nonneg (1+|(k:ℝ)|))
  simp only [hillRootDenominatorRaw,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _),Weight.sobolev_apply,Real.rpow_one]
  apply (Real.sqrt_le_iff).mpr
  refine ⟨by positivity,?_⟩
  rw [mul_pow]
  exact hd.trans hbig

/-- The inverse domain/base multiplier, normalized by the original H1 weight. -/
def hillRootDomainRaw (z : ℂ) (k : ℤ) : ℂ := hillRootDenominatorRaw z k/(Weight.sobolev 1 k:ℂ)

/-- The inverse normalized symbol is bounded at EVERY parameter, not only on source circles. -/
theorem norm_hillRootDomainRaw_le (z : ℂ) (k : ℤ) :
    ‖hillRootDomainRaw z k‖ ≤ 1+‖z‖+Real.pi^2 := by
  rw [hillRootDomainRaw,norm_div,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos ((Weight.sobolev 1).positive k)]
  exact (div_le_iff₀ ((Weight.sobolev 1).positive k)).mpr (hillRootDenominatorRaw_le_weight z k)

/-- A bounded inverse normalized square-root family with all original coefficients. -/
def hillRootDomainSymbol (z : ℂ) : Coeff ⊤ := Coeff.ofFunctionOrZero ⊤ (hillRootDomainRaw z)

/-- Every inverse normalized coefficient is recovered at every complex parameter. -/
theorem hillRootDomainSymbol_apply (z : ℂ) (k : ℤ) : hillRootDomainSymbol z k = hillRootDomainRaw z k := by
  apply Coeff.ofFunctionOrZero_apply_of_mem
  exact memℓp_infty ⟨1+‖z‖+Real.pi^2,by rintro _ ⟨j,rfl⟩;exact norm_hillRootDomainRaw_le z j⟩

/-- The exact normalized symbols multiply to one on the full original source circle. -/
theorem hillHalfDomainSymbol_mul_root (n : ℕ) (hn : 1 ≤ n) (z : ℂ)
    (hz : z ∈ sphere (freeHillValue n:ℂ) (n:ℝ)) (k : ℤ) :
    hillHalfDomainSymbol z k*hillRootDomainSymbol z k = 1 := by
  rw [hillHalfDomainSymbol_apply n hn z hz,hillRootDomainSymbol_apply,hillHalfDomainRaw,hillRootDomainRaw]
  calc
    _ = hillRootDenominatorRaw z k*hillHalfDenominatorRaw z k := by
      calc
        _ = ((Weight.sobolev 1 k:ℂ)*(hillRootDenominatorRaw z k*hillHalfDenominatorRaw z k))/(Weight.sobolev 1 k:ℂ) := by ring
        _ = _ := mul_div_cancel_left₀ _ ((Weight.sobolev 1).complex_ne_zero k)
    _ = 1 := hillRootDenominatorRaw_mul_half n hn z hz k

end NLS.KdV
