import NLS.KdV.HillHalfDomainSymbol
import NLS.KdV.HillHalfDenominatorPhysical

/-! Actual half-denominator maps to the ENTIRE original H1 domain and
from the FULL original H-minus-one base, with explicit bounded inverses. -/
noncomputable section
open Set Metric
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.SmoothPeriodicTest NLS.Fourier.PeriodicFourierLebesgue

/-- The half-denominator lift into the ENTIRE original H1 domain. -/
def hillHalfToH1 (z : ℂ) : Coeff 2 →L[ℂ] FourierLebesgueSpace (2:ℝ) 1 2 :=
  (sobolevCoefficients 1 2).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((WeightedCoeff.weightIsometry (Weight.sobolev 1) 2).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
      (Coeff.multiplierCLM (hillHalfDomainSymbol z)))

/-- The half-denominator map on the ENTIRE original H-minus-one base. -/
def hillHalfFromBase (z : ℂ) : FourierLebesgueSpace (2:ℝ) (-1) 2 →L[ℂ] Coeff 2 :=
  (Coeff.multiplierCLM (hillHalfDomainSymbol z)).comp
    ((WeightedCoeff.weightIsometry (Weight.sobolev (-1)) 2).toContinuousLinearEquiv.toContinuousLinearMap.comp
      (sobolevCoefficients (-1) 2).toContinuousLinearEquiv.toContinuousLinearMap)

/-- The actual inverse half-denominator on every original H1 vector. -/
def hillRootFromH1 (z : ℂ) : FourierLebesgueSpace (2:ℝ) 1 2 →L[ℂ] Coeff 2 :=
  (Coeff.multiplierCLM (hillRootDomainSymbol z)).comp
    ((WeightedCoeff.weightIsometry (Weight.sobolev 1) 2).toContinuousLinearEquiv.toContinuousLinearMap.comp
      (sobolevCoefficients 1 2).toContinuousLinearEquiv.toContinuousLinearMap)

/-- The actual inverse base half-denominator on every full l2 input. -/
def hillRootToBase (z : ℂ) : Coeff 2 →L[ℂ] FourierLebesgueSpace (2:ℝ) (-1) 2 :=
  (sobolevCoefficients (-1) 2).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((WeightedCoeff.weightIsometry (Weight.sobolev (-1)) 2).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
      (Coeff.multiplierCLM (hillRootDomainSymbol z)))

/-- The native source half-denominator preserves each raw H1 Fourier coefficient. -/
theorem hillHalfToH1_coefficient (n : ℕ) (hn : 1 ≤ n) (z : ℂ)
    (hz : z ∈ sphere (freeHillValue n:ℂ) (n:ℝ)) (a : Coeff 2) (k : ℤ) :
    (hillHalfToH1 z a).val (mode (-k)) = hillHalfDenominatorRaw z k*a k := by
  change ((sobolevCoefficients 1 2) ((sobolevCoefficients 1 2).symm _)).val k = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  change (hillHalfDomainSymbol z k*a k)/(Weight.sobolev 1 k:ℂ) = _
  rw [hillHalfDomainSymbol_apply n hn z hz,hillHalfDomainRaw]
  calc
    _ = ((Weight.sobolev 1 k:ℂ)*(hillHalfDenominatorRaw z k*a k))/(Weight.sobolev 1 k:ℂ) := by ring
    _ = _ := mul_div_cancel_left₀ _ ((Weight.sobolev 1).complex_ne_zero k)

/-- The positive and negative native domain weights are exact reciprocals. -/
theorem hillDomain_sobolev_neg_one (k : ℤ) :
    Weight.sobolev (-1) k = (Weight.sobolev 1 k)⁻¹ := by
  simp only [Weight.sobolev_apply,Real.rpow_neg_one,Real.rpow_one]

/-- The full native base map preserves every raw original distribution coefficient. -/
theorem hillHalfFromBase_coefficient (n : ℕ) (hn : 1 ≤ n) (z : ℂ)
    (hz : z ∈ sphere (freeHillValue n:ℂ) (n:ℝ))
    (F : FourierLebesgueSpace (2:ℝ) (-1) 2) (k : ℤ) :
    hillHalfFromBase z F k = hillHalfDenominatorRaw z k*F.val (mode (-k)) := by
  change hillHalfDomainSymbol z k*((Weight.sobolev (-1) k:ℂ)*F.val (mode (-k))) = _
  rw [hillHalfDomainSymbol_apply n hn z hz,hillHalfDomainRaw,hillDomain_sobolev_neg_one,Complex.ofReal_inv]
  calc
    _ = ((Weight.sobolev 1 k:ℂ)*(hillHalfDenominatorRaw z k*F.val (mode (-k))))/(Weight.sobolev 1 k:ℂ) := by ring
    _ = _ := mul_div_cancel_left₀ _ ((Weight.sobolev 1).complex_ne_zero k)

/-- The native inverse domain map has exactly the original square-root coefficients. -/
theorem hillRootFromH1_coefficient (z : ℂ) (f : FourierLebesgueSpace (2:ℝ) 1 2) (k : ℤ) :
    hillRootFromH1 z f k = hillRootDenominatorRaw z k*f.val (mode (-k)) := by
  change hillRootDomainSymbol z k*((Weight.sobolev 1 k:ℂ)*f.val (mode (-k))) = _
  rw [hillRootDomainSymbol_apply,hillRootDomainRaw]
  calc
    _ = ((Weight.sobolev 1 k:ℂ)*(hillRootDenominatorRaw z k*f.val (mode (-k))))/(Weight.sobolev 1 k:ℂ) := by ring
    _ = _ := mul_div_cancel_left₀ _ ((Weight.sobolev 1).complex_ne_zero k)

/-- The native inverse base map has exactly the same original square-root coefficients. -/
theorem hillRootToBase_coefficient (z : ℂ) (a : Coeff 2) (k : ℤ) :
    (hillRootToBase z a).val (mode (-k)) = hillRootDenominatorRaw z k*a k := by
  change ((sobolevCoefficients (-1) 2) ((sobolevCoefficients (-1) 2).symm _)).val k = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  change (hillRootDomainSymbol z k*a k)/(Weight.sobolev (-1) k:ℂ) = _
  rw [hillRootDomainSymbol_apply,hillRootDomainRaw,hillDomain_sobolev_neg_one,Complex.ofReal_inv]
  simp only [div_eq_mul_inv,inv_inv]
  calc
    _ = ((Weight.sobolev 1 k:ℂ)*(hillRootDenominatorRaw z k*a k))/(Weight.sobolev 1 k:ℂ) := by ring
    _ = _ := mul_div_cancel_left₀ _ ((Weight.sobolev 1).complex_ne_zero k)

/-- The bounded native domain maps are exact LEFT inverses on every full l2 input. -/
theorem hillRootFromH1_halfToH1 (n : ℕ) (hn : 1 ≤ n) (z : ℂ)
    (hz : z ∈ sphere (freeHillValue n:ℂ) (n:ℝ)) (a : Coeff 2) :
    hillRootFromH1 z (hillHalfToH1 z a) = a := by
  ext k
  rw [hillRootFromH1_coefficient,hillHalfToH1_coefficient n hn z hz,← mul_assoc,
    hillRootDenominatorRaw_mul_half n hn z hz,one_mul]

/-- The bounded native domain maps are exact RIGHT inverses on the ENTIRE original H1 space. -/
theorem hillHalfToH1_rootFromH1 (n : ℕ) (hn : 1 ≤ n) (z : ℂ)
    (hz : z ∈ sphere (freeHillValue n:ℂ) (n:ℝ)) (f : FourierLebesgueSpace (2:ℝ) 1 2) :
    hillHalfToH1 z (hillRootFromH1 z f) = f := by
  apply Subtype.ext
  apply Distribution.ext_coefficients
  intro k
  rw [hillHalfToH1_coefficient n hn z hz,hillRootFromH1_coefficient,← mul_assoc,
    mul_comm (hillHalfDenominatorRaw z k),hillRootDenominatorRaw_mul_half n hn z hz,one_mul]

/-- The full native base half map is left-inverse to its actual square-root lift. -/
theorem hillHalfFromBase_rootToBase (n : ℕ) (hn : 1 ≤ n) (z : ℂ)
    (hz : z ∈ sphere (freeHillValue n:ℂ) (n:ℝ)) (a : Coeff 2) :
    hillHalfFromBase z (hillRootToBase z a) = a := by
  ext k
  rw [hillHalfFromBase_coefficient n hn z hz,hillRootToBase_coefficient,← mul_assoc,
    mul_comm (hillHalfDenominatorRaw z k),hillRootDenominatorRaw_mul_half n hn z hz,one_mul]

/-- The full native base half map is right-inverse on EVERY original H-minus-one datum. -/
theorem hillRootToBase_halfFromBase (n : ℕ) (hn : 1 ≤ n) (z : ℂ)
    (hz : z ∈ sphere (freeHillValue n:ℂ) (n:ℝ)) (F : FourierLebesgueSpace (2:ℝ) (-1) 2) :
    hillRootToBase z (hillHalfFromBase z F) = F := by
  apply Subtype.ext
  apply Distribution.ext_coefficients
  intro k
  rw [hillRootToBase_coefficient,hillHalfFromBase_coefficient n hn z hz,← mul_assoc,
    hillRootDenominatorRaw_mul_half n hn z hz,one_mul]

/-- The actual full-domain lift has the proved derivative-weighted norm bound. -/
theorem norm_hillHalfToH1_le (n : ℕ) (hn : 1 ≤ n) (z : ℂ)
    (hz : z ∈ sphere (freeHillValue n:ℂ) (n:ℝ)) : ‖hillHalfToH1 z‖ ≤ 4*Real.sqrt (n:ℝ) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro a
  change ‖(sobolevCoefficients 1 2).symm
    ((WeightedCoeff.weightIsometry (Weight.sobolev 1) 2).symm
      (Coeff.multiplierCLM (hillHalfDomainSymbol z) a))‖ ≤ _
  rw [LinearIsometryEquiv.norm_map,LinearIsometryEquiv.norm_map]
  exact (Coeff.norm_multiplier_le _ a).trans
    (mul_le_mul_of_nonneg_right (norm_hillHalfDomainSymbol_le n hn z hz) (norm_nonneg a))

/-- The full native base map has exactly the same derivative-weighted bound. -/
theorem norm_hillHalfFromBase_le (n : ℕ) (hn : 1 ≤ n) (z : ℂ)
    (hz : z ∈ sphere (freeHillValue n:ℂ) (n:ℝ)) : ‖hillHalfFromBase z‖ ≤ 4*Real.sqrt (n:ℝ) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro F
  change ‖Coeff.multiplierCLM (hillHalfDomainSymbol z)
    ((WeightedCoeff.weightIsometry (Weight.sobolev (-1)) 2) (sobolevCoefficients (-1) 2 F))‖ ≤ _
  have h := Coeff.norm_multiplier_le (hillHalfDomainSymbol z)
    ((WeightedCoeff.weightIsometry (Weight.sobolev (-1)) 2) (sobolevCoefficients (-1) 2 F))
  rw [LinearIsometryEquiv.norm_map,LinearIsometryEquiv.norm_map] at h
  exact h.trans
    (mul_le_mul_of_nonneg_right (norm_hillHalfDomainSymbol_le n hn z hz) (norm_nonneg F))

end NLS.KdV
