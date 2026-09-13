import NLS.ZakharovShabat.DoubleReciprocalSums

/-!
# Frequency summation of the off-diagonal reciprocal regions

The source's two far reciprocal regions have the decay `M^(-min(1,p-1))`.
The near region has the potential-tail bound. These estimates cover every
finite `p>1`, before the remaining potential and even-vector factors are attached.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
local instance : Fact (1 ≤ p.conjExponent) := ⟨ENNReal.HolderConjugate.one_le p.conjExponent p⟩

/-- An explicit common constant for the double reciprocal region sums. -/
def doubleReciprocalSummationConstant (p : ℝ≥0∞) : ℝ :=
  (16 * (max p.toReal p.conjExponent.toReal)^2)^p.toReal

omit [Fact (1 ≤ p)] in
/-- A genuine sequence majorant proves convergence and bounds the entire nonnegative power sum. -/
theorem summable_rpow_le_of_coeff_majorant (hp : 0 < p.toReal) (f : ℤ → ℝ)
    (hf : ∀ n, 0 ≤ f n) (d : Coeff p) (hd : ∀ n, f n ≤ ‖d n‖) :
    Summable (fun n => (f n)^p.toReal) ∧ (∑' n, (f n)^p.toReal) ≤ ‖d‖^p.toReal := by
  have hpow n := Real.rpow_le_rpow (hf n) (hd n) hp.le
  have hs := (lp.memℓp d).summable hp
  have hf' := hs.of_nonneg_of_le (fun n => Real.rpow_nonneg (hf n) _) hpow
  exact ⟨hf', (hf'.tsum_le_tsum hpow hs).trans_eq (lp.norm_rpow_eq_tsum hp d).symm⟩

/-- Each far region has a convergent outer power sum with the exact source decay exponent. -/
theorem doubleReciprocalFarRow_summable_and_le (hp : p ≠ ⊤) (hp1 : 1 < p)
    (a : Coeff p) (M : ℕ) (hM : 0 < M) :
    let hq := (ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top
    Summable (fun n : ℤ => ‖doubleReciprocalFarRow hq a M n‖^p.toReal) ∧
      (∑' n : ℤ, ‖doubleReciprocalFarRow hq a M n‖^p.toReal) ≤
        doubleReciprocalSummationConstant p * ‖a‖^p.toReal / (M : ℝ)^(min 1 (p.toReal-1)) := by
  dsimp only
  have hr := one_lt_diagonalInnerExponent hp hp1
  let : Fact (1 ≤ diagonalInnerExponent p) := ⟨hr.le⟩
  obtain ⟨s, hc, hs, he⟩ := exists_diagonalInnerConjugate hp hp1
  obtain ⟨d, hd, hn⟩ := exists_doubleReciprocalFarMajorant_explicit hp hr
    (min_le_left _ _) (min_le_right _ _) hc a M hM
  have hP := ENNReal.toReal_pos (zero_lt_one.trans hp1).ne' hp
  obtain ⟨hconv, hsum⟩ := summable_rpow_le_of_coeff_majorant hP
    (fun n => ‖doubleReciprocalFarRow (hr.trans_le (min_le_right _ _)) a M n‖)
    (fun _ => norm_nonneg _) d hd
  refine ⟨hconv, hsum.trans ?_⟩
  have hs0 := hc.pos.le
  have hn' : ‖d‖ ≤ 16 * (max p.toReal p.conjExponent.toReal)^2 * ‖a‖ * (M : ℝ)^(-(1/s)) := by
    apply hn.trans
    gcongr
  calc
    _ ≤ (16 * (max p.toReal p.conjExponent.toReal)^2 * ‖a‖ * (M : ℝ)^(-(1/s)))^p.toReal :=
      Real.rpow_le_rpow (norm_nonneg _) hn' hP.le
    _ = _ := by
      rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) (norm_nonneg _),
        ← Real.rpow_mul (Nat.cast_nonneg M)]
      have hexp : -(1/s)*p.toReal = -(min 1 (p.toReal-1)) := by rw [← he]; ring
      rw [hexp, Real.rpow_neg (Nat.cast_nonneg M), div_eq_mul_inv]
      rfl

/-- The near reciprocal region has a convergent power sum bounded by the actual potential tail. -/
theorem doubleReciprocalNearRow_summable_and_le (hp : p ≠ ⊤) (hp1 : 1 < p)
    (a : Coeff p) (N : ℕ) :
    let hq := (ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top
    Summable (fun n : ℤ => ‖doubleReciprocalNearRow hq a N n‖^p.toReal) ∧
      (∑' n : ℤ, ‖doubleReciprocalNearRow hq a N n‖^p.toReal) ≤
        doubleReciprocalSummationConstant p * ‖Coeff.fourierTail N a‖^p.toReal := by
  dsimp only
  have hr := one_lt_diagonalInnerExponent hp hp1
  let : Fact (1 ≤ diagonalInnerExponent p) := ⟨hr.le⟩
  obtain ⟨s, hc, hs, _⟩ := exists_diagonalInnerConjugate hp hp1
  obtain ⟨d, hd, hn⟩ := exists_doubleReciprocalNearMajorant_explicit hp hr
    (min_le_left _ _) (min_le_right _ _) hc a N
  have hP := ENNReal.toReal_pos (zero_lt_one.trans hp1).ne' hp
  obtain ⟨hconv, hsum⟩ := summable_rpow_le_of_coeff_majorant hP
    (fun n => ‖doubleReciprocalNearRow (hr.trans_le (min_le_right _ _)) a N n‖)
    (fun _ => norm_nonneg _) d hd
  refine ⟨hconv, hsum.trans ?_⟩
  have hs0 := hc.pos.le
  have hn' : ‖d‖ ≤ 16 * (max p.toReal p.conjExponent.toReal)^2 * ‖Coeff.fourierTail N a‖ := by
    apply hn.trans
    gcongr
  calc
    _ ≤ (16 * (max p.toReal p.conjExponent.toReal)^2 * ‖Coeff.fourierTail N a‖)^p.toReal :=
      Real.rpow_le_rpow (norm_nonneg _) hn' hP.le
    _ = _ := Real.mul_rpow (by positivity) (norm_nonneg _)

end NLS.ZakharovShabat
