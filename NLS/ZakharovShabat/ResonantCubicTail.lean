import NLS.ZakharovShabat.ResonantCubicRemainder
import NLS.ZakharovShabat.SourceLemma6_8OffDiagonalProof

/-! # Full-strip supremum tails after cubic subtraction

For every finite p>1, the weighted error after the leading and cubic terms
has a convergent p-power tail over all distant signed strips. A small
potential gives the explicit order norm(phi)^(5p), for every cutoff N>=1.
-/
noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The first cubic operator term; true selects the positive coefficient. -/
def resonantCubicTermFunction (hp : p ≠ ⊤) (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight p)
    (n : ℤ) (positive : Bool) (z : ℂ) : ℂ :=
  if positive then weightedResonantParityTermFunction hp w φ n 2 0 1 0 z
  else weightedResonantParityTermFunction hp w φ n 2 0 0 1 z

/-- The actual coefficient after subtracting its leading and cubic terms. -/
def resonantCubicErrorFunction (hp : p ≠ ⊤) (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight p)
    (n : ℤ) (positive : Bool) (z : ℂ) : ℂ :=
  (if positive then weightedResonantBPlusExtension hp w φ n z-φ.snd.val (2*n)
   else weightedResonantBMinusExtension hp w φ n z-φ.fst.val (-(2*n))) - resonantCubicTermFunction hp w φ n positive z

/-- The weighted norm supremum of the cubic error on the whole closed strip. -/
def resonantCubicErrorSup (hp : p ≠ ⊤) (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight p)
    (n : ℤ) (positive : Bool) : ℝ := weightedStripSup w n (resonantCubicErrorFunction hp w φ n positive)

/-- The literal regional majorant with the appropriate reflected components. -/
def resonantCubicMajorant (hp : p ≠ ⊤) (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight p)
    (N : ℕ) (n : ℤ) (positive : Bool) : ℝ :=
  if positive then offDiagonalProofBound hp w φ.snd (w.reflection φ.fst) N n
  else offDiagonalProofBound hp w (w.reflection φ.fst) φ.snd N n

/-- The actual pointwise error retains a common upper bound for the square norm. -/
theorem resonantCubicErrorFunction_bound (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (N : ℕ) (n : ℤ) (hn : N ≤ n.natAbs)
    (positive : Bool) (z : ℂ) (hz : z ∈ resonantStrip n)
    (hh : ‖weightedPotentialSquareInShift hp w φ n z hz‖ ≤ 1/2)
    (Q : ℝ) (hQ : ‖weightedPotentialSquareInShift hp w φ n z hz‖ ≤ Q) :
    w (2*n)*‖resonantCubicErrorFunction hp w φ n positive z‖ ≤ Q*resonantCubicMajorant hp w φ N n positive := by
  have h : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1 := hh.trans_lt (by norm_num)
  cases positive
  · simpa only [resonantCubicErrorFunction,resonantCubicTermFunction,resonantCubicMajorant,Bool.false_eq_true,if_false,
      weightedResonantBMinusExtension_eq hp w φ n z hz h,
      weightedResonantParityTermFunction,weightedPotentialExtension_eq hp w φ n z hz,
      pow_zero,pow_two,one_apply_eq_self,mul_apply_eq_comp] using
      resonantCubic_negative_error hp hp1 w φ N n hn z hz h hh Q hQ
  · simpa only [resonantCubicErrorFunction,resonantCubicTermFunction,resonantCubicMajorant,if_true,
      weightedResonantBPlusExtension_eq hp w φ n z hz h,
      weightedResonantParityTermFunction,weightedPotentialExtension_eq hp w φ n z hz,
      pow_zero,pow_two,one_apply_eq_self,mul_apply_eq_comp] using
      resonantCubic_positive_error hp hp1 w φ N n hn z hz h hh Q hQ

/-- Actual error images are bounded and their nonnegative suprema dominate every strip value. -/
theorem resonantCubicErrorSup_bounds (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (N : ℕ) (n : ℤ) (hn : N ≤ n.natAbs)
    (positive : Bool) (Q : ℝ)
    (hh : ∀ z : ℂ, ∀ hz : z ∈ resonantStrip n,
      ‖weightedPotentialSquareInShift hp w φ n z hz‖ ≤ 1/2 ∧
      ‖weightedPotentialSquareInShift hp w φ n z hz‖ ≤ Q) :
    BddAbove ((fun z : ℂ => w (2*n)*‖resonantCubicErrorFunction hp w φ n positive z‖) '' resonantStrip n) ∧
    0 ≤ resonantCubicErrorSup hp w φ n positive ∧
    resonantCubicErrorSup hp w φ n positive ≤ Q*resonantCubicMajorant hp w φ N n positive ∧
    ∀ z ∈ resonantStrip n, w (2*n)*‖resonantCubicErrorFunction hp w φ n positive z‖ ≤ resonantCubicErrorSup hp w φ n positive := by
  have hb (z : ℂ) (hz : z ∈ resonantStrip n) :=
    resonantCubicErrorFunction_bound hp hp1 w φ N n hn positive z hz (hh z hz).1 Q (hh z hz).2
  refine ⟨⟨Q*resonantCubicMajorant hp w φ N n positive,?_⟩,?_⟩
  · rintro _ ⟨z,hz,rfl⟩
    exact hb z hz
  · exact weightedStripSup_bounds w n _ _ hb

/-- Domination by a scaled regional majorant gives a convergent p-power tail. -/
theorem resonantCubic_scaled_dominated_tail (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (d a : WeightedCoeff w.toWeight p) (N : ℕ) (hN : 0 < N) (Q : ℝ) (hQ : 0 ≤ Q)
    (S : ℤ → ℝ) (hb : ∀ n : ℤ, N ≤ n.natAbs →
      0 ≤ S n ∧ S n ≤ Q*offDiagonalProofBound hp w d a N n) :
    Summable (sourceCoefficientPowerTail p N S) ∧
    (∑' n : ℤ, sourceCoefficientPowerTail p N S n) ≤
      Q^p.toReal*(∑' n : ℤ, (offDiagonalProofBound hp w d a N n)^p.toReal) := by
  have hs := ((offDiagonalProofBound_summable_and_le hp hp1 w d a N hN).1).mul_left (Q^p.toReal)
  have hnon (n : ℤ) : 0 ≤ sourceCoefficientPowerTail p N S n := by
    unfold sourceCoefficientPowerTail
    split_ifs with hn
    · exact Real.rpow_nonneg (hb n hn).1 _
    · exact le_rfl
  have hdom (n : ℤ) : sourceCoefficientPowerTail p N S n ≤
      Q^p.toReal*(offDiagonalProofBound hp w d a N n)^p.toReal := by
    unfold sourceCoefficientPowerTail
    split_ifs with hn
    · calc
        _ ≤ (Q*offDiagonalProofBound hp w d a N n)^p.toReal :=
          Real.rpow_le_rpow (hb n hn).1 (hb n hn).2 ENNReal.toReal_nonneg
        _ = _ := Real.mul_rpow hQ (offDiagonalProofBound_nonneg hp w d a N n)
    · exact mul_nonneg (Real.rpow_nonneg hQ _)
        (Real.rpow_nonneg (offDiagonalProofBound_nonneg hp w d a N n) _)
  have hs' := hs.of_nonneg_of_le hnon hdom
  refine ⟨hs',?_⟩
  simpa only [tsum_mul_left] using hs'.tsum_le_tsum hdom hs

/-- Uniform component bounds give a cubic p-power budget for the regional majorant. -/
theorem resonantCubicMajorant_sum_le (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (d a : WeightedCoeff w.toWeight p) (N : ℕ) (hN : 0 < N)
    (B : ℝ) (hB : 0 ≤ B) (hd : ‖d‖ ≤ B) (ha : ‖a‖ ≤ B) :
    (∑' n : ℤ, (offDiagonalProofBound hp w d a N n)^p.toReal) ≤
      2*offDiagonalProofConstant p*B^(3*p.toReal) := by
  have hP : 0 < p.toReal := ENNReal.toReal_pos (zero_lt_one.trans hp1).ne' hp
  have hC := (offDiagonalProofConstant_pos hp hp1).le
  have hx := offDiagonalProofBound_sum_le_of_norm_bounds hp hp1 w d a N hN B B hB hB hd ha
    ((WeightedCoeff.norm_fourierTail_le w.toWeight N d).trans hd)
    ((WeightedCoeff.norm_fourierTail_le w.toWeight N a).trans ha)
  have hpow : 1 ≤ (N : ℝ)^(min 1 (p.toReal-1)) := by
    apply Real.one_le_rpow
    · exact_mod_cast hN
    · have hpR : 1 < p.toReal := (ENNReal.toReal_lt_toReal (by simp) hp).mpr hp1
      exact le_min (by norm_num) (by linarith)
  have hpowd := Real.rpow_le_rpow (norm_nonneg _) hd hP.le
  have hdiv := div_le_self (Real.rpow_nonneg hB (2*p.toReal)) hpow
  have hprod : B^p.toReal*B^(2*p.toReal) = B^(3*p.toReal) := by
    rw [← Real.rpow_add' hB (by positivity : p.toReal+2*p.toReal ≠ 0)]
    congr 1
    ring
  apply hx.trans
  calc
    _ ≤ offDiagonalProofConstant p*B^p.toReal*(B^(2*p.toReal)+B^(2*p.toReal)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hpowd hC) (add_le_add hdiv le_rfl)
        (by positivity) (mul_nonneg hC (Real.rpow_nonneg hB _))
    _ = 2*offDiagonalProofConstant p*(B^p.toReal*B^(2*p.toReal)) := by ring
    _ = _ := by rw [hprod]

/-- An explicit exponent-only constant for the fifth-order error tail. -/
def resonantCubicTailConstant (hp : p ≠ ⊤) : ℝ :=
  2*offDiagonalProofConstant p*(2*weightedDoubleConstant (p := p) hp)^p.toReal

/-- Small weighted potentials have summable full-strip errors bounded by norm(phi)^(5p). -/
theorem resonantCubicErrorSup_tail (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (N : ℕ) (hN : 0 < N)
    (hsmall : 2*weightedDoubleConstant (p := p) hp*‖φ‖^2 ≤ 1/2) (positive : Bool) :
    Summable (sourceCoefficientPowerTail p N (fun n => resonantCubicErrorSup hp w φ n positive)) ∧
    (∑' n : ℤ, sourceCoefficientPowerTail p N (fun k => resonantCubicErrorSup hp w φ k positive) n) ≤
      resonantCubicTailConstant hp*‖φ‖^(5*p.toReal) := by
  let Q := 2*weightedDoubleConstant (p := p) hp*‖φ‖^2
  have hD := weightedDoubleConstant_nonneg (p := p) hp
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  let d := if positive then φ.snd else w.reflection φ.fst
  let a := if positive then w.reflection φ.fst else φ.snd
  have hd : ‖d‖ ≤ ‖φ‖ := by
    cases positive <;> dsimp [d]
    · rw [LinearIsometryEquiv.norm_map]; exact WithLp.norm_fst_le _ φ
    · exact WithLp.norm_snd_le _ φ
  have ha : ‖a‖ ≤ ‖φ‖ := by
    cases positive <;> dsimp [a]
    · exact WithLp.norm_snd_le _ φ
    · rw [LinearIsometryEquiv.norm_map]; exact WithLp.norm_fst_le _ φ
  have hb (n : ℤ) (hn : N ≤ n.natAbs) : 0 ≤ resonantCubicErrorSup hp w φ n positive ∧
      resonantCubicErrorSup hp w φ n positive ≤ Q*offDiagonalProofBound hp w d a N n := by
    have hx := (resonantCubicErrorSup_bounds hp hp1 w φ N n hn positive Q (fun z hz =>
      ⟨(resonantCubic_square_bound hp w φ n z hz).trans hsmall,
        resonantCubic_square_bound hp w φ n z hz⟩)).2
    refine ⟨hx.1,?_⟩
    cases positive <;> simpa only [resonantCubicMajorant,Bool.false_eq_true,if_false,if_true,d,a] using hx.2.1
  obtain ⟨hs,hbound⟩ := resonantCubic_scaled_dominated_tail hp hp1 w d a N hN Q hQ _ hb
  refine ⟨hs,hbound.trans ?_⟩
  have hmajor := resonantCubicMajorant_sum_le hp hp1 w d a N hN ‖φ‖ (norm_nonneg _) hd ha
  have hP : 0 < p.toReal := ENNReal.toReal_pos (zero_lt_one.trans hp1).ne' hp
  calc
    _ ≤ Q^p.toReal*(2*offDiagonalProofConstant p*‖φ‖^(3*p.toReal)) :=
      mul_le_mul_of_nonneg_left hmajor (Real.rpow_nonneg hQ _)
    _ = resonantCubicTailConstant hp*‖φ‖^(5*p.toReal) := by
      dsimp [Q,resonantCubicTailConstant]
      rw [Real.mul_rpow (by positivity : 0 ≤ 2*weightedDoubleConstant (p := p) hp) (sq_nonneg _),
        ← Real.rpow_natCast_mul (norm_nonneg _) 2]
      have hprod : ‖φ‖^(2*p.toReal)*‖φ‖^(3*p.toReal) = ‖φ‖^(5*p.toReal) := by
        rw [← Real.rpow_add' (norm_nonneg _) (by positivity : 2*p.toReal+3*p.toReal ≠ 0)]
        congr 1
        ring
      calc
        _ = (2*offDiagonalProofConstant p*(2*weightedDoubleConstant (p := p) hp)^p.toReal)*
            (‖φ‖^(2*p.toReal)*‖φ‖^(3*p.toReal)) := by ring_nf
        _ = _ := by rw [hprod]

/-- The explicit error-tail constant is nonnegative. -/
theorem resonantCubicTailConstant_nonneg (hp : p ≠ ⊤) (hp1 : 1 < p) : 0 ≤ resonantCubicTailConstant hp := by
  have hD := weightedDoubleConstant_nonneg (p := p) hp
  have hC := (offDiagonalProofConstant_pos hp hp1).le
  unfold resonantCubicTailConstant
  positivity

end NLS.ZakharovShabat
