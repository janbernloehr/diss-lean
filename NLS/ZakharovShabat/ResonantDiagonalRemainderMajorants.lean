import NLS.ZakharovShabat.ResonantDiagonalRemainderRows

/-!
# Half-exponent majorants for the nonlinear diagonal remainder

Powered Young puts each retained row in ℓp. Their product belongs to
ℓ(p/2), including p/2 below one. The same majorant controls every spectral
parameter in the full strip wherever the actual contraction bounds hold.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
local instance remainderMajorantDoubleFact : Fact (1 ≤ 2*p) := ⟨one_le_double_exponent Fact.out⟩
local instance remainderMajorantConjFact : Fact (1 ≤ (2*p).conjExponent) :=
  ⟨ENNReal.HolderConjugate.one_le (2*p).conjExponent (2*p)⟩

/-- The strictly summable inner exponent for both retained rows. -/
def diagonalRemainderInnerExponent (p : ℝ≥0∞) : ℝ≥0∞ := min p (2*p).conjExponent

theorem one_lt_diagonalRemainderInnerExponent (hp : p ≠ ⊤) (hp1 : 1 < p) :
    1 < diagonalRemainderInnerExponent p := lt_min hp1 (one_lt_double_conjugate hp)

/-- The three reciprocal factors contribute an exponent-only cubic norm constant. -/
def diagonalRemainderRowConstant (hp : p ≠ ⊤) (hp1 : 1 < p) : ℝ := by
  let : Fact (1 ≤ diagonalRemainderInnerExponent p) := ⟨(one_lt_diagonalRemainderInnerExponent hp hp1).le⟩
  exact ‖Coeff.puncturedLattice (diagonalRemainderInnerExponent p)
    (one_lt_diagonalRemainderInnerExponent hp hp1)‖^3

theorem diagonalRemainderRowConstant_nonneg (hp : p ≠ ⊤) (hp1 : 1 < p) :
    0 ≤ diagonalRemainderRowConstant hp hp1 := by
  let : Fact (1 ≤ diagonalRemainderInnerExponent p) := ⟨(one_lt_diagonalRemainderInnerExponent hp hp1).le⟩
  change 0 ≤ ‖Coeff.puncturedLattice (diagonalRemainderInnerExponent p) _‖^3
  exact pow_nonneg (norm_nonneg _) _

/-- One half-exponent sequence controls the product of the two retained rows. -/
theorem exists_product_reciprocalRowMajorant (hp : p ≠ ⊤) (hp1 : 1 < p) (b : Coeff p) :
    ∃ D : Coeff (p/2),
      (∀ n : ℤ, ‖complementaryRowEnvelope (one_lt_double_conjugate hp) b n‖*
        ‖doubleReciprocalRow (one_lt_double_conjugate hp) b n‖ ≤ ‖D n‖) ∧
      ‖D‖ ≤ ‖b‖^2*diagonalRemainderRowConstant hp hp1 := by
  let t := diagonalRemainderInnerExponent p
  have ht := one_lt_diagonalRemainderInnerExponent hp hp1
  let : Fact (1 ≤ t) := ⟨ht.le⟩
  let K := Coeff.puncturedLattice t ht
  obtain ⟨B,hB,hBn⟩ := exists_reciprocalRowMajorant (r := t) hp ht (min_le_left _ _) (min_le_right _ _) b
  obtain ⟨C,hC,hCn⟩ := Coeff.exists_evenIteratedConvolutionRowNorm (r := t) hp (min_le_left _ _) b K K
  let : p.HolderTriple p (p/2) := Coeff.holderTriple_half p
  refine ⟨Coeff.quasiHolderProduct B C,?_,?_⟩
  · intro n
    rw [Coeff.quasiHolderProduct_apply,norm_mul]
    apply mul_le_mul (hB n) _ (norm_nonneg _) (norm_nonneg _)
    rw [hC,Complex.norm_real,norm_norm]
    exact norm_doubleReciprocalRow_le_inner (r := t) ht (min_le_right _ _) b n
  · have hpR := ENNReal.toReal_pos (zero_lt_one.trans hp1).ne' hp
    apply (Coeff.norm_quasiHolderProduct_le hpR hpR B C).trans
    calc
      _ ≤ (‖b‖*‖K‖)*(‖b‖*‖K‖*‖K‖) := mul_le_mul hBn hCn (norm_nonneg _) (by positivity)
      _ = _ := by dsimp [K,t,diagonalRemainderRowConstant]; ring

/-- The actual nonlinear diagonal remainder has a spectral-parameter-independent
ℓ(p/2) majorant, with a quartic potential-norm bound. -/
theorem exists_weightedResonantDiagonalRemainderMajorant (hp : p ≠ ⊤) (hp1 : 1 < p)
    (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight p) :
    ∃ D : Coeff (p/2),
      ‖D‖ ≤ 2*‖w.forgetWeight φ.fst‖^2*‖w.toCoeff φ.snd‖^2*diagonalRemainderRowConstant hp hp1 ∧
      ∀ n : ℤ, ∀ z : ℂ, ∀ hz : z ∈ resonantStrip n,
        ∀ hw : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1,
        ‖weightedPotentialSquareInShift hp SpectralWeight.one (w.forgetPairWeight φ) n z hz‖ ≤ 1/2 →
        ‖weightedResonantDiagonalRemainder hp w φ n z hz hw‖ ≤ ‖D n‖ := by
  obtain ⟨B,hB,hBn⟩ := exists_product_reciprocalRowMajorant hp hp1 (w.toCoeff φ.snd)
  let c := 2*‖w.forgetWeight φ.fst‖^2
  have hc : 0 ≤ c := by dsimp [c]; positivity
  let D : Coeff (p/2) := (c:ℂ) • B
  have hDn (n : ℤ) : ‖D n‖ = c*‖B n‖ := by
    simp only [D,lp.coeFn_smul,Pi.smul_apply,norm_smul,Complex.norm_real,Real.norm_of_nonneg hc]
  refine ⟨D,?_,?_⟩
  · rw [lp.norm_const_smul (ENNReal.div_pos (zero_lt_one.trans hp1).ne' (by norm_num)).ne',
      Complex.norm_real,Real.norm_of_nonneg hc]
    exact (mul_le_mul_of_nonneg_left hBn hc).trans_eq (by dsimp [c]; ring)
  · intro n z hz hw hh
    have h1 := hh.trans_lt (by norm_num : (1/2:ℝ)<1)
    apply (norm_weightedResonantDiagonalRemainder_le_rows hp w φ n z hz hw h1 hh).trans
    rw [hDn]
    exact (mul_le_mul_of_nonneg_left (hB n) hc).trans_eq' (by dsimp [c]; ring)

end NLS.ZakharovShabat
