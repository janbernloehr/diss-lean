import NLS.SequenceSpaces.YoungConvolutionTranspose
import NLS.SequenceSpaces.ProductRowExponents
import NLS.ZakharovShabat.ResonantDiagonalNonlinearRemainder
import NLS.ZakharovShabat.UnweightedDoubleRowTesting

/-!
# Two reciprocal rows in the nonlinear diagonal remainder

Transposing the first convolution places its row in ℓ(2p). Testing the
remaining two resolvents at that exponent retains a second reciprocal
row. Both rows admit outer ℓp majorants, unlike a coarse operator bound.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
local instance remainderRowsDoubleFact : Fact (1 ≤ 2*p) := ⟨one_le_double_exponent Fact.out⟩
local instance remainderRowsConjFact : Fact (1 ≤ (2*p).conjExponent) :=
  ⟨ENNReal.HolderConjugate.one_le (2*p).conjExponent (2*p)⟩

/-- The exact transposed first convolution, in the doubled input exponent. -/
def resonantDiagonalTransposeRow (hp : p ≠ ⊤) (a b : Coeff p)
    (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n) : Coeff (2*p) :=
  Coeff.youngConvolution (youngRelation_double_conjugate p) (Coeff.reflection a)
    (complementaryPotentialRow (one_lt_double_conjugate hp) b n z hz)

/-- Young's inequality retains the first parameter-independent reciprocal row. -/
theorem norm_resonantDiagonalTransposeRow_le (hp : p ≠ ⊤) (a b : Coeff p)
    (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n) :
    ‖resonantDiagonalTransposeRow hp a b n z hz‖ ≤
      ‖a‖*‖complementaryRowEnvelope (one_lt_double_conjugate hp) b n‖ := by
  apply (Coeff.norm_youngConvolution_le _ _ _).trans
  rw [LinearIsometryEquiv.norm_map]
  exact mul_le_mul_of_nonneg_left (norm_complementaryPotentialRow_le _ b n z hz) (norm_nonneg _)

/-- The transposed series equals the actual nonlinear remainder, with its physical signs. -/
theorem weightedResonantDiagonalRemainder_eq_transposed (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1) :
    weightedResonantDiagonalRemainder hp w φ n z hz h =
      ∑' l : ℤ, ∑' k : ℤ,
        resonantDiagonalTransposeRow hp (w.toCoeff φ.fst) (w.toCoeff φ.snd) n z hz l *
        φ.snd.val (l+k)*complementarySymbol n z l*complementarySymbol n z k*
        (weightedResonantEvenVector hp w φ n z hz h 1).fst.val (-k) := by
  let E := weightedResonantEvenVector hp w φ n z hz h 1
  let T := weightedPotentialInverse hp w φ n z hz
  let a := w.toCoeff φ.fst
  let b := w.toCoeff φ.snd
  let u := complementaryPotentialRow (one_lt_double_conjugate hp) b n z hz
  let v := w.toCoeff (complementaryScalarL1 hp w.toWeight n z hz false (T E).snd)
  have hF : w.toCoeff (T (T E)).fst = Coeff.convolution a v := by
    change w.toCoeff (w.convolution φ.fst _) = _
    exact w.toCoeff_convolution _ _
  have he : weightedResonantDiagonalRemainder hp w φ n z hz h =
      ∑' k : ℤ, u k*Coeff.convolution a v k := by
    unfold weightedResonantDiagonalRemainder
    apply tsum_congr
    intro k
    have hk := congrArg (fun f : Coeff p => f k) hF
    simpa only [u,b,complementaryPotentialRow_apply,SpectralWeight.toCoeff_apply,E,T] using
      congrArg (fun t : ℂ => φ.snd.val (n-k)*complementarySymbol n z (-k)*t) hk
  rw [he,Coeff.tsum_convolution_transpose (youngRelation_double_conjugate p)]
  apply tsum_congr
  intro l
  have hv : v l = complementarySymbol n z l *
      ∑' k : ℤ, φ.snd.val (l+k)*complementarySymbol n z k*E.fst.val (-k) := by
    simp only [v,SpectralWeight.toCoeff_apply,complementaryScalarL1_apply,freeFrequency_false]
    rw [weightedPotentialInverse_snd,SpectralWeight.convolution_apply,
      ← (Equiv.neg ℤ).tsum_eq]
    congr 1
    apply tsum_congr
    intro k
    simp only [Equiv.neg_apply,sub_neg_eq_add,complementaryScalarL1_apply,freeFrequency_true,neg_neg]
    ring
  rw [hv,← tsum_mul_left,← tsum_mul_left]
  apply tsum_congr
  intro k
  change _ = resonantDiagonalTransposeRow hp a b n z hz l *
    φ.snd.val (l+k)*complementarySymbol n z l*complementarySymbol n z k*E.fst.val (-k)
  unfold resonantDiagonalTransposeRow
  dsimp [u]
  ring

/-- Changing the input ambient exponent does not change a double reciprocal row. -/
theorem doubleReciprocalRow_exponentInclusion {q r : ℝ≥0∞} [Fact (1 ≤ q)] [Fact (1 ≤ r)]
    (hpq : p ≤ q) (hr : 1 < r) (b : Coeff p) (n : ℤ) :
    doubleReciprocalRow hr (Coeff.exponentInclusion hpq b) n = doubleReciprocalRow hr b n := by
  have he (m : ℤ) : Coeff.convolutionRow (Coeff.exponentInclusion hpq b)
      (Coeff.puncturedLattice r hr) m = Coeff.convolutionRow b (Coeff.puncturedLattice r hr) m := by
    ext k
    rfl
  ext j
  simp only [doubleReciprocalRow,Coeff.iteratedConvolutionRow_apply,he]

/-- The nonlinear remainder retains a product of two source-frequency row norms. -/
theorem norm_weightedResonantDiagonalRemainder_le_rows (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (hw : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1)
    (h1 : ‖weightedPotentialSquareInShift hp SpectralWeight.one (w.forgetPairWeight φ) n z hz‖ < 1)
    (hh : ‖weightedPotentialSquareInShift hp SpectralWeight.one (w.forgetPairWeight φ) n z hz‖ ≤ 1/2) :
    ‖weightedResonantDiagonalRemainder hp w φ n z hz hw‖ ≤
      (2*‖w.forgetWeight φ.fst‖^2)*
        ‖complementaryRowEnvelope (one_lt_double_conjugate hp) (w.toCoeff φ.snd) n‖*
        ‖doubleReciprocalRow (one_lt_double_conjugate hp) (w.toCoeff φ.snd) n‖ := by
  let E := weightedResonantEvenVector hp w φ n z hz hw 1
  let hle := (youngRelation_double_conjugate p).left_le
  let B := Coeff.exponentInclusion hle (w.toCoeff φ.snd)
  let F := Coeff.exponentInclusion hle (Coeff.reflection (w.toCoeff E.fst))
  have hF : ‖F‖ ≤ 2*‖w.forgetWeight φ.fst‖ := by
    apply (Coeff.norm_exponentInclusion_le hle _).trans
    rw [LinearIsometryEquiv.norm_map,w.norm_toCoeff_eq_norm_forgetWeight]
    exact (WithLp.norm_fst_le _ (w.forgetPairWeight E)).trans
      (norm_forget_evenVector_one_le_unweighted hp w φ n z hz hw h1 hh)
  have hbound := norm_tsum_resolvent_double_le (one_lt_double_conjugate hp)
    (resonantDiagonalTransposeRow hp (w.toCoeff φ.fst) (w.toCoeff φ.snd) n z hz) B F n z hz
  rw [weightedResonantDiagonalRemainder_eq_transposed]
  have hbound' := hbound
  simp only [B,F,Coeff.exponentInclusion_apply,Coeff.reflection_apply,
    SpectralWeight.toCoeff_apply,E] at hbound'
  apply hbound'.trans
  rw [show doubleReciprocalRow (one_lt_double_conjugate hp) B n =
    doubleReciprocalRow (one_lt_double_conjugate hp) (w.toCoeff φ.snd) n from
      doubleReciprocalRow_exponentInclusion hle _ _ _]
  have hD := norm_resonantDiagonalTransposeRow_le hp (w.toCoeff φ.fst) (w.toCoeff φ.snd) n z hz
  rw [w.norm_toCoeff_eq_norm_forgetWeight] at hD
  calc
    _ ≤ (‖w.forgetWeight φ.fst‖*‖complementaryRowEnvelope (one_lt_double_conjugate hp)
        (w.toCoeff φ.snd) n‖)*(2*‖w.forgetWeight φ.fst‖)*
        ‖doubleReciprocalRow (one_lt_double_conjugate hp) (w.toCoeff φ.snd) n‖ := by
      gcongr
    _ = _ := by ring

end NLS.ZakharovShabat
