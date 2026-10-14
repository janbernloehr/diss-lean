import NLS.ZakharovShabat.ResonantDiagonalQuadratic

/-!
# Exact nonlinear remainder of the resonant diagonal

The actual diagonal equals its quadratic reciprocal row plus the
explicit second-iterate correction of the even source vector. On the
proved contraction region, this remainder has a quartic source-norm
bound. This pointwise estimate does not assert half-exponent summability.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p r : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ r)]
local instance resonantDiagonalNonlinearRemainderConjFact : Fact (1 ≤ p.conjExponent) :=
  ⟨ENNReal.HolderConjugate.one_le p.conjExponent p⟩

/-- The explicit second-iterate correction tested against the actual diagonal row. -/
def weightedResonantDiagonalRemainder (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1) : ℂ :=
  ∑' k : ℤ, φ.snd.val (n-k)*complementarySymbol n z (-k)*
    (weightedPotentialInverse hp w φ n z hz
      (weightedPotentialInverse hp w φ n z hz (weightedResonantEvenVector hp w φ n z hz h 1))).fst.val k

/-- The full analytic diagonal splits exactly into its quadratic term and remainder. -/
theorem weightedResonantA_sub_quadratic (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1) :
    weightedResonantA hp w φ n z hz h-resonantDiagonalQuadratic (w.toCoeff φ.fst) (w.toCoeff φ.snd) n z =
      weightedResonantDiagonalRemainder hp w φ n z hz h := by
  let hq := (ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top
  let : Fact (1 ≤ p.conjExponent) := ⟨hq.le⟩
  have hlead := summable_complementaryRow hq (w.toCoeff φ.snd)
    (Coeff.reindex (Equiv.subRight n) (w.toCoeff φ.fst)) n z hz
  have hfull := summable_weightedResonantA_terms hp w φ n z hz h
  have hlead' : Summable (fun k : ℤ => φ.snd.val (n-k)*complementarySymbol n z (-k)*φ.fst.val (k-n)) := by
    simpa only [SpectralWeight.toCoeff_apply,Coeff.reindex_apply,Equiv.subRight_apply] using hlead
  rw [weightedResonantA_eq_tsum,resonantDiagonalQuadratic_eq_physical]
  simp only [SpectralWeight.toCoeff_apply]
  rw [← hfull.tsum_sub hlead']
  apply tsum_congr
  intro k
  have he := congrArg (fun f : WeightedCoeffPair w.toWeight p => f.fst.val k)
    (weightedResonantEvenVector_sub_source hp w φ n z hz h 1)
  have he' : (weightedResonantEvenVector hp w φ n z hz h 1).fst.val k-φ.fst.val (k-n) =
      (weightedPotentialInverse hp w φ n z hz
        (weightedPotentialInverse hp w φ n z hz (weightedResonantEvenVector hp w φ n z hz h 1))).fst.val k := by
    change (weightedResonantEvenVector hp w φ n z hz h 1).fst.val k-
      (weightedResonantSource hp w φ n 1).fst.val k = _ at he
    simpa only [weightedResonantSource_one_fst] using he
  change _ = φ.snd.val (n-k)*complementarySymbol n z (-k)*_
  rw [← he']
  ring

/-- The remainder retains the spectral square bound and the reciprocal row norm. -/
theorem norm_weightedResonantDiagonalRemainder_le (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (hw : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1)
    (h1 : ‖weightedPotentialSquareInShift hp SpectralWeight.one (w.forgetPairWeight φ) n z hz‖ < 1)
    (hh : ‖weightedPotentialSquareInShift hp SpectralWeight.one (w.forgetPairWeight φ) n z hz‖ ≤ 1/2) :
    ‖weightedResonantDiagonalRemainder hp w φ n z hz hw‖ ≤
      (weightedSquareBound hp SpectralWeight.one (w.forgetPairWeight φ) n *
        (2*‖w.forgetWeight φ.fst‖)) *
      ‖complementaryRowEnvelope
        ((ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top) (w.toCoeff φ.snd) n‖ := by
  let hq := (ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top
  let : Fact (1 ≤ p.conjExponent) := ⟨hq.le⟩
  let E := weightedResonantEvenVector hp w φ n z hz hw 1
  let T := weightedPotentialInverse hp w φ n z hz
  let F := T (T E)
  have hF : ‖w.forgetPairWeight F‖ ≤
      weightedSquareBound hp SpectralWeight.one (w.forgetPairWeight φ) n * ‖w.forgetPairWeight E‖ := by
    have hb := shiftedPairNorm_weightedPotentialInverse_sq_refined hp SpectralWeight.one
      (w.forgetPairWeight φ) n z hz (w.forgetPairWeight E)
    rw [← forgetPairWeight_potentialInverse hp w φ E n z hz,
      ← forgetPairWeight_potentialInverse hp w φ (T E) n z hz] at hb
    simpa only [SpectralWeight.shiftedPairNorm_one hp] using hb
  have hnorm : ‖w.toCoeff F.fst‖ ≤
      weightedSquareBound hp SpectralWeight.one (w.forgetPairWeight φ) n * (2*‖w.forgetWeight φ.fst‖) := by
    rw [w.norm_toCoeff_eq_norm_forgetWeight]
    have hf : ‖w.forgetWeight F.fst‖ ≤ ‖w.forgetPairWeight F‖ := by
      simpa only [SpectralWeight.forgetPairWeight_fst] using! (WithLp.norm_fst_le _ (w.forgetPairWeight F))
    exact (hf.trans hF).trans (mul_le_mul_of_nonneg_left
      (norm_forget_evenVector_one_le_unweighted hp w φ n z hz hw h1 hh)
      (weightedSquareBound_nonneg hp SpectralWeight.one (w.forgetPairWeight φ) n))
  have hr := norm_tsum_complementaryRow_le hq (w.toCoeff φ.snd) (w.toCoeff F.fst) n z hz
  have hr' : ‖weightedResonantDiagonalRemainder hp w φ n z hz hw‖ ≤ ‖w.toCoeff F.fst‖ * ‖complementaryRowEnvelope hq (w.toCoeff φ.snd) n‖ := by
    simpa only [weightedResonantDiagonalRemainder,SpectralWeight.toCoeff_apply] using hr
  exact hr'.trans (mul_le_mul_of_nonneg_right hnorm (norm_nonneg _))

/-- The unweighted spectral square bound is at most quadratic in the source norm. -/
theorem weightedSquareBound_one_le_norm_sq (hp : p ≠ ⊤)
    (φ : WeightedCoeffPair SpectralWeight.one.toWeight p) (n : ℤ) :
    weightedSquareBound hp SpectralWeight.one φ n ≤ 2*weightedDoubleConstant (p := p) hp*‖φ‖^2 := by
  have ht := norm_weightedPairFourierTail_le hp SpectralWeight.one.toWeight n.natAbs φ
  have he : (1+|(n:ℝ)|)^(-(1/p.toReal)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith [abs_nonneg (n:ℝ)]) (by simp only [neg_nonpos]; positivity)
  have hb : ‖φ‖*(1+|(n:ℝ)|)^(-(1/p.toReal)) ≤ ‖φ‖ := by
    simpa using mul_le_mul_of_nonneg_left he (norm_nonneg φ)
  simp only [weightedSquareBound,SpectralWeight.one_apply,div_one]
  have hD := weightedDoubleConstant_nonneg (p := p) hp
  nlinarith [mul_le_mul_of_nonneg_left (add_le_add hb ht) (mul_nonneg hD (norm_nonneg φ))]

/-- On the contraction region the actual nonlinear remainder is quartic in the source norm. -/
theorem norm_weightedResonantDiagonalRemainder_le_quartic (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (hw : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1)
    (h1 : ‖weightedPotentialSquareInShift hp SpectralWeight.one (w.forgetPairWeight φ) n z hz‖ < 1)
    (hh : ‖weightedPotentialSquareInShift hp SpectralWeight.one (w.forgetPairWeight φ) n z hz‖ ≤ 1/2) :
    ‖weightedResonantDiagonalRemainder hp w φ n z hz hw‖ ≤
      (4*weightedDoubleConstant (p := p) hp*
        ‖Coeff.puncturedLattice p.conjExponent
          ((ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top)‖)*
        ‖w.forgetPairWeight φ‖^4 := by
  let hq := (ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top
  have hfst : ‖w.forgetWeight φ.fst‖ ≤ ‖w.forgetPairWeight φ‖ := by
    simpa only [SpectralWeight.forgetPairWeight_fst] using! (WithLp.norm_fst_le _ (w.forgetPairWeight φ))
  have hsnd : ‖w.toCoeff φ.snd‖ ≤ ‖w.forgetPairWeight φ‖ := by
    rw [w.norm_toCoeff_eq_norm_forgetWeight]
    simpa only [SpectralWeight.forgetPairWeight_snd] using! (WithLp.norm_snd_le _ (w.forgetPairWeight φ))
  have hrow := (norm_complementaryRowEnvelope_le hq (w.toCoeff φ.snd) n).trans
    (mul_le_mul_of_nonneg_right hsnd (norm_nonneg _))
  apply (norm_weightedResonantDiagonalRemainder_le hp w φ n z hz hw h1 hh).trans
  calc
    _ ≤ (2*weightedDoubleConstant (p := p) hp*‖w.forgetPairWeight φ‖^2 *
        (2*‖w.forgetPairWeight φ‖)) *
        (‖w.forgetPairWeight φ‖*‖Coeff.puncturedLattice p.conjExponent hq‖) := by
      apply mul_le_mul
      · exact mul_le_mul (weightedSquareBound_one_le_norm_sq hp (w.forgetPairWeight φ) n)
          (mul_le_mul_of_nonneg_left hfst (by norm_num)) (by positivity)
          (by have := weightedDoubleConstant_nonneg (p := p) hp; positivity)
      · exact hrow
      · exact norm_nonneg _
      · have := weightedDoubleConstant_nonneg (p := p) hp
        positivity
    _ = _ := by ring

/-- An exponent-only constant for the uniform quartic remainder bound. -/
def resonantDiagonalRemainderConstant (hp : p ≠ ⊤) : ℝ :=
  4*weightedDoubleConstant (p := p) hp*
    ‖Coeff.puncturedLattice p.conjExponent
      ((ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top)‖

theorem resonantDiagonalRemainderConstant_nonneg (hp : p ≠ ⊤) : 0 ≤ resonantDiagonalRemainderConstant (p := p) hp := by
  have := weightedDoubleConstant_nonneg (p := p) hp
  unfold resonantDiagonalRemainderConstant
  positivity

end NLS.ZakharovShabat
