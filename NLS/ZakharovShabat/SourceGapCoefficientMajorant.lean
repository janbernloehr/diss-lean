import NLS.ZakharovShabat.SourceLemma6_9ProofRoots
import NLS.ZakharovShabat.SourceLemma6_8
import NLS.ZakharovShabat.UniformGapMajorant

/-! # Corrected original gap and coefficient powers

The final p.44 inference is implemented with the valid exponent-only constant
`rootGapSummationConstant p = 2^(3*p.toReal-2)`. The actual original spectral
pair, signed leading Fourier coefficients and full-strip suprema are retained.
No optimality or refutation of the printed constant is asserted here.
-/
noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The corrected exponent-only splitting constant is strictly positive. -/
theorem rootGapSummationConstant_pos (p : ℝ≥0∞) : 0 < rootGapSummationConstant p := by
  unfold rootGapSummationConstant
  positivity

/-- A compact expression for the valid, deliberately nonoptimal splitting constant. -/
theorem rootGapSummationConstant_eq_rpow (p : ℝ≥0∞) : rootGapSummationConstant p = (2 : ℝ)^(3*p.toReal-2) := by
  unfold rootGapSummationConstant
  rw [pow_two,← Real.rpow_add (by norm_num : (0 : ℝ) < 2),← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  congr 1
  ring

/-- The literal two leading Fourier terms, with the signed cutoff boundary retained. -/
def sourceGapLeadingPowerTail (w : SpectralWeight) (φ : CoeffPair p) (N : ℕ) (n : ℤ) : ℝ :=
  if N ≤ n.natAbs then (w (2*n))^p.toReal *
    (‖φ.fst (-(2*n))‖^p.toReal+‖φ.snd (2*n)‖^p.toReal) else 0

/-- The two original full-strip remainder powers; their suprema already include the weight. -/
def sourceGapRemainderPowerTail (hp : p ≠ ⊤) (w : SpectralWeight) (φ : CoeffPair p) (N : ℕ) (n : ℤ) : ℝ :=
  if N ≤ n.natAbs then (sourceResonantBMinusSup hp w φ n)^p.toReal+
    (sourceResonantBPlusSup hp w φ n)^p.toReal else 0

/-- The weighted power tail of the actual original canonical periodic gap. -/
def sourceCanonicalWeightedGapPowerTail (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight) (φ : CoeffPair p) (N : ℕ) (n : ℤ) : ℝ :=
  if N ≤ n.natAbs then (w (2*n))^p.toReal * ‖sourcePeriodTwoCanonicalGap hp hp1 φ n‖^p.toReal else 0

/-- Forgetting a weight preserves the physical leading Fourier coefficients. -/
theorem sourceGapLeadingPowerTail_weightedInput (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight p) (N : ℕ) :
    sourceGapLeadingPowerTail w (sourceWeightedPeriodTwoInput w φ) N =
      fun n : ℤ => if N ≤ n.natAbs then resonantLeadingPower w φ n else 0 := by
  funext n
  unfold sourceGapLeadingPowerTail resonantLeadingPower
  simp only [sourceWeightedPeriodTwoInput_fst,sourceWeightedPeriodTwoInput_snd,
    Real.mul_rpow (w.positive _).le (norm_nonneg _),mul_add]

/-- The grouped original remainder tail is the sum of the two coefficient tails. -/
theorem sourceGapRemainderPowerTail_eq (hp : p ≠ ⊤) (w : SpectralWeight) (φ : CoeffPair p) (N : ℕ) :
    sourceGapRemainderPowerTail hp w φ N = sourceCoefficientPowerTail p N (sourceResonantBMinusSup hp w φ) +
      sourceCoefficientPowerTail p N (sourceResonantBPlusSup hp w φ) := by
  funext n
  simp only [Pi.add_apply]
  unfold sourceGapRemainderPowerTail sourceCoefficientPowerTail
  split_ifs <;> simp

/-- Every controlled original counted pair obeys the corrected four-term bound, including repeated roots and p=1. -/
theorem sourceResonantRootPair_gap_le_four_terms (hp : p ≠ ⊤) (w : SpectralWeight) (φ : CoeffPair p) (n : ℤ)
    (x y : ℂ) (hr : SourceResonantRootPair hp φ n x y) (hc : SourceCoefficientStripBounds hp w φ n) :
    (w (2*n)*‖x-y‖)^p.toReal ≤ rootGapSummationConstant p *
      ((w (2*n)*‖φ.fst (-(2*n))‖)^p.toReal+(w (2*n)*‖φ.snd (2*n)‖)^p.toReal+
        (sourceResonantBMinusSup hp w φ n)^p.toReal+(sourceResonantBPlusSup hp w φ n)^p.toReal) := by
  obtain ⟨_,_,_,_,hm,hp',hb⟩ := hc
  let B := w (2*n)*‖φ.fst (-(2*n))‖+sourceResonantBMinusSup hp w φ n
  let C := w (2*n)*‖φ.snd (2*n)‖+sourceResonantBPlusSup hp w φ n
  have hw := w.positive (2*n)
  have hfull (z : ℂ) (hz : z ∈ resonantStrip n) :
      w (2*n)*‖sourceResonantBMinusFunction hp φ n z‖ ≤ B ∧
      w (2*n)*‖sourceResonantBPlusFunction hp φ n z‖ ≤ C := by
    have hm' := mul_le_mul_of_nonneg_left (norm_le_norm_sub_add
      (sourceResonantBMinusFunction hp φ n z) (φ.fst (-(2*n)))) hw.le
    have hp'' := mul_le_mul_of_nonneg_left (norm_le_norm_sub_add
      (sourceResonantBPlusFunction hp φ n z) (φ.snd (2*n))) hw.le
    obtain ⟨_,hmz,hpz⟩ := hb z hz
    dsimp [B,C]
    constructor <;> linarith
  have hpoint (z : ℂ) (hz : z ∈ resonantStrip n) :
      SpectralWeight.one (2*n)*‖sourceResonantBPlusFunction hp φ n z*sourceResonantBMinusFunction hp φ n z‖ ≤ B*C/(w (2*n))^2 := by
    simp only [SpectralWeight.one_apply,one_mul,norm_mul]
    apply (le_div_iff₀ (sq_pos_of_pos hw)).mpr
    have h := mul_le_mul (hfull z hz).1 (hfull z hz).2 (by positivity) (by dsimp [B]; positivity)
    nlinarith
  have hsup := (weightedStripSup_bounds SpectralWeight.one n _ _ hpoint).2.1
  simp only [weightedStripSup,SpectralWeight.one_apply,one_mul] at hsup
  change sourceResonantBProductSup hp φ n ≤ B*C/(w (2*n))^2 at hsup
  have hs := (le_div_iff₀ (sq_pos_of_pos hw)).mp hsup
  have hg := mul_le_mul_of_nonneg_left hr.gap_le (sq_nonneg (w (2*n)))
  have hP : 1 ≤ p.toReal := (ENNReal.toReal_le_toReal (by simp) hp).mpr (show 1 ≤ p from Fact.out)
  apply gap_rpow_le_four_terms hP (by positivity) (by positivity) (by positivity) hm hp'
  dsimp [B,C] at hs
  nlinarith

end NLS.ZakharovShabat
