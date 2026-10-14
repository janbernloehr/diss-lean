import NLS.ZakharovShabat.OffDiagonalUniformBound
import NLS.ZakharovShabat.DiagonalSummationExponent
import NLS.SequenceSpaces.QuasiHolderProduct
import NLS.ZakharovShabat.ResonantGapMajorant

/-!
# Sequence majorants for full off-diagonal coefficients

Powered Young bounds the double reciprocal rows in the original exponent.
Adding the leading Fourier coefficients gives two actual ℓp majorants,
with a polynomial norm budget on bounded sets of unit-weight sources.
Their product controls the full-strip off-diagonal product supremum.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
local instance midpointProductConjFact : Fact (1 ≤ p.conjExponent) :=
  ⟨ENNReal.HolderConjugate.one_le p.conjExponent p⟩

/-- The reciprocal norm used in the full off-diagonal majorant. -/
def resonantOffDiagonalRowConstant (hp : p ≠ ⊤) (hp1 : 1 < p) : ℝ := by
  let : Fact (1 ≤ diagonalInnerExponent p) := ⟨(one_lt_diagonalInnerExponent hp hp1).le⟩
  exact ‖Coeff.puncturedLattice (diagonalInnerExponent p) (one_lt_diagonalInnerExponent hp hp1)‖^2

theorem resonantOffDiagonalRowConstant_nonneg (hp : p ≠ ⊤) (hp1 : 1 < p) :
    0 ≤ resonantOffDiagonalRowConstant hp hp1 := by unfold resonantOffDiagonalRowConstant; positivity

/-- Leading coefficients plus the full double-row remainder have an actual ℓp majorant. -/
theorem exists_fullOffDiagonalMajorant (hp : p ≠ ⊤) (hp1 : 1 < p) (a d : Coeff p) :
    ∃ B : Coeff p,
      (∀ n : ℤ, ‖d (2*n)‖+2*‖d‖^2*‖doubleReciprocalRow
        ((ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top) a n‖ ≤ ‖B n‖) ∧
      ‖B‖ ≤ ‖d‖+2*‖d‖^2*‖a‖*resonantOffDiagonalRowConstant hp hp1 := by
  let r := diagonalInnerExponent p
  have hr := one_lt_diagonalInnerExponent hp hp1
  let : Fact (1 ≤ r) := ⟨hr.le⟩
  let k := Coeff.puncturedLattice r hr
  obtain ⟨e,he,hen⟩ := Coeff.exists_evenIteratedConvolutionRowNorm (r := r) hp (min_le_left _ _) a k k
  let B : Coeff p := Coeff.magnitude (Coeff.periodHalve d)+(2*‖d‖^2:ℝ) • Coeff.magnitude e
  have hBn (n : ℤ) : ‖B n‖ = ‖d (2*n)‖+2*‖d‖^2*‖e n‖ := by
    change ‖(‖d (2*n)‖:ℂ)+(2*‖d‖^2:ℝ) • (‖e n‖:ℂ)‖ = _
    rw [Complex.real_smul,← Complex.ofReal_mul,← Complex.ofReal_add,Complex.norm_real,
      Real.norm_of_nonneg (by positivity)]
  refine ⟨B,?_,?_⟩
  · intro n
    rw [hBn]
    apply add_le_add le_rfl
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [he,Complex.norm_real,norm_norm]
    exact norm_doubleReciprocalRow_le_inner (r := r) hr (min_le_right _ _) a n
  · have h := norm_add_le (Coeff.magnitude (Coeff.periodHalve d)) ((2*‖d‖^2:ℝ) • Coeff.magnitude e)
    rw [norm_smul,Coeff.norm_magnitude,Coeff.norm_magnitude,Real.norm_of_nonneg (by positivity)] at h
    exact h.trans (add_le_add (Coeff.norm_periodHalve_le d)
      ((mul_le_mul_of_nonneg_left hen (by positivity)).trans_eq (by
        dsimp [resonantOffDiagonalRowConstant,k,r]
        ring)))

/-- A source ball gives a polynomial bound for each full off-diagonal majorant. -/
def resonantOffDiagonalNormBudget (hp : p ≠ ⊤) (hp1 : 1 < p) (R : ℝ) : ℝ :=
  R+2*R^3*resonantOffDiagonalRowConstant hp hp1

theorem resonantOffDiagonalNormBudget_nonneg (hp : p ≠ ⊤) (hp1 : 1 < p) {R : ℝ} (hR : 0 ≤ R) :
    0 ≤ resonantOffDiagonalNormBudget hp hp1 R := by
  have := resonantOffDiagonalRowConstant_nonneg hp hp1
  unfold resonantOffDiagonalNormBudget
  positivity

/-- The majorant norm is uniform when both components are bounded by the same radius. -/
theorem exists_bounded_fullOffDiagonalMajorant (hp : p ≠ ⊤) (hp1 : 1 < p) (a d : Coeff p)
    {R : ℝ} (ha : ‖a‖ ≤ R) (hd : ‖d‖ ≤ R) :
    ∃ B : Coeff p,
      (∀ n : ℤ, ‖d (2*n)‖+2*‖d‖^2*‖doubleReciprocalRow
        ((ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top) a n‖ ≤ ‖B n‖) ∧
      ‖B‖ ≤ resonantOffDiagonalNormBudget hp hp1 R := by
  obtain ⟨B,hB,hBn⟩ := exists_fullOffDiagonalMajorant hp hp1 a d
  refine ⟨B,hB,hBn.trans ?_⟩
  have hR := (norm_nonneg a).trans ha
  have hC := resonantOffDiagonalRowConstant_nonneg hp hp1
  calc
    _ ≤ R+2*R^2*R*resonantOffDiagonalRowConstant hp hp1 := by gcongr
    _ = _ := by unfold resonantOffDiagonalNormBudget; ring

/-- Unit-weight full coefficients and their product are dominated by two ℓp sequences. -/
theorem exists_unitOffDiagonalMajorants (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : WeightedCoeffPair SpectralWeight.one.toWeight p) (N : ℕ) {R : ℝ} (hR : ‖φ‖ ≤ R)
    (hb : ∀ n : ℤ, N ≤ n.natAbs → ∀ z ∈ resonantStrip n,
      ‖weightedResonantBMinusExtension hp SpectralWeight.one φ n z-φ.fst.val (-(2*n))‖ ≤
        resonantBMinusRemainderBound hp SpectralWeight.one φ n ∧
      ‖weightedResonantBPlusExtension hp SpectralWeight.one φ n z-φ.snd.val (2*n)‖ ≤
        resonantBPlusRemainderBound hp SpectralWeight.one φ n) :
    ∃ B C : Coeff p,
      ‖B‖ ≤ resonantOffDiagonalNormBudget hp hp1 R ∧
      ‖C‖ ≤ resonantOffDiagonalNormBudget hp hp1 R ∧
      (∀ n : ℤ, N ≤ n.natAbs → ∀ z ∈ resonantStrip n,
        ‖weightedResonantBMinusExtension hp SpectralWeight.one φ n z‖ ≤ ‖B n‖ ∧
        ‖weightedResonantBPlusExtension hp SpectralWeight.one φ n z‖ ≤ ‖C n‖) ∧
      ∀ n : ℤ, N ≤ n.natAbs → resonantBProductSup hp SpectralWeight.one φ n ≤ ‖B n‖*‖C n‖ := by
  let a := WeightedCoeff.weightEquiv SpectralWeight.one.toWeight p φ.snd
  let d := WeightedCoeff.weightEquiv SpectralWeight.one.toWeight p (SpectralWeight.one.reflection φ.fst)
  have ha : ‖a‖ = ‖φ.snd‖ := rfl
  have hd : ‖d‖ = ‖φ.fst‖ := by
    change ‖SpectralWeight.one.reflection φ.fst‖ = ‖φ.fst‖
    exact LinearIsometryEquiv.norm_map _ _
  have haR : ‖a‖ ≤ R := ha ▸ (WithLp.norm_snd_le _ φ).trans hR
  have hdR : ‖d‖ ≤ R := hd ▸ (WithLp.norm_fst_le _ φ).trans hR
  obtain ⟨B,hB,hBn⟩ := exists_bounded_fullOffDiagonalMajorant hp hp1 a d haR hdR
  obtain ⟨C,hC,hCn⟩ := exists_bounded_fullOffDiagonalMajorant hp hp1 d a hdR haR
  have hfull (n : ℤ) (hn : N ≤ n.natAbs) (z : ℂ) (hz : z ∈ resonantStrip n) :
      ‖weightedResonantBMinusExtension hp SpectralWeight.one φ n z‖ ≤ ‖B n‖ ∧
      ‖weightedResonantBPlusExtension hp SpectralWeight.one φ n z‖ ≤ ‖C n‖ := by
    have hm := norm_le_norm_sub_add (weightedResonantBMinusExtension hp SpectralWeight.one φ n z)
      (φ.fst.val (-(2*n)))
    have hp' := norm_le_norm_sub_add (weightedResonantBPlusExtension hp SpectralWeight.one φ n z)
      (φ.snd.val (2*n))
    have hm' := hB n
    have hp'' := hC n
    rw [hd] at hm'
    rw [ha] at hp''
    have hdval : d (2*n) = φ.fst.val (-(2*n)) := by simp [d,WeightedCoeff.weightEquiv_apply]
    have haval : a (2*n) = φ.snd.val (2*n) := by simp [a,WeightedCoeff.weightEquiv_apply]
    rw [hdval] at hm'
    rw [haval] at hp''
    have hh := hb n hn z hz
    change _ ≤ 2*‖φ.fst‖^2*‖doubleReciprocalRow _ a n‖ ∧
      _ ≤ 2*‖φ.snd‖^2*‖doubleReciprocalRow _ d n‖ at hh
    constructor <;> linarith
  refine ⟨B,C,hBn,hCn,hfull,?_⟩
  intro n hn
  simpa only [SpectralWeight.one_apply,one_pow,one_mul] using
    weighted_resonantBProductSup_le hp SpectralWeight.one φ n ‖B n‖ ‖C n‖ (norm_nonneg _)
      (by simpa only [SpectralWeight.one_apply,one_mul] using hfull n hn)

end NLS.ZakharovShabat
