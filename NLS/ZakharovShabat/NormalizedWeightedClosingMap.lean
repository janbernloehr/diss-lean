import NLS.ZakharovShabat.NormalizedWeightedPeriodOne
import NLS.ZakharovShabat.WeightedResonantCenterClosingTail

/-!
# The adapted spectral closing map in normalized weighted coordinates

The map acts on normalized weighted Fourier coefficients. It is the identity
plus the reflected moving-center remainder. Frequencies below the cutoff
retain their normalized coefficients; high frequencies are the actual
closing equations multiplied by the physical weight. The first component
uses the negative equation at resonance `-n`.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual moving-center remainder transported to normalized weighted
source coordinates, with reflection in the first component only. -/
def normalizedWeightedSourceRemainder (hp : p ≠ ⊤) (w : SpectralWeight) (φ : CoeffPair p) (N : ℕ) : CoeffPair p :=
  sourceClosingReflection (weightedResonantCenterRemainder hp w
    (normalizedWeightedPeriodOne w φ) N)

/-- The normalized source coefficients with the high block replaced
by the weighted signed spectral closing equations. -/
def normalizedWeightedClosingMap (hp : p ≠ ⊤) (w : SpectralWeight) (φ : CoeffPair p) (N : ℕ) : CoeffPair p :=
  φ+normalizedWeightedSourceRemainder hp w φ N

/-- Source transport preserves the actual joint remainder norm. -/
theorem norm_normalizedWeightedSourceRemainder (hp : p ≠ ⊤) (w : SpectralWeight) (φ : CoeffPair p) (N : ℕ) :
    ‖normalizedWeightedSourceRemainder hp w φ N‖ =
      ‖weightedResonantCenterRemainder hp w (normalizedWeightedPeriodOne w φ) N‖ :=
  sourceClosingReflection.norm_map _

/-- The difference from the identity is exactly the actual source remainder. -/
theorem normalizedWeightedClosingMap_sub_source (hp : p ≠ ⊤) (w : SpectralWeight) (φ : CoeffPair p) (N : ℕ) :
    normalizedWeightedClosingMap hp w φ N-φ = normalizedWeightedSourceRemainder hp w φ N :=
  add_sub_cancel_left _ _

/-- Sequence membership identifies the adapted map with the actual
weighted closing equations at the physical source, including the unchanged
low normalized Fourier block. The negative equation is evaluated at resonance `-n`. -/
theorem normalizedWeightedClosingMap_apply_of_mem (hp : p ≠ ⊤) (w : SpectralWeight) (φ : CoeffPair p) (N : ℕ)
    (hmem : ∀ positive : Bool, Memℓp (weightedResonantCenterRemainderCoordinate hp w
      (normalizedWeightedPeriodOne w φ) N positive) p) (n : ℤ) :
    (normalizedWeightedClosingMap hp w φ N).fst n =
      (if N ≤ n.natAbs then (w (2*n) : ℂ)*weightedResonantBMinusExtension hp w
        (normalizedWeightedPeriodOne w φ) (-n)
        (weightedResonantDiagonalCenter hp w (normalizedWeightedPeriodOne w φ) (-n))
      else φ.fst n) ∧
    (normalizedWeightedClosingMap hp w φ N).snd n =
      (if N ≤ n.natAbs then (w (2*n) : ℂ)*weightedResonantBPlusExtension hp w
        (normalizedWeightedPeriodOne w φ) n
        (weightedResonantDiagonalCenter hp w (normalizedWeightedPeriodOne w φ) n)
      else φ.snd n) := by
  have hrem := weightedResonantCenterRemainder_apply_of_mem hp w
    (normalizedWeightedPeriodOne w φ) N hmem
  constructor
  · change φ.fst n+(weightedResonantCenterRemainder hp w
      (normalizedWeightedPeriodOne w φ) N).fst (-n) = _
    rw [(hrem (-n)).1]
    by_cases hn : N ≤ n.natAbs <;>
      simp [weightedResonantCenterRemainderCoordinate,hn,mul_neg, mul_sub]
    have hw : (w (2*n) : ℂ) ≠ 0 := w.toWeight.complex_ne_zero _
    field_simp
    ring
  · change φ.snd n+(weightedResonantCenterRemainder hp w
      (normalizedWeightedPeriodOne w φ) N).snd n = _
    rw [(hrem n).2]
    by_cases hn : N ≤ n.natAbs <;>
      simp [weightedResonantCenterRemainderCoordinate,hn,mul_sub]
    have hw : (w (2*n) : ℂ) ≠ 0 := w.toWeight.complex_ne_zero _
    field_simp
    ring

end NLS.ZakharovShabat
