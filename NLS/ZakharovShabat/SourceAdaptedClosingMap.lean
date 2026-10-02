import NLS.ZakharovShabat.SourceWeightedPeriodOne
import NLS.ZakharovShabat.WeightedResonantCenterClosingTail

/-!
# The adapted spectral closing map in the original source space

The map is the identity plus the reflected actual moving-center
remainder. Frequencies below the cutoff retain their original source
coefficients; the high frequencies are the actual closing equations.
The first component uses the negative equation at resonance `-n`, so
its leading Fourier coefficient is the original `φ₁(n)`.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual moving-center remainder transported to the original
source space, with reflection in the first component only. -/
def sourceResonantCenterRemainder (hp : p ≠ ⊤) (φ : CoeffPair p) (N : ℕ) : CoeffPair p :=
  sourceClosingReflection (weightedResonantCenterRemainder hp SpectralWeight.one
    (sourceWeightedPeriodOne φ) N)

/-- The original source coefficients with the high block replaced
by the actual signed spectral closing equations. -/
def sourceAdaptedClosingMap (hp : p ≠ ⊤) (φ : CoeffPair p) (N : ℕ) : CoeffPair p :=
  φ+sourceResonantCenterRemainder hp φ N

/-- Source transport preserves the actual joint remainder norm. -/
theorem norm_sourceResonantCenterRemainder (hp : p ≠ ⊤) (φ : CoeffPair p) (N : ℕ) :
    ‖sourceResonantCenterRemainder hp φ N‖ =
      ‖weightedResonantCenterRemainder hp SpectralWeight.one (sourceWeightedPeriodOne φ) N‖ :=
  sourceClosingReflection.norm_map _

/-- The difference from the identity is exactly the actual source remainder. -/
theorem sourceAdaptedClosingMap_sub_source (hp : p ≠ ⊤) (φ : CoeffPair p) (N : ℕ) :
    sourceAdaptedClosingMap hp φ N-φ = sourceResonantCenterRemainder hp φ N :=
  add_sub_cancel_left _ _

/-- Sequence membership identifies the adapted map with the actual
closing equations at the original source, including the unchanged low
Fourier block. The negative equation is evaluated at resonance `-n`. -/
theorem sourceAdaptedClosingMap_apply_of_mem (hp : p ≠ ⊤) (φ : CoeffPair p) (N : ℕ)
    (hmem : ∀ positive : Bool, Memℓp (weightedResonantCenterRemainderCoordinate hp SpectralWeight.one
      (sourceWeightedPeriodOne φ) N positive) p) (n : ℤ) :
    (sourceAdaptedClosingMap hp φ N).fst n =
      (if N ≤ n.natAbs then weightedResonantBMinusExtension hp SpectralWeight.one
        (sourceWeightedPeriodOne φ) (-n)
        (weightedResonantDiagonalCenter hp SpectralWeight.one (sourceWeightedPeriodOne φ) (-n))
      else φ.fst n) ∧
    (sourceAdaptedClosingMap hp φ N).snd n =
      (if N ≤ n.natAbs then weightedResonantBPlusExtension hp SpectralWeight.one
        (sourceWeightedPeriodOne φ) n
        (weightedResonantDiagonalCenter hp SpectralWeight.one (sourceWeightedPeriodOne φ) n)
      else φ.snd n) := by
  have hrem := weightedResonantCenterRemainder_apply_of_mem hp SpectralWeight.one
    (sourceWeightedPeriodOne φ) N hmem
  constructor
  · change φ.fst n+(weightedResonantCenterRemainder hp SpectralWeight.one
      (sourceWeightedPeriodOne φ) N).fst (-n) = _
    rw [(hrem (-n)).1]
    by_cases hn : N ≤ n.natAbs <;>
      simp [weightedResonantCenterRemainderCoordinate,hn,mul_neg]
  · change φ.snd n+(weightedResonantCenterRemainder hp SpectralWeight.one
      (sourceWeightedPeriodOne φ) N).snd n = _
    rw [(hrem n).2]
    by_cases hn : N ≤ n.natAbs <;>
      simp [weightedResonantCenterRemainderCoordinate,hn]

end NLS.ZakharovShabat
