import NLS.ZakharovShabat.ResonantCoordinates
import NLS.ZakharovShabat.WeightedDomainPotential

/-!
# The leading Fourier coefficients of the resonant potential

The physical order is `(e_n⁻,e_n⁺)`: column zero contains `φ_+(k+n)` in its
second component, and column one contains `φ_-(k-n)` in its first component.
Thus the source leading terms are `φ^+_{2n}` and `φ^-_{2n}` respectively.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Apply the actual potential to one resonant derivative-domain basis vector. -/
def weightedResonantSource (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (i : Fin 2) : WeightedCoeffPair w.toWeight p :=
  weightedDomainPotential hp w φ (resonantSynthesis w.toWeight.oneDerivative n (Pi.single i 1))

@[simp] theorem weightedResonantSource_zero_fst (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n k : ℤ) :
    (weightedResonantSource hp w φ n 0).fst.val k = 0 := by
  simp [weightedResonantSource, weightedDomainPotential_fst]

@[simp] theorem weightedResonantSource_zero_snd (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n k : ℤ) :
    (weightedResonantSource hp w φ n 0).snd.val k = φ.snd.val (k+n) := by
  simp [weightedResonantSource, weightedDomainPotential_snd, mul_ite]

@[simp] theorem weightedResonantSource_one_fst (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n k : ℤ) :
    (weightedResonantSource hp w φ n 1).fst.val k = φ.fst.val (k-n) := by
  simp [weightedResonantSource, weightedDomainPotential_fst, mul_ite]

@[simp] theorem weightedResonantSource_one_snd (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n k : ℤ) :
    (weightedResonantSource hp w φ n 1).snd.val k = 0 := by
  simp [weightedResonantSource, weightedDomainPotential_snd]

theorem weightedResonantSource_zero_fst_eq_zero (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) : (weightedResonantSource hp w φ n 0).fst = 0 := by
  apply Subtype.ext
  funext k
  simp

theorem weightedResonantSource_one_snd_eq_zero (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) : (weightedResonantSource hp w φ n 1).snd = 0 := by
  apply Subtype.ext
  funext k
  simp

/-- The positive source coefficient is the raw second-component coefficient at `2n`. -/
theorem resonantCoordinates_source_zero (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) :
    resonantCoordinates w.toWeight n (weightedResonantSource hp w φ n 0) = ![0, φ.snd.val (2*n)] := by
  funext i
  fin_cases i <;> simp [two_mul]

/-- The negative source coefficient is the raw first-component coefficient at `-2n`. -/
theorem resonantCoordinates_source_one (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) :
    resonantCoordinates w.toWeight n (weightedResonantSource hp w φ n 1) = ![φ.fst.val (-(2*n)), 0] := by
  funext i
  fin_cases i <;> simp [two_mul, sub_eq_add_neg]

end NLS.ZakharovShabat
