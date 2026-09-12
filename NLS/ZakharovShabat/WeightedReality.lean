import NLS.SequenceSpaces.ConjugateReflection
import NLS.ZakharovShabat.WeightedFreePencil

/-!
# Reality types and signed conjugate reflection

The source's `φ*` is physical conjugation followed by component exchange.
The signs `1` and `-1` describe real and imaginary type respectively.
-/

noncomputable section
open scoped ENNReal
namespace NLS

theorem Weight.oneDerivative_neg_eq (w : Weight) (hw : ∀ k, w (-k) = w k) (k : ℤ) :
    w.oneDerivative (-k) = w.oneDerivative k := by simp [hw]

namespace ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Physical conjugation, component exchange, and a sign on the second output. -/
def weightedConjugation (w : Weight) (hw : ∀ k, w (-k) = w k) (ε : ℂ)
    (f : WeightedCoeffPair w p) : WeightedCoeffPair w p :=
  (WeightedCoeffPair.toMax w p).symm
    (WeightedCoeff.conjugateReflection w hw f.snd, ε • WeightedCoeff.conjugateReflection w hw f.fst)

@[simp] theorem weightedConjugation_fst (w : Weight) (hw : ∀ k, w (-k) = w k)
    (ε : ℂ) (f : WeightedCoeffPair w p) (k : ℤ) :
    (weightedConjugation w hw ε f).fst.val k = (starRingEnd ℂ) (f.snd.val (-k)) :=
  WeightedCoeff.conjugateReflection_apply w hw f.snd k

@[simp] theorem weightedConjugation_snd (w : Weight) (hw : ∀ k, w (-k) = w k)
    (ε : ℂ) (f : WeightedCoeffPair w p) (k : ℤ) :
    (weightedConjugation w hw ε f).snd.val k = ε * (starRingEnd ℂ) (f.fst.val (-k)) := by
  change ε * (WeightedCoeff.conjugateReflection w hw f.fst).val k = _
  rw [WeightedCoeff.conjugateReflection_apply]

theorem weightedConjugation_add (w : Weight) (hw : ∀ k, w (-k) = w k)
    (ε : ℂ) (f g : WeightedCoeffPair w p) :
    weightedConjugation w hw ε (f+g) = weightedConjugation w hw ε f + weightedConjugation w hw ε g := by
  apply weightedPair_ext <;> intro k
  · rw [weightedConjugation_fst]
    change (starRingEnd ℂ) (f.snd.val (-k) + g.snd.val (-k)) = _
    simp
  · rw [weightedConjugation_snd]
    change ε * (starRingEnd ℂ) (f.fst.val (-k) + g.fst.val (-k)) = _
    simp [mul_add]

theorem weightedConjugation_sub (w : Weight) (hw : ∀ k, w (-k) = w k)
    (ε : ℂ) (f g : WeightedCoeffPair w p) :
    weightedConjugation w hw ε (f-g) = weightedConjugation w hw ε f - weightedConjugation w hw ε g := by
  apply weightedPair_ext <;> intro k
  · rw [weightedConjugation_fst]
    change (starRingEnd ℂ) (f.snd.val (-k) - g.snd.val (-k)) = _
    simp
  · rw [weightedConjugation_snd]
    change ε * (starRingEnd ℂ) (f.fst.val (-k) - g.fst.val (-k)) = _
    simp [mul_sub]

/-- The physical conjugate transpose of an off-diagonal potential. -/
def weightedPotentialStar (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight p) :
    WeightedCoeffPair w.toWeight p := weightedConjugation w.toWeight w.neg_eq 1 φ

/-- The source reality condition `φ*=εφ`, used with `ε=1` or `ε=-1`. -/
def HasRealitySign (w : SpectralWeight) (ε : ℂ) (φ : WeightedCoeffPair w.toWeight p) : Prop :=
  weightedPotentialStar w φ = ε • φ

/-- The reality condition in raw physical Fourier coefficients. -/
theorem hasRealitySign_iff (w : SpectralWeight) (ε : ℂ) (φ : WeightedCoeffPair w.toWeight p) :
    HasRealitySign w ε φ ↔
      (∀ k, (starRingEnd ℂ) (φ.snd.val (-k)) = ε * φ.fst.val k) ∧
      (∀ k, (starRingEnd ℂ) (φ.fst.val (-k)) = ε * φ.snd.val k) := by
  constructor
  · intro h
    constructor
    · intro k
      simpa [weightedPotentialStar] using congrArg (fun f => f.fst.val k) h
    · intro k
      simpa [weightedPotentialStar] using congrArg (fun f => f.snd.val k) h
  · rintro ⟨h₁, h₂⟩
    apply weightedPair_ext <;> intro k
    · simpa [weightedPotentialStar] using h₁ k
    · simpa [weightedPotentialStar] using h₂ k

end ZakharovShabat
end NLS
