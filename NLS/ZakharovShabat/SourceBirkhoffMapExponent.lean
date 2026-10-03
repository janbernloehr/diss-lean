import NLS.ZakharovShabat.SourceBirkhoffProposition17_1
import NLS.SequenceSpaces.RealCoeffExponent

/-! # Compatibility of the full real Birkhoff sequence maps

The rectangular-coordinate compatibility extends to the full real
sequence map, even for independently constructed normalized families.
-/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
namespace SourceBirkhoffMapComplexData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}
  {hq : q ≠ ⊤} {hq1 : 1 < q} {V₀ C V : Set (CoeffPair q)}
  {t : (k : ℤ) → CoeffPair q → DeletedCoeff q k}

/-- The actual real Birkhoff map commutes with increasing the exponent. -/
theorem real_map_exponent
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (E : SourceBirkhoffMapComplexData hq hq1 V₀ C V t)
    (hpq : p ≤ q) (φ : realTypeSourceSubmodule p) :
    ((RealCoeff.exponentInclusion hpq).prodMap (RealCoeff.exponentInclusion hpq))
      (sourceRealBirkhoffMap hp hp1 s φ) =
        sourceRealBirkhoffMap hq hq1 t (realTypeSourceExponentInclusion hpq φ) := by
  have hc (n : ℤ) := D.angular.birkhoffXY_real_exponent E.angular W V
    D.source_open E.source_open D.source_subset E.source_subset hpq n φ
    (D.real_subset φ.property) (E.real_subset (realTypeSourceExponentInclusion hpq φ).property)
  have hd (n : ℤ) := D.coordinates φ.val (D.real_subset φ.property) n
  have he (n : ℤ) := E.coordinates _ (E.real_subset (realTypeSourceExponentInclusion hpq φ).property) n
  apply Prod.ext <;> ext n
  · change ((sourceBirkhoffMap hp hp1 s φ.val).1 n).re = _
    rw [(hd n).1]
    exact congrArg Complex.re ((hc n).1.trans (he n).1.symm)
  · change ((sourceBirkhoffMap hp hp1 s φ.val).2 n).re = _
    rw [(hd n).2]
    exact congrArg Complex.re ((hc n).2.trans (he n).2.symm)

/-- Global injectivity at a larger exponent implies it at a smaller one.
The injectivity premise remains explicit until the Hilbert theorem is proved. -/
theorem real_map_injective_of_exponent
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (E : SourceBirkhoffMapComplexData hq hq1 V₀ C V t)
    (hpq : p ≤ q) (hinj : Function.Injective (sourceRealBirkhoffMap hq hq1 t)) :
    Function.Injective (sourceRealBirkhoffMap hp hp1 s) := by
  intro φ ψ heq
  have he : sourceRealBirkhoffMap hq hq1 t (realTypeSourceExponentInclusion hpq φ) =
      sourceRealBirkhoffMap hq hq1 t (realTypeSourceExponentInclusion hpq ψ) :=
    (D.real_map_exponent E hpq φ).symm.trans
      ((congrArg ((RealCoeff.exponentInclusion hpq).prodMap (RealCoeff.exponentInclusion hpq)) heq).trans
        (D.real_map_exponent E hpq ψ))
  apply Subtype.ext
  apply CoeffPair.exponentInclusion_injective hpq
  exact congrArg Subtype.val (hinj he)

end SourceBirkhoffMapComplexData
end NLS.ZakharovShabat
