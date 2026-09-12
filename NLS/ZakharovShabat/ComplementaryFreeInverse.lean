import NLS.ZakharovShabat.ComplementaryStrip
import NLS.ZakharovShabat.WeightedFreePencil

/-!
# The complementary free inverse, including the resonant lattice point

The inverse removes the two resonant coordinates and maps into the actual
weighted one-derivative domain. Multiplication by the free pencil in either
order gives precisely the complementary projection.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The nonresonant reciprocal as a bounded scalar map on the weighted base. -/
def complementaryScalar (w : Weight) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n) (b : Bool) :
    WeightedCoeff w p →L[ℂ] WeightedCoeff w p :=
  WeightedCoeff.weightedMultiplierCLM w w (fun k => complementarySymbol n z (freeFrequency b k)) 1 zero_le_one
    (fun k => by simpa using mul_le_mul_of_nonneg_left (norm_complementarySymbol_le hz (freeFrequency b k)) (w.positive k).le)

@[simp] theorem complementaryScalar_apply (w : Weight) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (b : Bool) (a : WeightedCoeff w p) (k : ℤ) :
    (complementaryScalar w n z hz b a).val k = complementarySymbol n z (freeFrequency b k) * a.val k := rfl

theorem norm_complementaryScalar_le (w : Weight) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (b : Bool) (a : WeightedCoeff w p) : ‖complementaryScalar w n z hz b a‖ ≤ ‖a‖ := by
  simpa only [one_mul] using! WeightedCoeff.norm_weightedMultiplier_le w w
    (fun k => complementarySymbol n z (freeFrequency b k)) 1 zero_le_one
    (fun k => by simpa using mul_le_mul_of_nonneg_left (norm_complementarySymbol_le hz (freeFrequency b k)) (w.positive k).le) a

/-- The same inverse gains one derivative in the weighted space. -/
def complementaryScalarDomain (w : Weight) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n) (b : Bool) :
    WeightedCoeff w p →L[ℂ] WeightedCoeff w.oneDerivative p :=
  WeightedCoeff.weightedMultiplierCLM w w.oneDerivative
    (fun k => complementarySymbol n z (freeFrequency b k)) (complementaryDomainBound z)
    (complementaryDomainBound_nonneg z) (fun k => by
      have h := mul_le_mul_of_nonneg_left (weighted_complementarySymbol_le hz (freeFrequency b k)) (w.positive k).le
      simpa only [abs_freeFrequency, Weight.oneDerivative_apply, mul_assoc, mul_comm (w k)] using h)

@[simp] theorem complementaryScalarDomain_apply (w : Weight) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (b : Bool) (a : WeightedCoeff w p) (k : ℤ) :
    (complementaryScalarDomain w n z hz b a).val k = complementarySymbol n z (freeFrequency b k) * a.val k := rfl

/-- Quantitative gain of one derivative for each scalar component. -/
theorem norm_complementaryScalarDomain_le (w : Weight) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (b : Bool) (a : WeightedCoeff w p) :
    ‖complementaryScalarDomain w n z hz b a‖ ≤ complementaryDomainBound z * ‖a‖ := by
  apply WeightedCoeff.norm_weightedMultiplier_le
  · exact complementaryDomainBound_nonneg z
  · intro k
    have h := mul_le_mul_of_nonneg_left (weighted_complementarySymbol_le hz (freeFrequency b k)) (w.positive k).le
    simpa only [abs_freeFrequency, Weight.oneDerivative_apply, mul_assoc, mul_comm (w k)] using h

/-- Base-space realization of `A_λ⁻¹ Q_n` in the source's pair norm. -/
def complementaryFreeInverse (w : Weight) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n) :
    WeightedCoeffPair w p →L[ℂ] WeightedCoeffPair w p :=
  WeightedCoeffPair.mapComponents w w (complementaryScalar w n z hz true) (complementaryScalar w n z hz false)

/-- Domain-valued realization of `A_λ⁻¹ Q_n`. -/
def complementaryFreeDomainInverse (w : Weight) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n) :
    WeightedCoeffPair w p →L[ℂ] WeightedDomain w p :=
  WeightedCoeffPair.mapComponents w w.oneDerivative
    (complementaryScalarDomain w n z hz true) (complementaryScalarDomain w n z hz false)

@[simp] theorem complementaryFreeInverse_fst (w : Weight) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (a : WeightedCoeffPair w p) (k : ℤ) :
    (complementaryFreeInverse w n z hz a).fst.val k = complementarySymbol n z (-k) * a.fst.val k := rfl
@[simp] theorem complementaryFreeInverse_snd (w : Weight) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (a : WeightedCoeffPair w p) (k : ℤ) :
    (complementaryFreeInverse w n z hz a).snd.val k = complementarySymbol n z k * a.snd.val k := rfl
@[simp] theorem complementaryFreeDomainInverse_fst (w : Weight) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (a : WeightedCoeffPair w p) (k : ℤ) :
    (complementaryFreeDomainInverse w n z hz a).fst.val k = complementarySymbol n z (-k) * a.fst.val k := rfl
@[simp] theorem complementaryFreeDomainInverse_snd (w : Weight) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (a : WeightedCoeffPair w p) (k : ℤ) :
    (complementaryFreeDomainInverse w n z hz a).snd.val k = complementarySymbol n z k * a.snd.val k := rfl

/-- The domain inverse includes to precisely the bounded base inverse. -/
theorem include_complementaryFreeDomainInverse (w : Weight) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (a : WeightedCoeffPair w p) :
    weightedDomainInclusion w (complementaryFreeDomainInverse w n z hz a) = complementaryFreeInverse w n z hz a := by
  apply weightedPair_ext <;> intro k <;> simp

/-- The complementary inverse has uniform norm at most one on the entire strip. -/
theorem norm_complementaryFreeInverse_le (hp : p ≠ ⊤) (w : Weight) (n : ℤ) (z : ℂ)
    (hz : z ∈ resonantStrip n) (a : WeightedCoeffPair w p) : ‖complementaryFreeInverse w n z hz a‖ ≤ ‖a‖ := by
  simpa only [one_mul] using! WeightedCoeffPair.norm_mapComponents_le hp w w
    (complementaryScalar w n z hz true) (complementaryScalar w n z hz false) zero_le_one
    (fun a => by simpa using norm_complementaryScalar_le w n z hz true a)
    (fun a => by simpa using norm_complementaryScalar_le w n z hz false a) a

/-- The explicit domain bound is independent of the weight and the strip index. -/
theorem norm_complementaryFreeDomainInverse_le (hp : p ≠ ⊤) (w : Weight) (n : ℤ) (z : ℂ)
    (hz : z ∈ resonantStrip n) (a : WeightedCoeffPair w p) :
    ‖complementaryFreeDomainInverse w n z hz a‖ ≤ complementaryDomainBound z * ‖a‖ := by
  exact WeightedCoeffPair.norm_mapComponents_le hp w w.oneDerivative
    (complementaryScalarDomain w n z hz true) (complementaryScalarDomain w n z hz false)
    (complementaryDomainBound_nonneg z) (norm_complementaryScalarDomain_le w n z hz true)
    (norm_complementaryScalarDomain_le w n z hz false) a

private theorem first_denominator_mul (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n) (k : ℤ) :
    (z + (Real.pi : ℂ) * k) * complementarySymbol n z (-k) = if k = -n then 0 else 1 := by
  simpa only [Int.cast_neg, mul_neg, sub_neg_eq_add, neg_eq_iff_eq_neg] using denominator_mul_complementarySymbol hz (-k)

/-- Applying the free pencil after the domain inverse gives `Q_n`. -/
theorem pencil_complementaryFreeDomainInverse (w : Weight) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (a : WeightedCoeffPair w p) :
    weightedFreePencil w z (complementaryFreeDomainInverse w n z hz a) = complementaryProjection w n a := by
  apply weightedPair_ext <;> intro k
  · rw [weightedFreePencil_fst, complementaryFreeDomainInverse_fst, ← mul_assoc,
      first_denominator_mul n z hz k, complementaryProjection_fst]
    split_ifs <;> simp
  · rw [weightedFreePencil_snd, complementaryFreeDomainInverse_snd, ← mul_assoc,
      denominator_mul_complementarySymbol hz, complementaryProjection_snd]
    split_ifs <;> simp

/-- Applying the inverse after the free pencil gives the domain's `Q_n`. -/
theorem complementaryFreeDomainInverse_pencil (w : Weight) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (a : WeightedDomain w p) :
    complementaryFreeDomainInverse w n z hz (weightedFreePencil w z a) = complementaryProjection w.oneDerivative n a := by
  apply weightedPair_ext <;> intro k
  · rw [complementaryFreeDomainInverse_fst, weightedFreePencil_fst, ← mul_assoc,
      mul_comm (complementarySymbol n z (-k)), first_denominator_mul n z hz k, complementaryProjection_fst]
    split_ifs <;> simp
  · rw [complementaryFreeDomainInverse_snd, weightedFreePencil_snd, ← mul_assoc,
      mul_comm (complementarySymbol n z k), denominator_mul_complementarySymbol hz, complementaryProjection_snd]
    split_ifs <;> simp

/-- The inverse takes values in the complementary domain. -/
theorem complementaryFreeDomainInverse_nonresonant (w : Weight) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (a : WeightedCoeffPair w p) :
    complementaryProjection w.oneDerivative n (complementaryFreeDomainInverse w n z hz a) = complementaryFreeDomainInverse w n z hz a := by
  apply (complementaryProjection_eq_self_iff _ _ _).mpr
  simp

/-- The domain inverse is the unique complementary solution of the projected equation. -/
theorem complementaryFreeDomainInverse_unique (w : Weight) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (a : WeightedCoeffPair w p) (u : WeightedDomain w p)
    (hu : complementaryProjection w.oneDerivative n u = u)
    (he : weightedFreePencil w z u = complementaryProjection w n a) :
    u = complementaryFreeDomainInverse w n z hz a := by
  have h := congrArg (complementaryFreeDomainInverse w n z hz) he
  rw [complementaryFreeDomainInverse_pencil, hu] at h
  rw [h]
  apply weightedPair_ext <;> intro k
  · by_cases hk : k = -n <;> simp [hk, complementarySymbol]
  · by_cases hk : k = n <;> simp [hk, complementarySymbol]

end NLS.ZakharovShabat
