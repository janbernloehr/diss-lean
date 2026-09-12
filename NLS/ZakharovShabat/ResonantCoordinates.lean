import NLS.ZakharovShabat.WeightedQEquation

/-!
# Coordinates on the two resonant Fourier modes

Coordinates are ordered by the physical modes `(-n,0)` and `(0,n)`.
Synthesis is available for every weight, including the derivative-domain
weight, so resonant vectors have an explicit domain lift.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Evaluate an unweighted Fourier coefficient continuously in any positive weighted space. -/
def weightedCoefficient (w : Weight) (k : ℤ) : WeightedCoeff w p →L[ℂ] ℂ :=
  ((w k : ℂ)⁻¹) • ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) p k).comp
    (WeightedCoeff.weightIsometry w p).toContinuousLinearEquiv.toContinuousLinearMap)

@[simp] theorem weightedCoefficient_apply (w : Weight) (k : ℤ) (f : WeightedCoeff w p) :
    weightedCoefficient w k f = f.val k := by
  change (w k : ℂ)⁻¹ * ((w k : ℂ) * f.val k) = _
  field_simp [w.complex_ne_zero k]

/-- Insert one Fourier mode with its raw amplitude. -/
def weightedMode (w : Weight) (k : ℤ) : ℂ →L[ℂ] WeightedCoeff w p :=
  (ContinuousLinearMap.id ℂ ℂ).smulRight
    ((WeightedCoeff.weightIsometry w p).symm (lp.single p k (w k : ℂ)))

@[simp] theorem weightedMode_apply (w : Weight) (k : ℤ) (c : ℂ) (j : ℤ) :
    (weightedMode (p := p) w k c).val j = if j = k then c else 0 := by
  change c * ((lp.single p k (w k : ℂ) : Coeff p) j / (w j : ℂ)) = _
  by_cases hj : j = k <;> simp [hj, lp.single_apply, w.complex_ne_zero]

/-- Extract the first `-n` and second `n` Fourier coefficients. -/
def resonantCoordinates (w : Weight) (n : ℤ) : WeightedCoeffPair w p →L[ℂ] (Fin 2 → ℂ) :=
  ContinuousLinearMap.pi (fun i => if i = 0 then
    (weightedCoefficient w (-n)).comp ((ContinuousLinearMap.fst ℂ _ _).comp (WeightedCoeffPair.toMax w p).toContinuousLinearMap)
    else (weightedCoefficient w n).comp ((ContinuousLinearMap.snd ℂ _ _).comp (WeightedCoeffPair.toMax w p).toContinuousLinearMap))

@[simp] theorem resonantCoordinates_zero (w : Weight) (n : ℤ) (f : WeightedCoeffPair w p) :
    resonantCoordinates w n f 0 = f.fst.val (-n) := by simp [resonantCoordinates]
@[simp] theorem resonantCoordinates_one (w : Weight) (n : ℤ) (f : WeightedCoeffPair w p) :
    resonantCoordinates w n f 1 = f.snd.val n := by simp [resonantCoordinates]

/-- Synthesize a pair supported on the two physical resonant modes. -/
def resonantSynthesis (w : Weight) (n : ℤ) : (Fin 2 → ℂ) →L[ℂ] WeightedCoeffPair w p :=
  (WeightedCoeffPair.toMax w p).symm.toContinuousLinearMap.comp
    (((weightedMode w (-n)).comp (ContinuousLinearMap.proj 0)).prod
      ((weightedMode w n).comp (ContinuousLinearMap.proj 1)))

@[simp] theorem resonantSynthesis_fst (w : Weight) (n : ℤ) (c : Fin 2 → ℂ) (k : ℤ) :
    (resonantSynthesis (p := p) w n c).fst.val k = if k = -n then c 0 else 0 := weightedMode_apply _ _ _ _
@[simp] theorem resonantSynthesis_snd (w : Weight) (n : ℤ) (c : Fin 2 → ℂ) (k : ℤ) :
    (resonantSynthesis (p := p) w n c).snd.val k = if k = n then c 1 else 0 := weightedMode_apply _ _ _ _

@[simp] theorem resonantCoordinates_synthesis (w : Weight) (n : ℤ) (c : Fin 2 → ℂ) :
    resonantCoordinates w n (resonantSynthesis (p := p) w n c) = c := by
  funext i
  fin_cases i <;> simp

/-- Synthesis after extraction is the actual resonant projection. -/
theorem resonantSynthesis_coordinates (w : Weight) (n : ℤ) (f : WeightedCoeffPair w p) :
    resonantSynthesis w n (resonantCoordinates w n f) = resonantProjection w n f := by
  apply weightedPair_ext <;> intro k
  · by_cases hk : k = -n <;> simp [hk]
  · by_cases hk : k = n <;> simp [hk]

theorem resonantSynthesis_injective (w : Weight) (n : ℤ) : Function.Injective (resonantSynthesis (p := p) w n) := by
  intro a b hab
  simpa using congrArg (resonantCoordinates w n) hab

@[simp] theorem complementary_resonantSynthesis (w : Weight) (n : ℤ) (c : Fin 2 → ℂ) :
    complementaryProjection w n (resonantSynthesis (p := p) w n c) = 0 := by
  apply weightedPair_ext <;> intro k <;> simp <;> tauto

@[simp] theorem resonantCoordinates_complementary (w : Weight) (n : ℤ) (f : WeightedCoeffPair w p) :
    resonantCoordinates w n (complementaryProjection w n f) = 0 := by
  funext i
  fin_cases i <;> simp

/-- The canonical domain lift has the same coordinates and base coefficients. -/
theorem include_resonantSynthesis (w : Weight) (n : ℤ) (c : Fin 2 → ℂ) :
    weightedDomainInclusion w (resonantSynthesis (p := p) w.oneDerivative n c) = resonantSynthesis w n c := by
  apply weightedPair_ext <;> intro k <;> simp

/-- On the two resonant modes the free pencil is multiplication by `λ-nπ`. -/
theorem pencil_resonantSynthesis (w : Weight) (n : ℤ) (z : ℂ) (c : Fin 2 → ℂ) :
    weightedFreePencil w z (resonantSynthesis (p := p) w.oneDerivative n c) =
      resonantSynthesis w n ((z - (Real.pi : ℂ) * n) • c) := by
  apply weightedPair_ext <;> intro k
  · by_cases hk : k = -n <;> simp [hk, sub_eq_add_neg]
  · by_cases hk : k = n <;> simp [hk]

/-- Applying the pencil preserves the complementary projection. -/
theorem pencil_complementaryProjection (w : Weight) (n : ℤ) (z : ℂ) (f : WeightedDomain w p) :
    weightedFreePencil w z (complementaryProjection w.oneDerivative n f) =
      complementaryProjection w n (weightedFreePencil w z f) := by
  apply weightedPair_ext <;> intro k <;> simp

end NLS.ZakharovShabat
