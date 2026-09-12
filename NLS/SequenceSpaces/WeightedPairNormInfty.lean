import NLS.SequenceSpaces.PairNormInfty

/-!
# Weighted infinity-exponent pairs with the exact source norm

Raw components are signed pair coefficients as in (1.2). Weighting identifies
this Banach space isometrically with bounded sum-norm pairs. For every real
Sobolev regularity, `toScalarMax` reflects the first sequence to recover the
scalar Fourier convention used by the existing operator and distribution APIs.
-/

noncomputable section
open scoped ENNReal
namespace NLS

/-- Raw signed pairs with the norm `sup_n w(n) (|a(n)| + |b(n)|)`. -/
def WeightedCoeffPairInfty (w : Weight) := WeightedCoeff w ⊤ × WeightedCoeff w ⊤

namespace WeightedCoeffPairInfty
variable (w : Weight)

instance : AddCommGroup (WeightedCoeffPairInfty w) :=
  inferInstanceAs (AddCommGroup (WeightedCoeff w ⊤ × WeightedCoeff w ⊤))
instance : Module ℂ (WeightedCoeffPairInfty w) :=
  inferInstanceAs (Module ℂ (WeightedCoeff w ⊤ × WeightedCoeff w ⊤))

/-- Weight the two signed coefficient sequences before taking their frequencywise sum norm. -/
def weightEquiv : WeightedCoeffPairInfty w ≃ₗ[ℂ] CoeffPairInfty :=
  ((WeightedCoeff.weightEquiv w ⊤).prodCongr (WeightedCoeff.weightEquiv w ⊤)).trans
    CoeffPairInfty.pairEquiv.symm

instance : NormedAddCommGroup (WeightedCoeffPairInfty w) :=
  NormedAddCommGroup.induced _ _ (weightEquiv w).toLinearMap (weightEquiv w).injective
instance : NormedSpace ℂ (WeightedCoeffPairInfty w) :=
  NormedSpace.induced ℂ _ _ (weightEquiv w).toLinearMap

/-- Weighting is an isometry onto the actual unweighted endpoint pair space. -/
def weightIsometry : WeightedCoeffPairInfty w ≃ₗᵢ[ℂ] CoeffPairInfty where
  toLinearEquiv := weightEquiv w
  norm_map' _ := rfl

instance : CompleteSpace (WeightedCoeffPairInfty w) :=
  (weightIsometry w).toIsometryEquiv.completeSpace

@[simp] theorem weightEquiv_apply (u : WeightedCoeffPairInfty w) (n : ℤ) :
    weightEquiv w u n = WithLp.toLp 1 ((w n : ℂ) * u.1.val n, (w n : ℂ) * u.2.val n) := rfl

/-- The exact weighted frequencywise supremum; no component supremum is taken first. -/
theorem norm_eq_ciSup (u : WeightedCoeffPairInfty w) :
    ‖u‖ = ⨆ n : ℤ, w n * (‖u.1.val n‖ + ‖u.2.val n‖) := by
  change ‖weightEquiv w u‖ = _
  rw [CoeffPairInfty.norm_eq_ciSup]
  congr 1
  funext n
  simp only [weightEquiv_apply]
  change ‖(w n : ℂ) * u.1.val n‖ + ‖(w n : ℂ) * u.2.val n‖ = _
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (w.positive n), mul_add]

/-- The unchanged signed raw pair as an algebraic equivalence. -/
def pairEquiv : WeightedCoeffPairInfty w ≃ₗ[ℂ] WeightedCoeff w ⊤ × WeightedCoeff w ⊤ :=
  LinearEquiv.refl ℂ _

/-- The raw maximum norm is bounded by the frequencywise sum norm. -/
theorem norm_pairEquiv_le (u : WeightedCoeffPairInfty w) : ‖pairEquiv w u‖ ≤ ‖u‖ := by
  have h := CoeffPairInfty.norm_toMax_le (weightEquiv w u)
  exact h

/-- Factor two bounds the inverse change of norm for every positive weight. -/
theorem norm_pairEquiv_symm_le (u : WeightedCoeff w ⊤ × WeightedCoeff w ⊤) :
    ‖(pairEquiv w).symm u‖ ≤ 2 * ‖u‖ :=
  CoeffPairInfty.norm_ofPair_le (WeightedCoeff.weightEquiv w ⊤ u.1)
    (WeightedCoeff.weightEquiv w ⊤ u.2)

/-- The existing weighted maximum product has exactly the same complex linear topology. -/
def toMax : WeightedCoeffPairInfty w ≃L[ℂ] WeightedCoeff w ⊤ × WeightedCoeff w ⊤ :=
  (pairEquiv w).toContinuousLinearEquivOfBounds 1 2
    (by intro u; simpa only [one_mul] using norm_pairEquiv_le w u)
    (norm_pairEquiv_symm_le w)

@[simp] theorem toMax_apply (u : WeightedCoeffPairInfty w) : toMax w u = (u.1, u.2) := rfl

@[simp] theorem toMax_symm_apply (u : WeightedCoeff w ⊤ × WeightedCoeff w ⊤) :
    (toMax w).symm u = (u : WeightedCoeffPairInfty w) := rfl

theorem norm_toMax_le (u : WeightedCoeffPairInfty w) : ‖toMax w u‖ ≤ ‖u‖ :=
  norm_pairEquiv_le w u

theorem norm_toMax_symm_le (u : WeightedCoeff w ⊤ × WeightedCoeff w ⊤) :
    ‖(toMax w).symm u‖ ≤ 2 * ‖u‖ := norm_pairEquiv_symm_le w u

/-- Combine signed weighted components in the source norm. -/
def ofPair (a b : WeightedCoeff w ⊤) : WeightedCoeffPairInfty w := (a, b)

@[simp] theorem ofPair_fst (a b : WeightedCoeff w ⊤) : (ofPair w a b).1 = a := rfl
@[simp] theorem ofPair_snd (a b : WeightedCoeff w ⊤) : (ofPair w a b).2 = b := rfl

/-- Equal signed weighted components attain the comparison constant two. -/
theorem norm_diagonal (a : WeightedCoeff w ⊤) :
    ‖ofPair w a a‖ = 2 * ‖a‖ :=
  CoeffPairInfty.norm_diagonal (WeightedCoeff.weightEquiv w ⊤ a)

/-- The dissertation's exact endpoint norm at every real Sobolev regularity. -/
theorem sobolev_norm_eq_ciSup (s : ℝ) (u : WeightedCoeffPairInfty (Weight.sobolev s)) :
    ‖u‖ = ⨆ n : ℤ, (1 + |(n : ℝ)|) ^ s * (‖u.1.val n‖ + ‖u.2.val n‖) :=
  norm_eq_ciSup (Weight.sobolev s) u

/-- Convert the signed first component to scalar Fourier frequencies at real Sobolev regularity. -/
def toScalarMax (s : ℝ) : WeightedCoeffPairInfty (Weight.sobolev s) ≃L[ℂ]
    WeightedCoeff (Weight.sobolev s) ⊤ × WeightedCoeff (Weight.sobolev s) ⊤ :=
  (toMax (Weight.sobolev s)).trans
    ((WeightedCoeff.reflection s).toContinuousLinearEquiv.prodCongr
      (ContinuousLinearEquiv.refl ℂ _))

@[simp] theorem toScalarMax_apply (s : ℝ) (u : WeightedCoeffPairInfty (Weight.sobolev s)) :
    toScalarMax s u = (WeightedCoeff.reflection s u.1, u.2) := rfl

/-- In physical scalar coefficients, the source norm pairs opposite frequencies. -/
theorem sobolev_norm_eq_ciSup_scalar (s : ℝ) (u : WeightedCoeffPairInfty (Weight.sobolev s)) :
    ‖u‖ = ⨆ n : ℤ, (1 + |(n : ℝ)|) ^ s *
      (‖(toScalarMax s u).1.val (-n)‖ + ‖(toScalarMax s u).2.val n‖) := by
  simp only [toScalarMax_apply, WeightedCoeff.reflection_apply, neg_neg]
  exact sobolev_norm_eq_ciSup s u

theorem norm_toScalarMax_le (s : ℝ) (u : WeightedCoeffPairInfty (Weight.sobolev s)) :
    ‖toScalarMax s u‖ ≤ ‖u‖ := by
  simpa only [toScalarMax_apply, toMax_apply, Prod.norm_def, LinearIsometryEquiv.norm_map]
    using norm_toMax_le (Weight.sobolev s) u

theorem norm_toScalarMax_symm_le (s : ℝ)
    (u : WeightedCoeff (Weight.sobolev s) ⊤ × WeightedCoeff (Weight.sobolev s) ⊤) :
    ‖(toScalarMax s).symm u‖ ≤ 2 * ‖u‖ := by
  have h := norm_toMax_symm_le (Weight.sobolev s) ((WeightedCoeff.reflection s).symm u.1, u.2)
  simpa only [Prod.norm_def, LinearIsometryEquiv.norm_map] using! h

end WeightedCoeffPairInfty
end NLS
