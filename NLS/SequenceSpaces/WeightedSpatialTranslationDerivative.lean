import NLS.SequenceSpaces.SpatialTranslation
import NLS.SequenceSpaces.PhaseFlowDerivative

/-! Strong differentiation of actual weighted Fourier translations at every
finite Banach exponent. The generator-domain condition retains the exact
physical frequency scale; no bounded-frequency assumption is used. -/
noncomputable section
open Complex
open scoped ENNReal ComplexConjugate
namespace NLS.WeightedCoeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem spatialTranslation_zero (w : Weight) (c : ℝ) (a : WeightedCoeff w p) :
    spatialTranslation w c 0 a=a := phaseFlow_zero w _ a

theorem spatialTranslation_add (w : Weight) (c t s : ℝ) (a : WeightedCoeff w p) :
    spatialTranslation w c t (spatialTranslation w c s a)=spatialTranslation w c (t+s) a :=
  phaseFlow_add w _ t s a

theorem continuous_spatialTranslation (w : Weight) (hp : p ≠ ⊤) (c : ℝ) :
    Continuous (fun x : ℝ × WeightedCoeff w p => spatialTranslation w c x.1 x.2) :=
  continuous_phaseFlow w hp _

/-- The actual conjugate-reflection physical real form is preserved. -/
theorem spatialTranslation_real (w : Weight) (c t : ℝ) (a : WeightedCoeff w p)
    (ha : ∀ k : ℤ, a.val (-k)=conj (a.val k)) :
    ∀ k : ℤ, (spatialTranslation w c t a).val (-k)=conj ((spatialTranslation w c t a).val k) := by
  intro k
  rw [spatialTranslation_apply,spatialTranslation_apply,ha,map_mul,← Complex.exp_conj]
  simp

/-- The weighted generator domain suffices for a strong derivative. -/
theorem hasDerivAt_spatialTranslation (w : Weight) (hp : p ≠ ⊤) (c : ℝ)
    (a v : WeightedCoeff w p) (hv : ∀ n : ℤ, v.val n=I*(c*n:ℝ)*a.val n) (t : ℝ) :
    HasDerivAt (fun r => spatialTranslation w c r a) (spatialTranslation w c t v) t := by
  have hd := Coeff.hasDerivAt_phaseFlow hp (fun n => c*n) (weightIsometry w p a)
    (weightIsometry w p v) (fun n => by
      change (w n:ℂ)*v.val n=I*(c*n:ℝ)*((w n:ℂ)*a.val n)
      rw [hv]
      ring) t
  exact (((weightIsometry w p).symm.toContinuousLinearEquiv.toContinuousLinearMap).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hd

end NLS.WeightedCoeff
