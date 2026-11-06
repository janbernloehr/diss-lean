import NLS.DifferentialPolynomial.IndependentJetVariation
import NLS.DifferentialPolynomial.RiccatiResolventNaturality
import NLS.DifferentialPolynomial.RiccatiResolventVariation
import NLS.ZakharovShabat.NLSRiccatiResolvent

/-! # The constructed Riccati resolvent gives the physical first variation

Independent background and variation jets instantiate the differential-algebra
identity. Their actual smooth periodic evaluation kills its explicit total
derivative and yields the original physical density's integral variation.
-/
noncomputable section
open NLS.DifferentialPolynomial MvPolynomial MeasureTheory
open scoped ContDiff
namespace NLS.ZakharovShabat

def nlsResolventCoefficientA (n : ℕ) : DifferentialPolynomial.Polynomial :=
  PowerSeries.coeff n (riccatiResolventA spatialDerivative (X (false,0)) (X (true,0)))

def nlsResolventCoefficientB (n : ℕ) : DifferentialPolynomial.Polynomial :=
  PowerSeries.coeff n (riccatiResolventB spatialDerivative (X (false,0)) (X (true,0)))

theorem backgroundEmbedding_nlsResolventA (n : ℕ) :
    backgroundEmbedding (nlsResolventCoefficientA n) = PowerSeries.coeff n
      (riccatiResolventA (multiSpatialDerivative (Bool × Bool)) (X ((false,false),0)) (X ((false,true),0))) := by
  have he := congrArg (PowerSeries.coeff n) (map_riccatiResolventA spatialDerivative
    (multiSpatialDerivative (Bool × Bool)) backgroundEmbedding.toRingHom
    backgroundEmbedding_spatialDerivative (X (false,0)) (X (true,0)))
  change backgroundEmbedding (nlsResolventCoefficientA n) = PowerSeries.coeff n
    (riccatiResolventA (multiSpatialDerivative (Bool × Bool))
      (backgroundEmbedding (X (false,0))) (backgroundEmbedding (X (true,0)))) at he
  simpa only [backgroundEmbedding_X] using he

theorem backgroundEmbedding_nlsResolventB (n : ℕ) :
    backgroundEmbedding (nlsResolventCoefficientB n) = PowerSeries.coeff n
      (riccatiResolventB (multiSpatialDerivative (Bool × Bool)) (X ((false,false),0)) (X ((false,true),0))) := by
  have he := congrArg (PowerSeries.coeff n) (map_riccatiResolventB spatialDerivative
    (multiSpatialDerivative (Bool × Bool)) backgroundEmbedding.toRingHom
    backgroundEmbedding_spatialDerivative (X (false,0)) (X (true,0)))
  change backgroundEmbedding (nlsResolventCoefficientB n) = PowerSeries.coeff n
    (riccatiResolventB (multiSpatialDerivative (Bool × Bool))
      (backgroundEmbedding (X (false,0))) (backgroundEmbedding (X (true,0)))) at he
  simpa only [backgroundEmbedding_X] using he

/-- The actual two-field density has the claimed variation modulo a constructed
spatial derivative in the four independent jet families. -/
theorem exists_nlsResolvent_jet_variation (n : ℕ) : ∃ q : VariationPolynomial,
    independentJetVariation (backgroundEmbedding (X (false,0)*nlsRiccatiPolynomial n)) =
      X ((true,false),0)*backgroundEmbedding (nlsResolventCoefficientA n)+
      X ((true,true),0)*backgroundEmbedding (nlsResolventCoefficientB n)-
      multiSpatialDerivative (Bool × Bool) q := by
  have hr : backgroundEmbedding (nlsRiccatiPolynomial n) =
      differentialRiccatiSequence (multiSpatialDerivative (Bool × Bool))
        (X ((false,false),0)) (X ((false,true),0)) n := by
    rw [nlsRiccatiPolynomial_eq_differentialRiccatiSequence]
    have he := map_differentialRiccatiSequence spatialDerivative
      (multiSpatialDerivative (Bool × Bool)) backgroundEmbedding.toRingHom
      backgroundEmbedding_spatialDerivative (X (false,0)) (X (true,0)) n
    change backgroundEmbedding (differentialRiccatiSequence spatialDerivative (X (false,0)) (X (true,0)) n) =
      differentialRiccatiSequence (multiSpatialDerivative (Bool × Bool))
        (backgroundEmbedding (X (false,0))) (backgroundEmbedding (X (true,0))) n at he
    simpa only [backgroundEmbedding_X] using he
  have he := riccati_resolvent_coefficient_variation (multiSpatialDerivative (Bool × Bool))
    independentJetVariation independentJetVariation_commute (X ((false,false),0)) (X ((false,true),0)) n
  refine ⟨PowerSeries.coeff n (PowerSeries.X*
    riccatiResolventB (multiSpatialDerivative (Bool × Bool)) (X ((false,false),0)) (X ((false,true),0))*
    powerSeriesDerivation independentJetVariation
      (differentialRiccatiSeries (multiSpatialDerivative (Bool × Bool))
        (X ((false,false),0)) (X ((false,true),0)))), ?_⟩
  rw [map_mul, backgroundEmbedding_X, hr]
  simpa only [independentJetVariation_background_X (false,0),
    independentJetVariation_background_X (true,0),
    ← backgroundEmbedding_nlsResolventA, ← backgroundEmbedding_nlsResolventB] using he

/-- Actual periodic integration removes the constructed primitive for every
smooth complex pair and arbitrary smooth periodic independent variations. -/
theorem integral_firstVariationDensity_eq_resolvent (a b h k : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hh : ContDiff ℝ ∞ h) (hk : ContDiff ℝ ∞ k)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1)
    (hph : Function.Periodic h 1) (hpk : Function.Periodic k 1) (n : ℕ) :
    (∫ x in (0 : ℝ)..1, firstVariationDensity a b h k (X (false,0)*nlsRiccatiPolynomial n) x) =
      ∫ x in (0 : ℝ)..1, h x*evaluate a b (nlsResolventCoefficientA n) x+
        k x*evaluate a b (nlsResolventCoefficientB n) x := by
  obtain ⟨q,hq⟩ := exists_nlsResolvent_jet_variation n
  have hf (i : Bool × Bool) : ContDiff ℝ ∞ (variationFields a b h k i) := by
    dsimp [variationFields]
    split <;> split <;> assumption
  have hp (i : Bool × Bool) : Function.Periodic (variationFields a b h k i) 1 := by
    dsimp [variationFields]
    split <;> split <;> assumption
  have he (x : ℝ) : firstVariationDensity a b h k (X (false,0)*nlsRiccatiPolynomial n) x =
      h x*evaluate a b (nlsResolventCoefficientA n) x+
      k x*evaluate a b (nlsResolventCoefficientB n) x-
      evaluateMulti (variationFields a b h k) (multiSpatialDerivative (Bool × Bool) q) x := by
    rw [← evaluate_independentJetVariation, hq]
    simp only [evaluateMulti_sub, evaluateMulti_add, evaluateMulti_mul, evaluateMulti_X,
      evaluateMulti_backgroundEmbedding, Pi.sub_apply, Pi.add_apply, Pi.mul_apply,
      iteratedDeriv_zero, variationFields, Bool.false_eq_true, ↓reduceIte]
  simp_rw [he]
  have hi : IntervalIntegrable (fun x => h x*evaluate a b (nlsResolventCoefficientA n) x+
      k x*evaluate a b (nlsResolventCoefficientB n) x) volume 0 1 :=
    ((hh.continuous.mul (continuous_evaluate a b ha hb _)).add
      (hk.continuous.mul (continuous_evaluate a b ha hb _))).intervalIntegrable 0 1
  have hd : IntervalIntegrable
      (evaluateMulti (variationFields a b h k) (multiSpatialDerivative (Bool × Bool) q)) volume 0 1 :=
    (continuous_evaluateMulti _ hf _).intervalIntegrable 0 1
  rw [intervalIntegral.integral_sub hi hd,
    integral_evaluateMulti_spatialDerivative _ hf hp, sub_zero]

end NLS.ZakharovShabat
