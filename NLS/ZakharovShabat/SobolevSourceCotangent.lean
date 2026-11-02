import NLS.ZakharovShabat.SobolevSourceSmoothDensity
import NLS.SequenceSpaces.SobolevScalarGradient

/-! # Physical gradients in the opposite Sobolev space

Full Sobolev duality represents each component of an actual source
Fréchet derivative. This retains the unconjugated pairing and the original
period-one coefficient indices, at negative as well as positive order.
-/
noncomputable section
open NLS.Fourier
open scoped ContDiff
namespace NLS.ZakharovShabat

abbrev NegativeScalarSobolev (s : ℕ) := WeightedCoeff (Weight.sobolev (-(s : ℝ))) 2

def hierarchyFieldInjection (s : ℕ) (field : Bool) : ScalarSobolev s →L[ℂ] SobolevSource s :=
  if field then ContinuousLinearMap.inr ℂ _ _ else ContinuousLinearMap.inl ℂ _ _

def hierarchyFieldCotangent (s : ℕ) (field : Bool) :
    (SobolevSource s →L[ℂ] ℂ) →L[ℂ] NegativeScalarSobolev s :=
  (WeightedCoeff.sobolevCotangentCLM (p := 2) (q := 2) (s : ℝ) (by norm_num)).comp
    ((ContinuousLinearMap.compL ℂ (ScalarSobolev s) (SobolevSource s) ℂ).flip
      (hierarchyFieldInjection s field))

theorem hierarchyFieldCotangent_coefficient (s : ℕ) (field : Bool)
    (L : SobolevSource s →L[ℂ] ℂ) (n : ℤ) :
    (hierarchyFieldCotangent s field L).val n =
      L (hierarchyFieldInjection s field
        (WeightedCoeff.ofFinsupp (Weight.sobolev (s : ℝ)) 2 (Finsupp.single (-n) 1))) := by
  change (WeightedCoeff.sobolevCotangentCLM (s : ℝ) (by norm_num)
    (L.comp (hierarchyFieldInjection s field))).val n = _
  rw [WeightedCoeff.sobolevCotangentCLM_apply, WeightedCoeff.sobolevCotangent_val]
  rfl

def hierarchyWeakGradient (s : ℕ) (F : SobolevSource s → ℂ) (ab : SobolevSource s) :
    NegativeScalarSobolev s × NegativeScalarSobolev s :=
  (hierarchyFieldCotangent s false (fderiv ℂ F ab), hierarchyFieldCotangent s true (fderiv ℂ F ab))

theorem analyticAt_hierarchyWeakGradient (s : ℕ) (F : SobolevSource s → ℂ)
    (ab : SobolevSource s) (hF : AnalyticAt ℂ F ab) :
    AnalyticAt ℂ (hierarchyWeakGradient s F) ab :=
  (((hierarchyFieldCotangent s false).analyticAt _).comp hF.fderiv).prod
    (((hierarchyFieldCotangent s true).analyticAt _).comp hF.fderiv)

/-- The opposite-order gradient represents the entire actual differential. -/
theorem hierarchyWeakGradient_represents (s : ℕ) (F : SobolevSource s → ℂ)
    (ab h : SobolevSource s) :
    WeightedCoeff.sobolevBilinearPairing (s : ℝ) h.1 (hierarchyWeakGradient s F ab).1 +
      WeightedCoeff.sobolevBilinearPairing (s : ℝ) h.2 (hierarchyWeakGradient s F ab).2 =
        fderiv ℂ F ab h := by
  have h1 := WeightedCoeff.sobolevBilinearPairing_sobolevCotangent (p := 2) (q := 2)
    (s : ℝ) (by norm_num) ((fderiv ℂ F ab).comp (hierarchyFieldInjection s false)) h.1
  have h2 := WeightedCoeff.sobolevBilinearPairing_sobolevCotangent (p := 2) (q := 2)
    (s : ℝ) (by norm_num) ((fderiv ℂ F ab).comp (hierarchyFieldInjection s true)) h.2
  rw [← WeightedCoeff.sobolevCotangentCLM_apply] at h1 h2
  change WeightedCoeff.sobolevBilinearPairing (s : ℝ) h.1
    (hierarchyFieldCotangent s false (fderiv ℂ F ab)) = fderiv ℂ F ab (h.1,0) at h1
  change WeightedCoeff.sobolevBilinearPairing (s : ℝ) h.2
    (hierarchyFieldCotangent s true (fderiv ℂ F ab)) = fderiv ℂ F ab (0,h.2) at h2
  change WeightedCoeff.sobolevBilinearPairing (s : ℝ) h.1
      (hierarchyFieldCotangent s false (fderiv ℂ F ab)) +
    WeightedCoeff.sobolevBilinearPairing (s : ℝ) h.2
      (hierarchyFieldCotangent s true (fderiv ℂ F ab)) = _
  rw [h1,h2, ← map_add]
  simp

private theorem integral_polynomial_single (f : ℝ → ℂ) (n : ℤ) :
    (∫ x in (0 : ℝ)..1, polynomial (Finsupp.single (-n) 1) x*f x) =
      periodOneCoefficient f n := by
  rw [periodOneCoefficient, ← unitFourierCoefficient_eq_fourierCoeffOn]
  unfold unitFourierCoefficient
  apply intervalIntegral.integral_congr
  intro x _
  simp [polynomial, Finsupp.sum, mul_comm]

/-- Smooth first variations fix every physical gradient coefficient. The
representative itself is constructed by full duality, not by this hypothesis. -/
theorem hierarchyFieldCotangent_eq_classical (s : ℕ) (field : Bool)
    (L : SobolevSource s →L[ℂ] ℂ) (g : ℝ → ℂ)
    (hL : ∀ (h : ScalarSobolev s) (f : ℝ → ℂ), ContDiff ℝ ∞ f → Function.Periodic f 1 →
      (∀ j, h.val j = periodOneCoefficient f j) →
      L (hierarchyFieldInjection s field h) = ∫ x in (0 : ℝ)..1, f x*g x) (n : ℤ) :
    (hierarchyFieldCotangent s field L).val n = periodOneCoefficient g n := by
  rw [hierarchyFieldCotangent_coefficient]
  rw [hL _ (polynomial (Finsupp.single (-n) 1)) (contDiff_source_polynomial _)
    (periodic_source_polynomial _) (fun j => by
      simp only [WeightedCoeff.ofFinsupp_apply, periodOneCoefficient_source_polynomial])]
  exact integral_polynomial_single g n

theorem scalarCotangent_eq_classical (s : ℕ) (L : ScalarSobolev s →L[ℂ] ℂ) (g : ℝ → ℂ)
    (hL : ∀ (h : ScalarSobolev s) (f : ℝ → ℂ), ContDiff ℝ ∞ f → Function.Periodic f 1 →
      (∀ j, h.val j = periodOneCoefficient f j) → L h = ∫ x in (0 : ℝ)..1, f x*g x) (n : ℤ) :
    (WeightedCoeff.sobolevCotangentCLM (p := 2) (q := 2) (s : ℝ) (by norm_num) L).val n =
      periodOneCoefficient g n := by
  rw [WeightedCoeff.sobolevCotangentCLM_apply, WeightedCoeff.sobolevCotangent_val]
  rw [hL _ (polynomial (Finsupp.single (-n) 1)) (contDiff_source_polynomial _)
    (periodic_source_polynomial _) (fun j => by
      simp only [WeightedCoeff.ofFinsupp_apply, periodOneCoefficient_source_polynomial])]
  exact integral_polynomial_single g n

end NLS.ZakharovShabat
