import NLS.ZakharovShabat.SobolevPhysicalJets
import NLS.Fourier.PeriodOneCircleMean
import NLS.DifferentialPolynomial.JetOrderBounds
import Mathlib.Analysis.Analytic.Polynomial

/-! # Analytic evaluation of lower-order differential polynomials on Hˢ

Every jet of order below s has a bounded continuous realization. Higher jets
are assigned zero; the jet-order hypothesis ensures none is used by the
polynomials to which the physical comparison theorem applies.
-/
noncomputable section
open NLS.Fourier NLS.DifferentialPolynomial MvPolynomial
open scoped ContDiff
namespace NLS.ZakharovShabat

def lowerSobolevJet (s : ℕ) (v : Jet) : SobolevSource s →L[ℂ] C(AddCircle (2:ℝ),ℂ) :=
  if h : v.2 < s then
    (hierarchySobolevJetContinuous s v.2 h).comp
      (if v.1 then ContinuousLinearMap.snd ℂ _ _ else ContinuousLinearMap.fst ℂ _ _)
  else 0

def sobolevPolynomialField (s : ℕ) (q : DifferentialPolynomial.Polynomial)
    (ab : SobolevSource s) : C(AddCircle (2:ℝ),ℂ) :=
  MvPolynomial.aeval (fun v => lowerSobolevJet s v ab) q

def sobolevPolynomialMean (s : ℕ) (q : DifferentialPolynomial.Polynomial)
    (ab : SobolevSource s) : ℂ := periodOneCircleMean (sobolevPolynomialField s q ab)

theorem analyticAt_sobolevPolynomialField (s : ℕ) (q : DifferentialPolynomial.Polynomial)
    (ab : SobolevSource s) : AnalyticAt ℂ (sobolevPolynomialField s q) ab :=
  AnalyticAt.aeval_mvPolynomial (fun v => (lowerSobolevJet s v).analyticAt ab) q

theorem analyticAt_sobolevPolynomialMean (s : ℕ) (q : DifferentialPolynomial.Polynomial)
    (ab : SobolevSource s) : AnalyticAt ℂ (sobolevPolynomialMean s q) ab :=
  (periodOneCircleMean.analyticAt _).comp (analyticAt_sobolevPolynomialField s q ab)

/-- Evaluating a circle polynomial at a point commutes with its algebraic evaluation. -/
theorem sobolevPolynomialField_apply (s : ℕ) (q : DifferentialPolynomial.Polynomial)
    (ab : SobolevSource s) (x : ℝ) :
    sobolevPolynomialField s q ab (x : AddCircle (2:ℝ)) =
      MvPolynomial.eval (fun v => lowerSobolevJet s v ab (x : AddCircle (2:ℝ))) q := by
  exact MvPolynomial.comp_aeval_apply (fun v => lowerSobolevJet s v ab) (ContinuousMap.evalAlgHom ℂ ℂ (x : AddCircle (2:ℝ))) q

/-- All assigned jets are unit-periodic on arbitrary Sobolev inputs. -/
theorem lowerSobolevJet_periodic (s : ℕ) (v : Jet) (ab : SobolevSource s) :
    Function.Periodic (fun x : ℝ => lowerSobolevJet s v ab (x : AddCircle (2:ℝ))) 1 := by
  by_cases hv : v.2 < s
  · rw [lowerSobolevJet,dif_pos hv]
    cases h : v.1
    · simp only [Bool.false_eq_true,↓reduceIte,ContinuousLinearMap.comp_apply]
      exact hierarchySobolevJetContinuous_periodic s v.2 hv ab.1
    · simp only [↓reduceIte,ContinuousLinearMap.comp_apply]
      exact hierarchySobolevJetContinuous_periodic s v.2 hv ab.2
  · rw [lowerSobolevJet,dif_neg hv]
    intro x
    rfl

/-- The physical polynomial field is unit-periodic without a smoothness hypothesis. -/
theorem sobolevPolynomialField_periodic (s : ℕ) (q : DifferentialPolynomial.Polynomial)
    (ab : SobolevSource s) :
    Function.Periodic (fun x : ℝ => sobolevPolynomialField s q ab (x : AddCircle (2:ℝ))) 1 := by
  intro x
  change sobolevPolynomialField s q ab ((x+1 : ℝ) : AddCircle (2:ℝ)) =
    sobolevPolynomialField s q ab (x : AddCircle (2:ℝ))
  rw [sobolevPolynomialField_apply,sobolevPolynomialField_apply]
  apply congrArg (fun f : Jet → ℂ => MvPolynomial.eval f q)
  funext v
  exact lowerSobolevJet_periodic s v ab x

/-- The mean is actual integration of the continuous polynomial field on every Hˢ input. -/
theorem sobolevPolynomialMean_eq_physical_integral (s : ℕ) (q : DifferentialPolynomial.Polynomial)
    (ab : SobolevSource s) :
    sobolevPolynomialMean s q ab = ∫ x in (0:ℝ)..1,
      sobolevPolynomialField s q ab (x : AddCircle (2:ℝ)) :=
  periodOneCircleMean_eq_integral _ (sobolevPolynomialField_periodic s q ab)

/-- The lower jets coincide pointwise with the original classical derivatives. -/
theorem lowerSobolevJet_eq_classical (s : ℕ) (ab : SobolevSource s) (a b : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1)
    (haq : ∀ j, ab.1.val j = periodOneCoefficient a j)
    (hbq : ∀ j, ab.2.val j = periodOneCoefficient b j)
    (v : Jet) (hv : v.2 < s) (x : ℝ) :
    lowerSobolevJet s v ab (x : AddCircle (2:ℝ)) =
      iteratedDeriv v.2 (if v.1 then b else a) x := by
  rw [lowerSobolevJet,dif_pos hv]
  cases h : v.1
  · simp only [Bool.false_eq_true,↓reduceIte,ContinuousLinearMap.comp_apply]
    exact congrFun (hierarchySobolevJetContinuous_eq_classical s v.2 hv ab.1 a ha hpa haq) x
  · simp only [↓reduceIte,ContinuousLinearMap.comp_apply]
    exact congrFun (hierarchySobolevJetContinuous_eq_classical s v.2 hv ab.2 b hb hpb hbq) x

/-- Only variables occurring in q are needed for physical comparison. -/
theorem sobolevPolynomialField_eq_classical (s : ℕ) (hs : 1 ≤ s)
    (q : DifferentialPolynomial.Polynomial) (hq : JetOrderLE q (s-1))
    (ab : SobolevSource s) (a b : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1)
    (haq : ∀ j, ab.1.val j = periodOneCoefficient a j)
    (hbq : ∀ j, ab.2.val j = periodOneCoefficient b j) (x : ℝ) :
    sobolevPolynomialField s q ab (x : AddCircle (2:ℝ)) = evaluate a b q x := by
  rw [sobolevPolynomialField_apply]
  change MvPolynomial.eval₂Hom (RingHom.id ℂ) _ q = MvPolynomial.eval₂Hom (RingHom.id ℂ) _ q
  apply MvPolynomial.eval₂Hom_congr' rfl _ rfl
  intro v hv _
  exact lowerSobolevJet_eq_classical s ab a b ha hb hpa hpb haq hbq v
    (by have := hq.vars v hv; omega) x

/-- The bounded polynomial mean is exactly the classical physical integral. -/
theorem sobolevPolynomialMean_eq_integral (s : ℕ) (hs : 1 ≤ s)
    (q : DifferentialPolynomial.Polynomial) (hq : JetOrderLE q (s-1))
    (ab : SobolevSource s) (a b : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1)
    (haq : ∀ j, ab.1.val j = periodOneCoefficient a j)
    (hbq : ∀ j, ab.2.val j = periodOneCoefficient b j) :
    sobolevPolynomialMean s q ab = ∫ x in (0:ℝ)..1, evaluate a b q x := by
  have he := sobolevPolynomialField_eq_classical s hs q hq ab a b ha hb hpa hpb haq hbq
  have hp : Function.Periodic
      (fun x : ℝ => sobolevPolynomialField s q ab (x : AddCircle (2:ℝ))) 1 := by
    intro x
    exact (he (x+1)).trans ((DifferentialPolynomial.periodic_evaluate a b 1 hpa hpb q x).trans (he x).symm)
  rw [sobolevPolynomialMean,periodOneCircleMean_eq_integral _ hp]
  exact intervalIntegral.integral_congr (fun x _ => he x)

end NLS.ZakharovShabat
