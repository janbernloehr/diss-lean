import NLS.ZakharovShabat.SobolevDifferentialPolynomial
import NLS.ZakharovShabat.NLSOddHamiltonianReducedPolynomial
import NLS.SequenceSpaces.ConjugateDuality

/-! # Physical odd Hamiltonians on the sharp integer Sobolev scale

The mth-derivative pairing and the reduced polynomial mean define H_(2m+1)
on the full complex H^m space. The definition is entire analytic and uses no
spectral actions. It agrees with the classical hierarchy on smooth fields.
-/
noncomputable section
open NLS.Fourier NLS.DifferentialPolynomial Set MeasureTheory
open scoped ContDiff
namespace NLS.ZakharovShabat

/-- A single reduced physical polynomial, chosen independently of all fields. -/
def nlsOddReducedPolynomial (m : ℕ) (hm : 1 ≤ m) : DifferentialPolynomial.Polynomial :=
  Classical.choose (exists_classicalNLSHamiltonian_odd_reduced_polynomial m hm)

theorem nlsOddReducedPolynomial_order (m : ℕ) (hm : 1 ≤ m) :
    JetOrderLE (nlsOddReducedPolynomial m hm) (m-1) :=
  (Classical.choose_spec (exists_classicalNLSHamiltonian_odd_reduced_polynomial m hm)).1

theorem nlsOddReducedPolynomial_classical (m : ℕ) (hm : 1 ≤ m)
    (a b : ℝ → ℂ) (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1) :
    classicalNLSHamiltonian a b (2*m+1) = ∫ x in (0:ℝ)..1,
      iteratedDeriv m a x*iteratedDeriv m b x+evaluate a b (nlsOddReducedPolynomial m hm) x :=
  (Classical.choose_spec (exists_classicalNLSHamiltonian_odd_reduced_polynomial m hm)).2.2.2
    a b ha hb hpa hpb

/-- The physical leading pairing of mth derivatives, including the L² endpoint. -/
def sobolevOddKinetic (m : ℕ) (ab : SobolevSource m) : ℂ :=
  Coeff.dualPairing (Coeff.reflection (hierarchySobolevJetL2 m m le_rfl ab.1))
    (hierarchySobolevJetL2 m m le_rfl ab.2)

/-- H_(2m+1) on complex H^m, defined by the reduced physical polynomial. -/
def sobolevOddHamiltonian (m : ℕ) (hm : 1 ≤ m) (ab : SobolevSource m) : ℂ :=
  sobolevOddKinetic m ab+sobolevPolynomialMean m (nlsOddReducedPolynomial m hm) ab

theorem analyticAt_sobolevOddKinetic (m : ℕ) (ab : SobolevSource m) :
    AnalyticAt ℂ (sobolevOddKinetic m) ab := by
  let A : SobolevSource m →L[ℂ] Coeff 2 :=
    (Coeff.reflection.toContinuousLinearEquiv.toContinuousLinearMap.comp
      (hierarchySobolevJetL2 m m le_rfl)).comp (ContinuousLinearMap.fst ℂ _ _)
  let B : SobolevSource m →L[ℂ] Coeff 2 :=
    (hierarchySobolevJetL2 m m le_rfl).comp (ContinuousLinearMap.snd ℂ _ _)
  exact (Coeff.dualPairing.analyticAt_bilinear (A ab,B ab)).comp (f := fun cd => (A cd,B cd))
    ((A.analyticAt ab).prod (B.analyticAt ab))

/-- The physical odd Hamiltonian is analytic on every complex H^m input. -/
theorem analyticAt_sobolevOddHamiltonian (m : ℕ) (hm : 1 ≤ m) (ab : SobolevSource m) :
    AnalyticAt ℂ (sobolevOddHamiltonian m hm) ab :=
  (analyticAt_sobolevOddKinetic m ab).add
    (analyticAt_sobolevPolynomialMean m (nlsOddReducedPolynomial m hm) ab)

theorem continuous_sobolevOddHamiltonian (m : ℕ) (hm : 1 ≤ m) :
    Continuous (sobolevOddHamiltonian m hm) :=
  continuous_iff_continuousAt.mpr fun ab => (analyticAt_sobolevOddHamiltonian m hm ab).continuousAt

/-- The leading Fourier mean is absolutely convergent at precisely H^m regularity. -/
theorem summable_norm_sobolevOddKinetic (m : ℕ) (ab : SobolevSource m) :
    Summable (fun j : ℤ => ‖((2*Complex.I*(Real.pi:ℂ)*(-j))^m*ab.1.val (-j))*
      ((2*Complex.I*(Real.pi:ℂ)*j)^m*ab.2.val j)‖) := by
  simpa only [Coeff.reflection_apply,hierarchySobolevJetL2_apply,Int.cast_neg] using
    Coeff.summable_norm_dualPairing (Coeff.reflection (hierarchySobolevJetL2 m m le_rfl ab.1))
      (hierarchySobolevJetL2 m m le_rfl ab.2)

/-- Bilinear Parseval identifies the leading term with actual smooth derivatives. -/
theorem sobolevOddKinetic_eq_integral (m : ℕ) (ab : SobolevSource m) (a b : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1)
    (haq : ∀ j, ab.1.val j = periodOneCoefficient a j)
    (hbq : ∀ j, ab.2.val j = periodOneCoefficient b j) :
    sobolevOddKinetic m ab = ∫ x in (0:ℝ)..1, iteratedDeriv m a x*iteratedDeriv m b x := by
  have h := tsum_bilinear_unitFourierCoefficient
    (contDiff_iteratedDeriv_of_smooth a ha m).continuous (contDiff_iteratedDeriv_of_smooth b hb m).continuous
  have he (f : ℝ → ℂ) (j : ℤ) : unitFourierCoefficient f j = periodOneCoefficient f j :=
    unitFourierCoefficient_eq_fourierCoeffOn f j
  simp only [he,periodOneCoefficient_iteratedDeriv_of_smooth a ha hpa,
    periodOneCoefficient_iteratedDeriv_of_smooth b hb hpb] at h
  simpa only [sobolevOddKinetic,Coeff.dualPairing_apply,Coeff.reflection_apply,
    hierarchySobolevJetL2_apply,haq,hbq] using h

/-- The sharp Sobolev extension is the original classical physical Hamiltonian
for every smooth periodic source, at every positive odd order. -/
theorem sobolevOddHamiltonian_eq_classical (m : ℕ) (hm : 1 ≤ m)
    (ab : SobolevSource m) (a b : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1)
    (haq : ∀ j, ab.1.val j = periodOneCoefficient a j)
    (hbq : ∀ j, ab.2.val j = periodOneCoefficient b j) :
    sobolevOddHamiltonian m hm ab = classicalNLSHamiltonian a b (2*m+1) := by
  rw [sobolevOddHamiltonian,sobolevOddKinetic_eq_integral m ab a b ha hb hpa hpb haq hbq,
    sobolevPolynomialMean_eq_integral m hm _ (nlsOddReducedPolynomial_order m hm) ab a b ha hb hpa hpb haq hbq,
    nlsOddReducedPolynomial_classical m hm a b ha hb hpa hpb]
  symm
  apply intervalIntegral.integral_add
  · exact ((contDiff_iteratedDeriv_of_smooth a ha m).continuous.mul
      (contDiff_iteratedDeriv_of_smooth b hb m).continuous).intervalIntegrable 0 1
  · exact (DifferentialPolynomial.continuous_evaluate a b ha hb _).intervalIntegrable 0 1

end NLS.ZakharovShabat
