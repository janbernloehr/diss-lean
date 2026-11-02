import NLS.ZakharovShabat.SobolevPolynomialL2
import NLS.ZakharovShabat.SobolevSourceSmoothDensity
import NLS.DifferentialPolynomial.SmoothVariation
import NLS.Fourier.CircleUnitCoefficients
import NLS.SequenceSpaces.ConjugateDuality

/-! # Physical first variations of endpoint Sobolev polynomial integrals

The partial jet derivatives are actual L² fields. Pairing them with the
corresponding weak derivatives of a Sobolev direction constructs a bounded
covector. Smooth density identifies it with the actual Fréchet derivative.
-/
noncomputable section
open NLS.Fourier NLS.DifferentialPolynomial MvPolynomial MeasureTheory Set
open scoped ContDiff
namespace NLS.ZakharovShabat

def sobolevPolynomialL2Mean (s : ℕ) (p : DifferentialPolynomial.Polynomial)
    (ab : SobolevSource s) : ℂ :=
  circlePrimitiveCLM 1 (by constructor <;> norm_num) (sobolevPolynomialL2 s p ab)

theorem analyticAt_sobolevPolynomialL2Mean (s : ℕ) (p : DifferentialPolynomial.Polynomial)
    (ab : SobolevSource s) : AnalyticAt ℂ (sobolevPolynomialL2Mean s p) ab :=
  ((circlePrimitiveCLM 1 (by constructor <;> norm_num)).analyticAt _).comp
    (analyticAt_sobolevPolynomialL2 s p ab)

theorem sobolevPolynomialL2Mean_eq_classical (s : ℕ) (hs : 1 ≤ s)
    (p : DifferentialPolynomial.Polynomial) (hp : DerivativeOrderLE p (2*(s : ℤ)-1))
    (hj : JetOrderLE p s) (ab : SobolevSource s) (a b : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1)
    (haq : ∀ j, ab.1.val j = periodOneCoefficient a j)
    (hbq : ∀ j, ab.2.val j = periodOneCoefficient b j) :
    sobolevPolynomialL2Mean s p ab = ∫ x in (0 : ℝ)..1, evaluate a b p x := by
  change (∫ x in (0 : ℝ)..1, circlePullback _ x) = _
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  exact integral_congr_ae
    (sobolevPolynomialL2_eq_classical_of_jetOrder s hs p hp hj ab a b ha hb hpa hpb haq hbq)

def sobolevPolynomialPartialCoefficients (s : ℕ) (p : DifferentialPolynomial.Polynomial)
    (v : Jet) (ab : SobolevSource s) : Coeff 2 :=
  circleUnitCoefficients (sobolevPolynomialL2 s (pderiv v p) ab)

theorem analyticAt_sobolevPolynomialPartialCoefficients (s : ℕ)
    (p : DifferentialPolynomial.Polynomial) (v : Jet) (ab : SobolevSource s) :
    AnalyticAt ℂ (sobolevPolynomialPartialCoefficients s p v) ab :=
  (circleUnitCoefficients.analyticAt _).comp (analyticAt_sobolevPolynomialL2 s _ ab)

theorem sobolevPolynomialPartialCoefficients_eq_classical (s : ℕ) (hs : 1 ≤ s)
    (p : DifferentialPolynomial.Polynomial) (hp : DerivativeOrderLE p (2*(s : ℤ)-1))
    (hj : JetOrderLE p s) (v : Jet) (ab : SobolevSource s) (a b : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1)
    (haq : ∀ j, ab.1.val j = periodOneCoefficient a j)
    (hbq : ∀ j, ab.2.val j = periodOneCoefficient b j) (j : ℤ) :
    sobolevPolynomialPartialCoefficients s p v ab j =
      periodOneCoefficient (evaluate a b (pderiv v p)) j :=
  circleUnitCoefficients_eq_classical _ _
    (sobolevPolynomialL2_eq_classical_of_jetOrder s hs _
      ((hp.pderiv v).mono (by omega)) (hj.pderiv v) ab a b ha hb hpa hpb haq hbq) j

/-- A bounded pairing with the weak derivative belonging to a selected jet. -/
def sobolevJetCovector (s : ℕ) (v : Jet) (hv : v.2 ≤ s) :
    Coeff 2 →L[ℂ] (SobolevSource s →L[ℂ] ℂ) :=
  let L := (hierarchySobolevJetL2 s v.2 hv).comp
    (if v.1 then ContinuousLinearMap.snd ℂ _ _ else ContinuousLinearMap.fst ℂ _ _)
  ((ContinuousLinearMap.compL ℂ (SobolevSource s) (Coeff 2) ℂ).flip L).comp
    (Coeff.dualPairing.comp Coeff.reflection.toContinuousLinearEquiv.toContinuousLinearMap)

@[simp] theorem sobolevJetCovector_apply (s : ℕ) (v : Jet) (hv : v.2 ≤ s)
    (g : Coeff 2) (cd : SobolevSource s) :
    sobolevJetCovector s v hv g cd = Coeff.dualPairing (Coeff.reflection g)
      (hierarchySobolevJetL2 s v.2 hv (if v.1 then cd.2 else cd.1)) := by
  rcases v with ⟨field,k⟩
  cases field <;> rfl

def sobolevPolynomialCovector (s : ℕ) (p : DifferentialPolynomial.Polynomial)
    (ab : SobolevSource s) : SobolevSource s →L[ℂ] ℂ :=
  ∑ v ∈ p.vars, if hv : v.2 ≤ s then
    sobolevJetCovector s v hv (sobolevPolynomialPartialCoefficients s p v ab) else 0

theorem analyticAt_sobolevPolynomialCovector (s : ℕ) (p : DifferentialPolynomial.Polynomial)
    (ab : SobolevSource s) : AnalyticAt ℂ (sobolevPolynomialCovector s p) ab := by
  apply Finset.analyticAt_fun_sum
  intro v _
  split_ifs
  · exact ((sobolevJetCovector s v _).analyticAt _).comp
      (analyticAt_sobolevPolynomialPartialCoefficients s p v ab)
  · exact analyticAt_const

theorem sobolevPolynomialCovector_eq_classical (s : ℕ) (hs : 1 ≤ s)
    (p : DifferentialPolynomial.Polynomial) (hp : DerivativeOrderLE p (2*(s : ℤ)-1))
    (hj : JetOrderLE p s) (ab cd : SobolevSource s) (a b h l : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hh : ContDiff ℝ ∞ h) (hl : ContDiff ℝ ∞ l)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1)
    (hph : Function.Periodic h 1) (hpl : Function.Periodic l 1)
    (haq : ∀ j, ab.1.val j = periodOneCoefficient a j)
    (hbq : ∀ j, ab.2.val j = periodOneCoefficient b j)
    (hhq : ∀ j, cd.1.val j = periodOneCoefficient h j)
    (hlq : ∀ j, cd.2.val j = periodOneCoefficient l j) :
    sobolevPolynomialCovector s p ab cd =
      ∫ x in (0 : ℝ)..1, firstVariationDensity a b h l p x := by
  classical
  have hc (v : Jet) : Continuous (fun x =>
      iteratedDeriv v.2 (if v.1 then l else h) x * evaluate a b (pderiv v p) x) :=
    (NLS.FunctionalAnalysis.contDiff_iteratedDeriv _ (by split <;> assumption) v.2).continuous.mul
      (continuous_evaluate a b ha hb _)
  rw [sobolevPolynomialCovector]
  simp only [sum_apply]
  unfold firstVariationDensity
  rw [intervalIntegral.integral_finsetSum (fun v _ => (hc v).intervalIntegrable 0 1)]
  apply Finset.sum_congr rfl
  intro v hv
  rw [dif_pos (hj.vars v hv), sobolevJetCovector_apply, Coeff.dualPairing_apply]
  have he := tsum_bilinear_unitFourierCoefficient
    (continuous_evaluate a b ha hb (pderiv v p))
    (NLS.FunctionalAnalysis.contDiff_iteratedDeriv (if v.1 then l else h)
      (by split <;> assumption) v.2).continuous
  have hunit (f : ℝ → ℂ) (j : ℤ) : unitFourierCoefficient f j = periodOneCoefficient f j :=
    unitFourierCoefficient_eq_fourierCoeffOn f j
  simp only [hunit] at he
  have hd (j : ℤ) :
      hierarchySobolevJetL2 s v.2 (hj.vars v hv) (if v.1 then cd.2 else cd.1) j =
        periodOneCoefficient (iteratedDeriv v.2 (if v.1 then l else h)) j := by
    rw [hierarchySobolevJetL2_apply, periodOneCoefficient_iteratedDeriv_of_smooth _
      (by split <;> assumption) (by split <;> assumption)]
    cases v.1 <;> simp only [Bool.false_eq_true, ↓reduceIte, hhq, hlq]
  simp_rw [Coeff.reflection_apply, sobolevPolynomialPartialCoefficients_eq_classical
    s hs p hp hj v ab a b ha hb hpa hpb haq hbq, hd]
  rw [he]
  apply intervalIntegral.integral_congr
  intro x _
  exact mul_comm _ _

private theorem coefficient_affine (s : ℕ) (a h : ScalarSobolev s) (f g : ℝ → ℂ)
    (hf : Continuous f) (hg : Continuous g)
    (ha : ∀ j, a.val j = periodOneCoefficient f j)
    (hh : ∀ j, h.val j = periodOneCoefficient g j) (z : ℂ) (j : ℤ) :
    (a+z • h).val j = periodOneCoefficient (fun t => f t+z*g t) j := by
  change a.val j+z*h.val j = periodOneCoefficient (f+z • g) j
  rw [periodOneCoefficient_add f (z • g) hf (hg.const_smul z)]
  have he : periodOneCoefficient (z • g) j = z*periodOneCoefficient g j := by
    rw [periodOneCoefficient, fourierCoeffOn.const_smul]
    rfl
  rw [he, ha, hh]

private theorem fderiv_polynomial_smooth_direction (s : ℕ) (hs : 1 ≤ s)
    (p : DifferentialPolynomial.Polynomial) (hp : DerivativeOrderLE p (2*(s : ℤ)-1))
    (hj : JetOrderLE p s) (ab cd : SobolevSource s) (a b h l : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hh : ContDiff ℝ ∞ h) (hl : ContDiff ℝ ∞ l)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1)
    (hph : Function.Periodic h 1) (hpl : Function.Periodic l 1)
    (haq : ∀ j, ab.1.val j = periodOneCoefficient a j)
    (hbq : ∀ j, ab.2.val j = periodOneCoefficient b j)
    (hhq : ∀ j, cd.1.val j = periodOneCoefficient h j)
    (hlq : ∀ j, cd.2.val j = periodOneCoefficient l j) :
    fderiv ℂ (sobolevPolynomialL2Mean s p) ab cd = sobolevPolynomialCovector s p ab cd := by
  have he (z : ℂ) : sobolevPolynomialL2Mean s p (ab+z • cd) =
      ∫ x in (0 : ℝ)..1, evaluate (fun t => a t+z*h t) (fun t => b t+z*l t) p x :=
    sobolevPolynomialL2Mean_eq_classical s hs p hp hj (ab+z • cd) _ _
      (ha.add (contDiff_const.mul hh)) (hb.add (contDiff_const.mul hl))
      (fun x => by rw [hpa x,hph x]) (fun x => by rw [hpb x,hpl x])
      (coefficient_affine s ab.1 cd.1 a h ha.continuous hh.continuous haq hhq z)
      (coefficient_affine s ab.2 cd.2 b l hb.continuous hl.continuous hbq hlq z)
  have hline : HasDerivAt (fun z : ℂ => ab+z • cd) cd 0 := by
    simpa using (hasDerivAt_id (0 : ℂ)).smul_const cd |>.const_add ab
  have hf := (analyticAt_sobolevPolynomialL2Mean s p ab).differentiableAt.hasFDerivAt
  have hzero : ab+(0 : ℂ) • cd = ab := by module
  have hd := (hzero ▸ hf).comp_hasDerivAt 0 hline
  simp only [Function.comp_def, he] at hd
  rw [sobolevPolynomialCovector_eq_classical s hs p hp hj ab cd a b h l
    ha hb hh hl hpa hpb hph hpl haq hbq hhq hlq]
  simpa only [hzero] using hd.unique (hasDerivAt_integral_evaluate a b h l ha hb hh hl p)

/-- The endpoint polynomial covector is the actual Fréchet derivative on
all complex H^s inputs and all H^s directions, including nonsmooth ones. -/
theorem fderiv_sobolevPolynomialL2Mean (s : ℕ) (hs : 1 ≤ s)
    (p : DifferentialPolynomial.Polynomial) (hp : DerivativeOrderLE p (2*(s : ℤ)-1))
    (hj : JetOrderLE p s) (ab : SobolevSource s) :
    fderiv ℂ (sobolevPolynomialL2Mean s p) ab = sobolevPolynomialCovector s p ab := by
  have hF : Continuous (fderiv ℂ (sobolevPolynomialL2Mean s p)) :=
    continuous_iff_continuousAt.mpr (fun cd =>
      (analyticAt_sobolevPolynomialL2Mean s p cd).contDiffAt.continuousAt_fderiv
        (n := 1) one_ne_zero)
  have hG : Continuous (sobolevPolynomialCovector s p) :=
    continuous_iff_continuousAt.mpr (fun cd => (analyticAt_sobolevPolynomialCovector s p cd).continuousAt)
  have he := eq_of_continuous_of_smooth_sobolevSource s _ _ hF hG (by
    intro cd a b ha hb hpa hpb haq hbq
    apply ContinuousLinearMap.ext
    intro ef
    have hd := eq_of_continuous_of_smooth_sobolevSource s _ _
      (fderiv ℂ (sobolevPolynomialL2Mean s p) cd).continuous
      (sobolevPolynomialCovector s p cd).continuous (by
        intro fg h l hh hl hph hpl hhq hlq
        exact fderiv_polynomial_smooth_direction s hs p hp hj cd fg a b h l
          ha hb hh hl hpa hpb hph hpl haq hbq hhq hlq)
    exact congrFun hd ef)
  exact congrFun he ab

end NLS.ZakharovShabat
