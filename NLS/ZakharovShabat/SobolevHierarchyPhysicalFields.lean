import NLS.ZakharovShabat.SobolevHierarchyGradient
import NLS.ZakharovShabat.SobolevSourceSmoothDensity
import NLS.Fourier.UnitIntervalSobolevRealization

/-! # Actual continuous and L2 representatives of the hierarchy gradients

At one derivative below the top order the physical gradient is continuous.
At the top order its independently constructed polynomial realization is
only L2. Both retain the original unit-interval Fourier coefficients.
-/
noncomputable section
open Set Complex MeasureTheory NLS.Fourier NLS.DifferentialPolynomial MvPolynomial
open scoped ContDiff
namespace NLS.ZakharovShabat

def sobolevNLSHierarchyContinuousGradient (s k : ℕ) (ab : SobolevSource s) :
    C(AddCircle (2:ℝ),ℂ) × C(AddCircle (2:ℝ),ℂ) :=
  (sobolevPolynomialField s (eulerDerivative false (nlsHamiltonianPolynomial k)) ab,
   sobolevPolynomialField s (eulerDerivative true (nlsHamiltonianPolynomial k)) ab)

def sobolevNLSHierarchyCircleGradient (s k : ℕ) (ab : SobolevSource s) : CircleL2 × CircleL2 :=
  (sobolevPolynomialL2 s (eulerDerivative false (nlsHamiltonianPolynomial k)) ab,
   sobolevPolynomialL2 s (eulerDerivative true (nlsHamiltonianPolynomial k)) ab)

theorem analyticAt_sobolevNLSHierarchyContinuousGradient (s k : ℕ) (ab : SobolevSource s) :
    AnalyticAt ℂ (sobolevNLSHierarchyContinuousGradient s k) ab :=
  (analyticAt_sobolevPolynomialField s _ ab).prod (analyticAt_sobolevPolynomialField s _ ab)

theorem analyticAt_sobolevNLSHierarchyCircleGradient (s k : ℕ) (ab : SobolevSource s) :
    AnalyticAt ℂ (sobolevNLSHierarchyCircleGradient s k) ab :=
  (analyticAt_sobolevPolynomialL2 s _ ab).prod (analyticAt_sobolevPolynomialL2 s _ ab)

theorem sobolevNLSHierarchyContinuousGradient_eq_classical
    (s k : ℕ) (hs : 1 ≤ s) (hk : k ≤ s) (ab : SobolevSource s) (a b : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1)
    (haq : ∀ j, ab.1.val j = periodOneCoefficient a j)
    (hbq : ∀ j, ab.2.val j = periodOneCoefficient b j) (x : ℝ) :
    ((sobolevNLSHierarchyContinuousGradient s k ab).1 (x : AddCircle (2:ℝ)),
     (sobolevNLSHierarchyContinuousGradient s k ab).2 (x : AddCircle (2:ℝ))) =
       classicalNLSHierarchyGradient a b k x := by
  apply Prod.ext
  · exact sobolevPolynomialField_eq_classical s hs _
      (JetOrderLE.of_derivativeOrder (nlsHierarchyEuler_derivativeOrder k false) (by omega))
        ab a b ha hb hpa hpb haq hbq x
  · exact sobolevPolynomialField_eq_classical s hs _
      (JetOrderLE.of_derivativeOrder (nlsHierarchyEuler_derivativeOrder k true) (by omega))
        ab a b ha hb hpa hpb haq hbq x

theorem sobolevNLSHierarchyCircleGradient_eq_classical
    (s k : ℕ) (hs : 1 ≤ s) (hk : k ≤ s+1) (ab : SobolevSource s) (a b : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1)
    (haq : ∀ j, ab.1.val j = periodOneCoefficient a j)
    (hbq : ∀ j, ab.2.val j = periodOneCoefficient b j) :
    (fun x => (circlePullback (sobolevNLSHierarchyCircleGradient s k ab).1 x,
      circlePullback (sobolevNLSHierarchyCircleGradient s k ab).2 x))
      =ᵐ[volume.restrict (Ioc 0 1)] classicalNLSHierarchyGradient a b k := by
  filter_upwards [sobolevPolynomialL2_eq_classical s hs _
    ((nlsHierarchyEuler_derivativeOrder k false).mono (by omega)) ab a b ha hb hpa hpb haq hbq,
    sobolevPolynomialL2_eq_classical s hs _
      ((nlsHierarchyEuler_derivativeOrder k true).mono (by omega)) ab a b ha hb hpa hpb haq hbq]
    with x hx₁ hx₂
  exact Prod.ext hx₁ hx₂

theorem sobolevNLSHierarchyCircleGradient_coefficients (s k : ℕ) (hs : 1 ≤ s) (ab : SobolevSource s) :
    (circleUnitCoefficients (sobolevNLSHierarchyCircleGradient s k ab).1,
     circleUnitCoefficients (sobolevNLSHierarchyCircleGradient s k ab).2) =
       sobolevNLSHierarchyGradient s k ab := by
  simp only [sobolevNLSHierarchyGradient,dif_pos hs,sobolevNLSHierarchyCircleGradient]

theorem circleUnitCoefficients_toLp_apply (f : C(AddCircle (2:ℝ),ℂ)) (j : ℤ) :
    circleUnitCoefficients (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ f) j =
      periodOneCoefficient (fun x : ℝ => f (x : AddCircle (2:ℝ))) j := by
  apply circleUnitCoefficients_eq_classical
  exact ae_restrict_of_ae_restrict_of_subset (Ioc_subset_Ioc_right (by norm_num : (1:ℝ) ≤ 2))
    (circle_ae_pullback (ContinuousMap.coeFn_toLp AddCircle.haarAddCircle f))

theorem unitL2Synthesis_circleUnitCoefficients (f : CircleL2) :
    unitL2SynthesisEquiv (circleUnitCoefficients f) =ᵐ[volume.restrict (Ioc 0 1)] circlePullback f := by
  apply unitL2Synthesis_eq_of_unitCoefficients
  · exact (memLp_circlePullback f).mono_measure
      (Measure.restrict_mono_set _ (Ioc_subset_Ioc_right (by norm_num : (1:ℝ) ≤ 2)))
  · intro j
    rw [unitFourierCoefficient_eq_fourierCoeffOn]
    exact (circleUnitCoefficients_apply f j).symm

theorem sobolevNLSHierarchyContinuousGradient_coefficients (s k : ℕ) (hs : 1 ≤ s) (hk : k ≤ s)
    (ab : SobolevSource s) :
    (circleUnitCoefficients (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ
        (sobolevNLSHierarchyContinuousGradient s k ab).1),
     circleUnitCoefficients (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ
        (sobolevNLSHierarchyContinuousGradient s k ab).2)) =
       sobolevNLSHierarchyGradient s k ab := by
  let F (cd : SobolevSource s) :=
    (circleUnitCoefficients (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ
        (sobolevNLSHierarchyContinuousGradient s k cd).1),
     circleUnitCoefficients (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ
        (sobolevNLSHierarchyContinuousGradient s k cd).2))
  have hC : Continuous (sobolevNLSHierarchyContinuousGradient s k) :=
    continuous_iff_continuousAt.mpr fun cd => (analyticAt_sobolevNLSHierarchyContinuousGradient s k cd).continuousAt
  have hF : Continuous F :=
    (circleUnitCoefficients.continuous.comp ((ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ).continuous.comp
      hC.fst)).prodMk
      (circleUnitCoefficients.continuous.comp ((ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ).continuous.comp hC.snd))
  have he := eq_of_continuous_of_smooth_sobolevSource s F (sobolevNLSHierarchyGradient s k) hF
    (continuous_iff_continuousAt.mpr fun cd => (analyticAt_sobolevNLSHierarchyGradient s k cd).continuousAt) (by
      intro cd a b ha hb hpa hpb haq hbq
      have hfield := sobolevNLSHierarchyContinuousGradient_eq_classical s k hs hk cd a b ha hb hpa hpb haq hbq
      have hc₁ : (fun x : ℝ => (sobolevNLSHierarchyContinuousGradient s k cd).1 (x : AddCircle (2:ℝ))) =
          fun x => (classicalNLSHierarchyGradient a b k x).1 := funext fun x => congrArg Prod.fst (hfield x)
      have hc₂ : (fun x : ℝ => (sobolevNLSHierarchyContinuousGradient s k cd).2 (x : AddCircle (2:ℝ))) =
          fun x => (classicalNLSHierarchyGradient a b k x).2 := funext fun x => congrArg Prod.snd (hfield x)
      apply Prod.ext
      · ext j
        change circleUnitCoefficients _ j = _
        rw [circleUnitCoefficients_toLp_apply,hc₁]
        exact (congrArg Prod.fst (sobolevNLSHierarchyGradient_eq_classical s k (by omega)
          cd a b ha hb hpa hpb haq hbq j)).symm
      · ext j
        change circleUnitCoefficients _ j = _
        rw [circleUnitCoefficients_toLp_apply,hc₂]
        exact (congrArg Prod.snd (sobolevNLSHierarchyGradient_eq_classical s k (by omega)
          cd a b ha hb hpa hpb haq hbq j)).symm)
  exact congrFun he ab

end NLS.ZakharovShabat
