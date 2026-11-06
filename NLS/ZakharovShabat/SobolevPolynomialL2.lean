import NLS.ZakharovShabat.SobolevDifferentialPolynomial
import NLS.DifferentialPolynomial.EulerOrderBounds
import NLS.Fourier.CircleMultiplication
import NLS.Fourier.ContinuousPeriodOneRealization

/-! # L² realization at the top Sobolev jet

For s ≥ 1, a monomial with jets through order s and total derivative count
below 2s contains at most one jet of order s. Remove that factor, evaluate the remaining polynomial as
a continuous field, and multiply by the actual L² Fourier realization of the
top derivative. This constructs an analytic field without assigning the top
derivative a continuous representative.
-/
noncomputable section
open NLS.Fourier NLS.DifferentialPolynomial MvPolynomial MeasureTheory Set
open scoped ContDiff
namespace NLS.ZakharovShabat

/-- The actual top physical derivative on the period-two ambient circle,
using even insertion of the original period-one coefficients. -/
def topSobolevJetCircleL2 (s : ℕ) (field : Bool) : SobolevSource s →L[ℂ] CircleL2 :=
  l2Synthesis.toContinuousLinearEquiv.toContinuousLinearMap.comp (Coeff.periodDouble.toContinuousLinearMap.comp
    ((hierarchySobolevJetL2 s s le_rfl).comp
      (if field then ContinuousLinearMap.snd ℂ _ _ else ContinuousLinearMap.fst ℂ _ _)))

theorem topSobolevJetCircleL2_eq_classical (s : ℕ) (field : Bool)
    (ab : SobolevSource s) (a b : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1)
    (haq : ∀ j, ab.1.val j = periodOneCoefficient a j)
    (hbq : ∀ j, ab.2.val j = periodOneCoefficient b j) :
    circlePullback (topSobolevJetCircleL2 s field ab) =ᵐ[volume.restrict (Ioc 0 1)]
      iteratedDeriv s (if field then b else a) := by
  let f := iteratedDeriv s (if field then b else a)
  have hf : Continuous f :=
    (contDiff_iteratedDeriv_of_smooth _ (by split <;> assumption) s).continuous
  have hp : Function.Periodic f 1 :=
    DifferentialPolynomial.periodic_iteratedDeriv _ 1 (by split <;> assumption) s
  have hend : f 0 = f 1 := by simpa using (hp 0).symm
  have he : hierarchySobolevJetL2 s s le_rfl (if field then ab.2 else ab.1) =
      continuousPeriodOneCoefficients f hf hend := by
    ext j
    simp only [hierarchySobolevJetL2_apply, continuousPeriodOneCoefficients_apply, f]
    rw [periodOneCoefficient_iteratedDeriv_of_smooth _ (by split <;> assumption)
      (by split <;> assumption)]
    cases field <;> simp only [Bool.false_eq_true, ↓reduceIte, haq, hbq]
  have ht : topSobolevJetCircleL2 s field ab =
      l2Synthesis (Coeff.periodDouble (continuousPeriodOneCoefficients f hf hend)) := by
    change l2Synthesis (Coeff.periodDouble (hierarchySobolevJetL2 s s le_rfl
      ((if field then ContinuousLinearMap.snd ℂ _ _ else ContinuousLinearMap.fst ℂ _ _) ab))) = _
    have hchoose : ((if field then ContinuousLinearMap.snd ℂ _ _ else
        ContinuousLinearMap.fst ℂ _ _) ab) = (if field then ab.2 else ab.1) := by
      cases field <;> rfl
    rw [hchoose, he]
  rw [ht]
  exact circlePullback_continuousPeriodOneCoefficients f hf hend

/-- Monomial realization; the support choice is fixed by the monomial and
does not depend on the Sobolev input. The physical comparison uses s ≥ 1. -/
def sobolevMonomialL2 (s : ℕ) (m : Monomial) (c : ℂ) (ab : SobolevSource s) : CircleL2 :=
  if ht : ∃ v ∈ m.support, v.2 = s then
    let v := Classical.choose ht
    circleMulCLM (sobolevPolynomialField s (MvPolynomial.monomial (m-Finsupp.single v 1) c) ab)
      (topSobolevJetCircleL2 s v.1 ab)
  else ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ
    (sobolevPolynomialField s (MvPolynomial.monomial m c) ab)

theorem analyticAt_sobolevMonomialL2 (s : ℕ) (m : Monomial) (c : ℂ)
    (ab : SobolevSource s) : AnalyticAt ℂ (sobolevMonomialL2 s m c) ab := by
  unfold sobolevMonomialL2
  split_ifs
  · rename_i ht
    let v := Classical.choose ht
    let q := MvPolynomial.monomial (m-Finsupp.single v 1) c
    exact (circleMulCLM.analyticAt_bilinear
      (sobolevPolynomialField s q ab,topSobolevJetCircleL2 s v.1 ab)).comp
      (f := fun cd : SobolevSource s =>
        (sobolevPolynomialField s q cd,topSobolevJetCircleL2 s v.1 cd))
      ((analyticAt_sobolevPolynomialField s q ab).prod
        ((topSobolevJetCircleL2 s v.1).analyticAt ab))
  · exact ((ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ).analyticAt _).comp
      (analyticAt_sobolevPolynomialField s _ ab)

theorem sobolevMonomialL2_eq_classical_of_jetOrder (s : ℕ) (hs : 1 ≤ s) (m : Monomial) (c : ℂ)
    (hm : Finsupp.weight derivativeWeight m ≤ 2*(s : ℤ)-1)
    (hjet : ∀ v ∈ m.support, v.2 ≤ s)
    (ab : SobolevSource s) (a b : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1)
    (haq : ∀ j, ab.1.val j = periodOneCoefficient a j)
    (hbq : ∀ j, ab.2.val j = periodOneCoefficient b j) :
    circlePullback (sobolevMonomialL2 s m c ab) =ᵐ[volume.restrict (Ioc 0 1)]
      evaluate a b (MvPolynomial.monomial m c) := by
  classical
  unfold sobolevMonomialL2
  split_ifs with ht
  · let v := Classical.choose ht
    have hv : v ∈ m.support := (Classical.choose_spec ht).1
    have hvs : v.2 = s := (Classical.choose_spec ht).2
    have hr : JetOrderLE (MvPolynomial.monomial (m-Finsupp.single v 1) c) (s-1) :=
      JetOrderLE.of_derivativeOrder
        (Supported.monomial _ _ (show Finsupp.weight derivativeWeight
          (m-Finsupp.single v 1) ≤ (s-1 : ℕ) from by
            rw [weight_erase_one _ m v hv]
            simp only [derivativeWeight, hvs]
            omega)) le_rfl
    have hp := ae_restrict_of_ae_restrict_of_subset
      (Ioc_subset_Ioc_right (by norm_num : (1 : ℝ) ≤ 2))
      (circlePullback_circleMul
        (sobolevPolynomialField s (MvPolynomial.monomial (m-Finsupp.single v 1) c) ab)
        (topSobolevJetCircleL2 s v.1 ab))
    have hj := topSobolevJetCircleL2_eq_classical s v.1 ab a b ha hb hpa hpb haq hbq
    filter_upwards [hp, hj] with x hpx hjx
    change circlePullback (circleMul
      (sobolevPolynomialField s (MvPolynomial.monomial (m-Finsupp.single v 1) c) ab)
      (topSobolevJetCircleL2 s v.1 ab)) x = _
    rw [hpx, hjx, sobolevPolynomialField_eq_classical s hs _ hr ab a b ha hb hpa hpb haq hbq,
      monomial_factor_jet m c v hv, evaluate_mul, evaluate_X]
    simp only [Pi.mul_apply, hvs]
    ring
  · have hlow : JetOrderLE (MvPolynomial.monomial m c) (s-1) := by
      apply Supported.monomial
      intro v hv
      have hvle := hjet v hv
      have hvne : v.2 ≠ s := fun he => ht ⟨v,hv,he⟩
      omega
    have hp := ae_restrict_of_ae_restrict_of_subset
      (Ioc_subset_Ioc_right (by norm_num : (1 : ℝ) ≤ 2))
      (circle_ae_pullback (ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ)
        AddCircle.haarAddCircle (sobolevPolynomialField s (MvPolynomial.monomial m c) ab)))
    filter_upwards [hp] with x hpx
    exact hpx.trans (sobolevPolynomialField_eq_classical s hs _ hlow ab a b
      ha hb hpa hpb haq hbq x)

theorem sobolevMonomialL2_eq_classical (s : ℕ) (hs : 1 ≤ s) (m : Monomial) (c : ℂ)
    (hm : Finsupp.weight derivativeWeight m ≤ s)
    (ab : SobolevSource s) (a b : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1)
    (haq : ∀ j, ab.1.val j = periodOneCoefficient a j)
    (hbq : ∀ j, ab.2.val j = periodOneCoefficient b j) :
    circlePullback (sobolevMonomialL2 s m c ab) =ᵐ[volume.restrict (Ioc 0 1)]
      evaluate a b (MvPolynomial.monomial m c) := by
  have hD : DerivativeOrderLE (MvPolynomial.monomial m (1 : ℂ)) s :=
    Supported.monomial _ _ hm
  apply sobolevMonomialL2_eq_classical_of_jetOrder s hs m c (hm.trans (by omega))
    (fun v hv => by exact_mod_cast hD.jet_order m (by simp) v hv)
    ab a b ha hb hpa hpb haq hbq

/-- The finite physical monomial sum supplies the top-jet L² realization. -/
def sobolevPolynomialL2 (s : ℕ) (p : DifferentialPolynomial.Polynomial)
    (ab : SobolevSource s) : CircleL2 :=
  ∑ m ∈ p.support, sobolevMonomialL2 s m (p.coeff m) ab

theorem analyticAt_sobolevPolynomialL2 (s : ℕ) (p : DifferentialPolynomial.Polynomial)
    (ab : SobolevSource s) : AnalyticAt ℂ (sobolevPolynomialL2 s p) ab := by
  exact Finset.analyticAt_fun_sum _ (fun m _ => analyticAt_sobolevMonomialL2 s m (p.coeff m) ab)

/-- At most one top L² jet occurs when the total derivative count is below 2s. -/
theorem sobolevPolynomialL2_eq_classical_of_jetOrder (s : ℕ) (hs : 1 ≤ s)
    (p : DifferentialPolynomial.Polynomial) (hp : DerivativeOrderLE p (2*(s : ℤ)-1))
    (hjet : JetOrderLE p s)
    (ab : SobolevSource s) (a b : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1)
    (haq : ∀ j, ab.1.val j = periodOneCoefficient a j)
    (hbq : ∀ j, ab.2.val j = periodOneCoefficient b j) :
    circlePullback (sobolevPolynomialL2 s p ab) =ᵐ[volume.restrict (Ioc 0 1)]
      evaluate a b p := by
  classical
  have he := (Filter.eventually_all_finset p.support).mpr
    (fun m hm => sobolevMonomialL2_eq_classical_of_jetOrder s hs m (p.coeff m) (hp m hm) (hjet m hm)
      ab a b ha hb hpa hpb haq hbq)
  have hsum := circle_ae_pullback (Lp.coeFn_fun_finsetSum p.support
    (fun m => sobolevMonomialL2 s m (p.coeff m) ab))
  have hsum' := ae_restrict_of_ae_restrict_of_subset
    (Ioc_subset_Ioc_right (by norm_num : (1 : ℝ) ≤ 2)) hsum
  filter_upwards [he, hsum'] with x hx hxs
  change circlePullback (∑ m ∈ p.support, sobolevMonomialL2 s m (p.coeff m) ab) x = _
  refine hxs.trans ?_
  conv_rhs => rw [p.as_sum]
  simp only [evaluate, map_sum]
  exact Finset.sum_congr rfl (fun m hm => hx m hm)

theorem sobolevPolynomialL2_eq_classical (s : ℕ) (hs : 1 ≤ s)
    (p : DifferentialPolynomial.Polynomial) (hp : DerivativeOrderLE p s)
    (ab : SobolevSource s) (a b : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1)
    (haq : ∀ j, ab.1.val j = periodOneCoefficient a j)
    (hbq : ∀ j, ab.2.val j = periodOneCoefficient b j) :
    circlePullback (sobolevPolynomialL2 s p ab) =ᵐ[volume.restrict (Ioc 0 1)]
      evaluate a b p := by
  exact sobolevPolynomialL2_eq_classical_of_jetOrder s hs p (hp.mono (by omega))
    (JetOrderLE.of_derivativeOrder hp le_rfl) ab a b ha hb hpa hpb haq hbq

end NLS.ZakharovShabat
