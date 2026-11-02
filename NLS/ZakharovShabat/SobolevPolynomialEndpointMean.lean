import NLS.ZakharovShabat.SobolevPolynomialL2
import NLS.Fourier.CircleBilinearMean

/-! # Endpoint means with two top-order L² factors

For s>=1, jets through s and at most 2s total derivatives allow at most
two order-s factors. After removing both, the remaining factors are
continuous. Bounded bilinear Parseval supplies their actual physical mean.
-/
noncomputable section
open NLS.Fourier NLS.DifferentialPolynomial MvPolynomial MeasureTheory Set
open scoped ContDiff
namespace NLS.ZakharovShabat

def sobolevTopMonomialProduct (s : ℕ) (field : Bool) (m : Monomial) (c : ℂ)
    (ab : SobolevSource s) : CircleL2 :=
  circleMulCLM (sobolevPolynomialField s (MvPolynomial.monomial m c) ab)
    (topSobolevJetCircleL2 s field ab)

theorem analyticAt_sobolevTopMonomialProduct (s : ℕ) (field : Bool) (m : Monomial) (c : ℂ)
    (ab : SobolevSource s) : AnalyticAt ℂ (sobolevTopMonomialProduct s field m c) ab :=
  (circleMulCLM.analyticAt_bilinear
    (sobolevPolynomialField s (MvPolynomial.monomial m c) ab, topSobolevJetCircleL2 s field ab)).comp
      (f := fun cd => (sobolevPolynomialField s (MvPolynomial.monomial m c) cd,
        topSobolevJetCircleL2 s field cd))
      ((analyticAt_sobolevPolynomialField s _ ab).prod ((topSobolevJetCircleL2 s field).analyticAt ab))

theorem sobolevTopMonomialProduct_eq_classical (s : ℕ) (hs : 1 ≤ s) (field : Bool)
    (m : Monomial) (c : ℂ) (hm : JetOrderLE (MvPolynomial.monomial m c) (s-1))
    (ab : SobolevSource s) (a b : ℝ → ℂ) (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1)
    (hac : ∀ j, ab.1.val j = periodOneCoefficient a j)
    (hbc : ∀ j, ab.2.val j = periodOneCoefficient b j) :
    circlePullback (sobolevTopMonomialProduct s field m c ab) =ᵐ[volume.restrict (Ioc 0 1)]
      (fun x => evaluate a b (MvPolynomial.monomial m c) x*iteratedDeriv s (if field then b else a) x) := by
  have hp := ae_restrict_of_ae_restrict_of_subset
    (Ioc_subset_Ioc_right (by norm_num : (1 : ℝ) ≤ 2))
    (circlePullback_circleMul (sobolevPolynomialField s (MvPolynomial.monomial m c) ab)
      (topSobolevJetCircleL2 s field ab))
  have hj := topSobolevJetCircleL2_eq_classical s field ab a b ha hb hpa hpb hac hbc
  filter_upwards [hp,hj] with x hx hjx
  change circlePullback (circleMul _ _) x = _
  rw [hx,hjx,sobolevPolynomialField_eq_classical s hs _ hm ab a b ha hb hpa hpb hac hbc]

def sobolevMonomialEndpointMean (s : ℕ) (m : Monomial) (c : ℂ) (ab : SobolevSource s) : ℂ :=
  if ht : ∃ v ∈ m.support, v.2 = s then
    let v := Classical.choose ht
    let r := m-Finsupp.single v 1
    if hw : ∃ w ∈ r.support, w.2 = s then
      let w := Classical.choose hw
      circleBilinearMean (sobolevTopMonomialProduct s v.1 (r-Finsupp.single w 1) c ab)
        (topSobolevJetCircleL2 s w.1 ab)
    else circlePrimitiveCLM 1 (by constructor <;> norm_num) (sobolevTopMonomialProduct s v.1 r c ab)
  else sobolevPolynomialMean s (MvPolynomial.monomial m c) ab

theorem analyticAt_sobolevMonomialEndpointMean (s : ℕ) (m : Monomial) (c : ℂ)
    (ab : SobolevSource s) : AnalyticAt ℂ (sobolevMonomialEndpointMean s m c) ab := by
  unfold sobolevMonomialEndpointMean
  split_ifs with ht
  · dsimp only
    split_ifs with hw
    · let v := Classical.choose ht
      let r := m-Finsupp.single v 1
      let w := Classical.choose hw
      exact (circleBilinearMean.analyticAt_bilinear
        (sobolevTopMonomialProduct s v.1 (r-Finsupp.single w 1) c ab,
          topSobolevJetCircleL2 s w.1 ab)).comp
        (f := fun cd => (sobolevTopMonomialProduct s v.1 (r-Finsupp.single w 1) c cd,
          topSobolevJetCircleL2 s w.1 cd))
        ((analyticAt_sobolevTopMonomialProduct s v.1 _ c ab).prod
          ((topSobolevJetCircleL2 s w.1).analyticAt ab))
    · exact ((circlePrimitiveCLM 1 (by constructor <;> norm_num)).analyticAt _).comp
        (analyticAt_sobolevTopMonomialProduct s (Classical.choose ht).1 _ c ab)
  · exact analyticAt_sobolevPolynomialMean s _ ab

theorem sobolevMonomialEndpointMean_eq_classical (s : ℕ) (hs : 1 ≤ s)
    (m : Monomial) (c : ℂ) (hm : Finsupp.weight derivativeWeight m ≤ 2*(s : ℤ))
    (hjet : ∀ v ∈ m.support, v.2 ≤ s)
    (ab : SobolevSource s) (a b : ℝ → ℂ) (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1)
    (hac : ∀ j, ab.1.val j = periodOneCoefficient a j)
    (hbc : ∀ j, ab.2.val j = periodOneCoefficient b j) :
    sobolevMonomialEndpointMean s m c ab =
      ∫ x in (0 : ℝ)..1, evaluate a b (MvPolynomial.monomial m c) x := by
  classical
  unfold sobolevMonomialEndpointMean
  split_ifs with ht
  · dsimp only
    split_ifs with hw
    · let v := Classical.choose ht
      let r := m-Finsupp.single v 1
      let w := Classical.choose hw
      have hv : v ∈ m.support := (Classical.choose_spec ht).1
      have hvs : v.2 = s := (Classical.choose_spec ht).2
      have hwr : w ∈ r.support := (Classical.choose_spec hw).1
      have hws : w.2 = s := (Classical.choose_spec hw).2
      have hlo : JetOrderLE (MvPolynomial.monomial (r-Finsupp.single w 1) c) (s-1) :=
        JetOrderLE.of_derivativeOrder (Supported.monomial _ _ (show
          Finsupp.weight derivativeWeight (r-Finsupp.single w 1) ≤ 0 from by
            rw [weight_erase_one _ r w hwr, show r = m-Finsupp.single v 1 from rfl,
              weight_erase_one _ m v hv]
            simp only [derivativeWeight,hvs,hws]
            omega)) (by omega)
      have hc1 := sobolevTopMonomialProduct_eq_classical s hs v.1 _ c hlo ab a b ha hb hpa hpb hac hbc
      have hc2 := topSobolevJetCircleL2_eq_classical s w.1 ab a b ha hb hpa hpb hac hbc
      rw [circleBilinearMean_eq_classical _ _ _ _
        ((continuous_evaluate a b ha hb _).mul
          (NLS.FunctionalAnalysis.contDiff_iteratedDeriv _ (by split <;> assumption) s).continuous)
        (NLS.FunctionalAnalysis.contDiff_iteratedDeriv _ (by split <;> assumption) s).continuous hc1 hc2]
      apply intervalIntegral.integral_congr
      intro x _
      rw [monomial_factor_jet m c v hv,evaluate_mul,evaluate_X,
        monomial_factor_jet r c w hwr,evaluate_mul,evaluate_X]
      simp only [Pi.mul_apply,hvs,hws]
      ring
    · let v := Classical.choose ht
      let r := m-Finsupp.single v 1
      have hv : v ∈ m.support := (Classical.choose_spec ht).1
      have hvs : v.2 = s := (Classical.choose_spec ht).2
      have hlo : JetOrderLE (MvPolynomial.monomial r c) (s-1) := by
        apply Supported.monomial
        intro w hwr
        have hwle := hjet w (Finsupp.support_tsub hwr)
        have hwne : w.2 ≠ s := fun he => hw ⟨w,hwr,he⟩
        omega
      have hc1 := sobolevTopMonomialProduct_eq_classical s hs v.1 r c hlo ab a b ha hb hpa hpb hac hbc
      change (∫ x in (0 : ℝ)..1, circlePullback _ x) = _
      rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
        intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      apply integral_congr_ae
      filter_upwards [hc1] with x hx
      rw [hx,monomial_factor_jet m c v hv,evaluate_mul,evaluate_X]
      simp only [Pi.mul_apply,hvs]
      ring
  · have hlo : JetOrderLE (MvPolynomial.monomial m c) (s-1) := by
      apply Supported.monomial
      intro v hv
      have hvle := hjet v hv
      have hvne : v.2 ≠ s := fun he => ht ⟨v,hv,he⟩
      omega
    exact sobolevPolynomialMean_eq_integral s hs _ hlo ab a b ha hb hpa hpb hac hbc


def sobolevPolynomialEndpointMean (s : ℕ) (p : DifferentialPolynomial.Polynomial)
    (ab : SobolevSource s) : ℂ :=
  ∑ m ∈ p.support, sobolevMonomialEndpointMean s m (p.coeff m) ab

theorem analyticAt_sobolevPolynomialEndpointMean (s : ℕ) (p : DifferentialPolynomial.Polynomial)
    (ab : SobolevSource s) : AnalyticAt ℂ (sobolevPolynomialEndpointMean s p) ab :=
  Finset.analyticAt_fun_sum _ (fun m _ => analyticAt_sobolevMonomialEndpointMean s m (p.coeff m) ab)

theorem sobolevPolynomialEndpointMean_eq_classical (s : ℕ) (hs : 1 ≤ s)
    (p : DifferentialPolynomial.Polynomial) (hp : DerivativeOrderLE p (2*(s : ℤ)))
    (hj : JetOrderLE p s) (ab : SobolevSource s) (a b : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1)
    (hac : ∀ j, ab.1.val j = periodOneCoefficient a j)
    (hbc : ∀ j, ab.2.val j = periodOneCoefficient b j) :
    sobolevPolynomialEndpointMean s p ab = ∫ x in (0 : ℝ)..1, evaluate a b p x := by
  calc
    sobolevPolynomialEndpointMean s p ab = ∑ m ∈ p.support,
        ∫ x in (0 : ℝ)..1, evaluate a b (MvPolynomial.monomial m (p.coeff m)) x := by
      apply Finset.sum_congr rfl
      intro m hm
      exact sobolevMonomialEndpointMean_eq_classical s hs m (p.coeff m) (hp m hm) (hj m hm)
        ab a b ha hb hpa hpb hac hbc
    _ = ∫ x in (0 : ℝ)..1, ∑ m ∈ p.support,
        evaluate a b (MvPolynomial.monomial m (p.coeff m)) x := by
      symm
      exact intervalIntegral.integral_finsetSum (fun m _ =>
        (continuous_evaluate a b ha hb (MvPolynomial.monomial m (p.coeff m))).intervalIntegrable 0 1)
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro x _
      conv_rhs => rw [p.as_sum]
      simp only [evaluate,map_sum]

end NLS.ZakharovShabat
