import NLS.ZakharovShabat.RealDeletedPeriodicProduct
import NLS.ComplexAnalysis.EndpointSqrtWeight
import NLS.ComplexAnalysis.RealAxisSecondDerivative
import NLS.ZakharovShabat.DiscriminantCriticalLocalization

/-!
# Integrability of the arcosh derivative on a real open gap

The discriminant radicand is the endpoint-distance product times a
positive continuous deleted product. Its derivative is continuous,
so the arcosh kernel is interval-integrable across both endpoints.
-/

noncomputable section
open Set Complex MeasureTheory
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem continuous_realGapHalfDiscriminant_deriv
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (heven : φ ∈ pairParitySubspace 0)
    (n : ℤ) :
    Continuous (deriv (realGapHalfDiscriminant hp φ n)) := by
  let D : ℝ → ℝ := fun x => (canonicalDiscriminant hp φ x).re
  have hdiff : Differentiable ℂ (canonicalDiscriminant hp φ) :=
    fun z => (analyticOnNhd_canonicalDiscriminant hp hp1 φ heven z (mem_univ _)).differentiableAt
  have hderivD (x : ℝ) : deriv D x =
      (deriv (canonicalDiscriminant hp φ) (x:ℂ)).re :=
    NLS.ComplexAnalysis.deriv_real_axis_re _ hdiff x
  have hDc : Continuous (deriv D) := by
    have hc := (analyticOnNhd_discriminant_derivative hp hp1 φ heven).continuousOn
    have hc' : Continuous (deriv (canonicalDiscriminant hp φ)) :=
      continuousOn_univ.mp hc
    have hr : Continuous (fun x : ℝ =>
        (deriv (canonicalDiscriminant hp φ) (x:ℂ)).re) :=
      continuous_re.comp (hc'.comp continuous_ofReal)
    have he : deriv D = fun x : ℝ =>
        (deriv (canonicalDiscriminant hp φ) (x:ℂ)).re :=
      funext hderivD
    rwa [he]
  by_cases hn : n % 2 = 0
  · have he : realGapHalfDiscriminant hp φ n =
        fun x : ℝ => D x / 2 := by
      funext x
      simp [realGapHalfDiscriminant,D,hn]
    have hd : deriv (realGapHalfDiscriminant hp φ n) =
        fun x : ℝ => deriv D x / 2 := by
      funext x
      rw [he,deriv_div_const]
    rw [hd]
    exact hDc.div_const 2
  · have he : realGapHalfDiscriminant hp φ n =
        fun x : ℝ => -D x / 2 := by
      funext x
      simp [realGapHalfDiscriminant,D,hn]
    have hd : deriv (realGapHalfDiscriminant hp φ n) =
        fun x : ℝ => -(deriv D x) / 2 := by
      funext x
      rw [he,deriv_div_const]
      change deriv (-D) x / 2 = -(deriv D x) / 2
      rw [deriv.neg]
    rw [hd]
    exact hDc.neg.div_const 2

/-- For a real-type source potential, the arcosh derivative kernel
is integrable on every open canonical real gap. -/
theorem intervalIntegrable_realGapHalfDiscriminant_arcosh_deriv
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re) :
    IntervalIntegrable
      (fun x : ℝ =>
        deriv (realGapHalfDiscriminant hp (periodOnePotential ψ) n) x /
          Real.sqrt ((realGapHalfDiscriminant hp (periodOnePotential ψ) n x)^2 - 1))
      volume
        (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
          (periodOnePotential_mem ψ) n).re
        (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
          (periodOnePotential_mem ψ) n).re := by
  let φ := periodOnePotential ψ
  let a := (canonicalPeriodicLeft hp hp1 φ (periodOnePotential_mem ψ) n).re
  let b := (canonicalPeriodicRight hp hp1 φ (periodOnePotential_mem ψ) n).re
  let g := realGapHalfDiscriminant hp φ n
  let G (x : ℝ) := (canonicalDeletedPeriodicProduct hp hp1 φ
    (periodOnePotential_mem ψ) n x).re
  have hnum : ContinuousOn (deriv g) (Icc a b) :=
    (continuous_realGapHalfDiscriminant_deriv hp hp1 φ
      (periodOnePotential_mem ψ) n).continuousOn
  have hGc : ContinuousOn G (Icc a b) := by
    have hc := (analyticOnNhd_canonicalDeletedPeriodicProduct hp hp1 φ
      (periodOnePotential_mem ψ) n).continuousOn
    exact (continuous_re.comp ((continuousOn_univ.mp hc).comp
      continuous_ofReal)).continuousOn
  have hGpos (x : ℝ) (hx : x ∈ Icc a b) : 0 < G x :=
    canonicalDeletedPeriodicProduct_re_pos_on_realGap hp hp1 ψ hreal n
      hopen x hx
  have hfactor (x : ℝ) (hx : x ∈ Ioo a b) :
      g x^2-1 = (x-a)*(b-x)*G x :=
    realGapHalfDiscriminant_sq_sub_one_eq_deletedPair_re hp hp1 φ
      (periodOnePotential_mem ψ) (isRealType_periodOnePotential ψ hreal) n x
  exact NLS.ComplexAnalysis.intervalIntegrable_div_sqrt_factored_endpoint_product
    hopen hnum hGc hGpos hfactor

/-- The signed discriminant's arcosh derivative integrates to zero
across a real open source gap, without an endpoint-integrability
assumption. -/
theorem integral_realGapHalfDiscriminant_arcosh_deriv_eq_zero_of_source
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re) :
    (∫ x in (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re..
        (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
          (periodOnePotential_mem ψ) n).re,
      deriv (realGapHalfDiscriminant hp (periodOnePotential ψ) n) x /
        Real.sqrt ((realGapHalfDiscriminant hp (periodOnePotential ψ) n x)^2 - 1)) =
      0 :=
  integral_realGapHalfDiscriminant_arcosh_deriv_eq_zero hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ)
    (isRealType_periodOnePotential ψ hreal) n
    (intervalIntegrable_realGapHalfDiscriminant_arcosh_deriv hp hp1 ψ hreal n hopen)

end NLS.ZakharovShabat
