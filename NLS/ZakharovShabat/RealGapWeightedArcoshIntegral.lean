import NLS.ZakharovShabat.RealGapArcoshIntegrability

/-!
# The weighted arcosh integral on a real periodic gap

The action integral of Lemma 11.1 contains the spectral parameter as
an extra factor compared with the zero integral in Lemma 10.11.
Integration by parts converts the centered weighted arcosh derivative
to minus the integral of the positive arcosh profile. In particular,
the real integral has a strict sign on every open gap, independently
of the chosen center.
-/

noncomputable section
open Set Complex MeasureTheory intervalIntegral
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The weighted signed-discriminant arcosh derivative equals minus
the area under its strictly positive arcosh profile. -/
theorem realGap_weighted_arcosh_integral_eq_and_neg
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re)
    (q : ℝ) :
    let a := (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re
    let b := (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re
    let g := realGapHalfDiscriminant hp (periodOnePotential ψ) n
    (∫ x in a..b,
      (x-q) * (deriv g x / Real.sqrt ((g x)^2-1))) =
        -(∫ x in a..b, Real.arcosh (g x)) ∧
    (∫ x in a..b,
      (x-q) * (deriv g x / Real.sqrt ((g x)^2-1))) < 0 := by
  let φ := periodOnePotential ψ
  let a := (canonicalPeriodicLeft hp hp1 φ (periodOnePotential_mem ψ) n).re
  let b := (canonicalPeriodicRight hp hp1 φ (periodOnePotential_mem ψ) n).re
  let g := realGapHalfDiscriminant hp φ n
  obtain ⟨_,hcont,hderiv,hleft,hright,hgt⟩ :=
    realGapHalfDiscriminant_arcosh_gap_data hp hp1 φ
      (periodOnePotential_mem ψ) (isRealType_periodOnePotential ψ hreal) n
  have hint : IntervalIntegrable
      (fun x : ℝ => deriv g x / Real.sqrt ((g x)^2-1)) volume a b :=
    intervalIntegrable_realGapHalfDiscriminant_arcosh_deriv
      hp hp1 ψ hreal n hopen
  exact ⟨NLS.ComplexAnalysis.integral_sub_mul_deriv_div_sqrt_sq_sub_one_eq_neg_arcosh
      g (deriv g) a b q hopen hcont hderiv hleft hright hgt hint,
    NLS.ComplexAnalysis.integral_sub_mul_deriv_div_sqrt_sq_sub_one_neg
      g (deriv g) a b q hopen hcont hderiv hleft hright hgt hint⟩

end NLS.ZakharovShabat
