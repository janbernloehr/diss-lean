import NLS.ZakharovShabat.SmoothPeriodOneSource
import NLS.ZakharovShabat.ClassicalNLSNonextension

/-! # Smooth physical sources at every sequence exponent

The H¹ coefficients of a smooth period-one function are absolutely summable.
Their inclusion into any source exponent keeps the original Fourier integrals
and commutes with every coefficient-preserving exponent inclusion.
-/
noncomputable section
open Set NLS.Fourier
open scoped ENNReal ContDiff
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- Canonical real source of smooth physical data at any exponent at least one. -/
def smoothPeriodOneSourceAt (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (f : C(AddCircle (2 : ℝ), ℂ))
    (hf : ContDiff ℝ ∞ (fun x : ℝ => f (x : AddCircle (2 : ℝ))))
    (hp : Function.Periodic (fun x : ℝ => f (x : AddCircle (2 : ℝ))) 1) :
    realTypeSourceSubmodule p :=
  let a := smoothPeriodOneSource f hf hp
  let L := (Coeff.exponentInclusion (Fact.out : 1 ≤ p)).comp
    (WeightedCoeff.sobolevToL1CLM 2 (by simp))
  ⟨(CoeffPair.toMax p).symm (L a.val.1,L a.val.2),by
    intro n
    change L a.val.2 n = (starRingEnd ℂ) (L a.val.1 (-n))
    simp only [L,ContinuousLinearMap.comp_apply,Coeff.exponentInclusion_apply,
      WeightedCoeff.sobolevToL1CLM_apply]
    have hr := a.property n
    change (sobolevSourceInclusion a.val).snd n =
      (starRingEnd ℂ) ((sobolevSourceInclusion a.val).fst (-n)) at hr
    simpa only [sobolevSourceInclusion_snd,sobolevSourceInclusion_fst] using hr⟩

@[simp] theorem smoothPeriodOneSourceAt_fst (f : C(AddCircle (2 : ℝ), ℂ))
    (hf : ContDiff ℝ ∞ (fun x : ℝ => f (x : AddCircle (2 : ℝ))))
    (hp : Function.Periodic (fun x : ℝ => f (x : AddCircle (2 : ℝ))) 1) (n : ℤ) :
    (smoothPeriodOneSourceAt p f hf hp).val.fst n =
      periodOneCoefficient (fun x : ℝ => f (x : AddCircle (2 : ℝ))) n := by
  exact WeightedCoeff.sobolevToL1CLM_apply 2 (by simp) _ n

/-- The exponent-two construction is the original canonical Hilbert source. -/
@[simp] theorem smoothPeriodOneSourceAt_two (f : C(AddCircle (2 : ℝ), ℂ))
    (hf : ContDiff ℝ ∞ (fun x : ℝ => f (x : AddCircle (2 : ℝ))))
    (hp : Function.Periodic (fun x : ℝ => f (x : AddCircle (2 : ℝ))) 1) :
    smoothPeriodOneSourceAt 2 f hf hp = smoothPeriodOneHilbertSource f hf hp := by
  apply realTypeSource_eq_of_fst
  intro n
  exact (smoothPeriodOneSourceAt_fst f hf hp n).trans (smoothPeriodOneHilbertSource_fst f hf hp n).symm

/-- Exponent changes preserve the canonical smooth physical source. -/
@[simp] theorem smoothPeriodOneSourceAt_exponent (hpq : p ≤ q)
    (f : C(AddCircle (2 : ℝ), ℂ))
    (hf : ContDiff ℝ ∞ (fun x : ℝ => f (x : AddCircle (2 : ℝ))))
    (hp : Function.Periodic (fun x : ℝ => f (x : AddCircle (2 : ℝ))) 1) :
    realTypeSourceExponentInclusion hpq (smoothPeriodOneSourceAt p f hf hp) =
      smoothPeriodOneSourceAt q f hf hp := by
  apply realTypeSource_eq_of_fst
  intro n
  exact (smoothPeriodOneSourceAt_fst (p := p) f hf hp n).trans
    (smoothPeriodOneSourceAt_fst (p := q) f hf hp n).symm

end NLS.ZakharovShabat
