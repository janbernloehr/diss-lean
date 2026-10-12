import NLS.Poisson.SobolevBivector

/-! # Endpoint Poisson pairing for represented gradients

The (1,infinity) gradient pairing uses both original source pair norms.
It is absolutely convergent and continuously bilinear. This supplies a
bracket when endpoint gradients are given; it does not assert that an
arbitrary infinity-source functional has a coefficient gradient.
-/
noncomputable section
open scoped ENNReal
namespace NLS.Poisson

/-- The original endpoint gradient norms, with the printed -iJ pairing. -/
def oneInfinityBivector (s : ℝ) :
    WeightedCoeffPair (Weight.sobolev s) 1 →L[ℂ]
      WeightedCoeffPairInfty (Weight.sobolev (-s)) →L[ℂ] ℂ :=
  (signedBivector (p := 1) (q := ⊤) s).bilinearComp
    (WeightedCoeffPair.toMax (Weight.sobolev s) 1).toContinuousLinearMap
    (WeightedCoeffPairInfty.toMax (Weight.sobolev (-s))).toContinuousLinearMap

/-- Endpoint boundedness uses the original l1 pair norm and frequencywise sum infinity norm. -/
theorem norm_oneInfinityBivector_le (s : ℝ)
    (a : WeightedCoeffPair (Weight.sobolev s) 1) (b : WeightedCoeffPairInfty (Weight.sobolev (-s))) :
    ‖oneInfinityBivector s a b‖ ≤ 2*‖a‖*‖b‖ := by
  apply (norm_signedBivector_le s _ _).trans
  exact mul_le_mul
    (mul_le_mul_of_nonneg_left (WeightedCoeffPair.norm_toMax_le _ a) (by norm_num))
    (WeightedCoeffPairInfty.norm_toMax_le _ b) (norm_nonneg _) (by positivity)

/-- The same physical matrix and sign hold at the endpoint. -/
theorem oneInfinityBivector_physical (s : ℝ)
    (a : WeightedCoeffPair (Weight.sobolev s) 1) (b : WeightedCoeffPairInfty (Weight.sobolev (-s))) :
    oneInfinityBivector s a b = -Complex.I *
      (WeightedCoeff.sobolevBilinearPairing s (WeightedCoeff.reflection s a.fst) b.2 -
        WeightedCoeff.sobolevBilinearPairing s a.snd (WeightedCoeff.reflection (-s) b.1)) :=
  signedBivector_physical s _ _

theorem oneInfinityBivector_summable (s : ℝ)
    (a : WeightedCoeffPair (Weight.sobolev s) 1) (b : WeightedCoeffPairInfty (Weight.sobolev (-s))) :
    Summable (fun n : ℤ => ‖a.fst.val n*b.2.val n-a.snd.val n*b.1.val n‖) :=
  summable_signed_cross s _ _

theorem oneInfinityBivector_eq_tsum (s : ℝ)
    (a : WeightedCoeffPair (Weight.sobolev s) 1) (b : WeightedCoeffPairInfty (Weight.sobolev (-s))) :
    oneInfinityBivector s a b = -Complex.I * ∑' n : ℤ,
      (a.fst.val n*b.2.val n-a.snd.val n*b.1.val n) :=
  signedBivector_eq_tsum s _ _

/-- Analytic represented gradient fields give an analytic endpoint bracket. -/
theorem analyticOnNhd_oneInfinityBivector {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (s : ℝ) (a : E → WeightedCoeffPair (Weight.sobolev s) 1)
    (b : E → WeightedCoeffPairInfty (Weight.sobolev (-s))) {U : Set E}
    (ha : AnalyticOnNhd ℂ a U) (hb : AnalyticOnNhd ℂ b U) :
    AnalyticOnNhd ℂ (fun x => oneInfinityBivector s (a x) (b x)) U := by
  intro x hx
  exact ((oneInfinityBivector s).analyticAt_bilinear _).comp₂ (ha x hx) (hb x hx)

end NLS.Poisson
