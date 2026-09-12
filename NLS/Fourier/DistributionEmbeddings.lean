import NLS.Fourier.WeightedDistributionIdentification
import NLS.SequenceSpaces.HolderEmbedding

/-!
# Intrinsic Fourier regularity under exponent and Hölder embeddings

The sequence embeddings preserve the actual tempered distribution. Thus their
norm and regularity statements concern the same object across Banach exponents,
including the infinity endpoint and negative real Sobolev regularities.
-/

noncomputable section
open scoped ENNReal SchwartzMap
namespace NLS.Fourier
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- Increasing exponent does not change the represented distribution. -/
theorem weightedDistributionSynthesis_exponentInclusion (w : Weight)
    (hw : w.HasTemperedInverse) (hpq : p ≤ q) (a : WeightedCoeff w p) :
    weightedDistributionSynthesis w hw (WeightedCoeff.exponentInclusion w hpq a) =
      weightedDistributionSynthesis w hw a :=
  (weightedDistributionSynthesis_eq_iff _ _ _ _ _ _).mpr
    (fun n => WeightedCoeff.exponentInclusion_apply w hpq a n)

/-- Decreasing regularity and increasing exponent preserve the actual Sobolev distribution. -/
theorem sobolevDistributionSynthesis_exponentInclusion {s t : ℝ} (hst : t ≤ s) (hpq : p ≤ q)
    (a : WeightedCoeff (Weight.sobolev s) p) :
    sobolevDistributionSynthesisCLM t (WeightedCoeff.sobolevExponentInclusion hst hpq a) =
      sobolevDistributionSynthesisCLM s a :=
  (weightedDistributionSynthesis_eq_iff _ _ _ _ _ _).mpr
    (fun n => WeightedCoeff.sobolevExponentInclusion_apply hst hpq a n)

variable {r : ℝ≥0∞} [Fact (1 ≤ r)] [p.HolderTriple r q]

/-- Weighted Hölder embeddings preserve the raw distribution, even when the exponent decreases. -/
theorem weightedDistributionSynthesis_holderInclusion (w v : Weight)
    (hw : w.HasTemperedInverse) (hv : v.HasTemperedInverse)
    (h : Memℓp (fun n : ℤ => (v n : ℂ) / (w n : ℂ)) r) (a : WeightedCoeff w p) :
    weightedDistributionSynthesis v hv (WeightedCoeff.holderInclusion (q := q) w v h a) =
      weightedDistributionSynthesis w hw a :=
  (weightedDistributionSynthesis_eq_iff _ _ _ _ _ _).mpr
    (fun n => WeightedCoeff.holderInclusion_apply w v h a n)

/-- The strict Sobolev Hölder embedding concerns the same actual periodic distribution. -/
theorem sobolevDistributionSynthesis_holderInclusion (s t : ℝ) (hr : r ≠ ⊤)
    (h : 1 < (s - t) * r.toReal) (a : WeightedCoeff (Weight.sobolev s) p) :
    sobolevDistributionSynthesisCLM t (WeightedCoeff.sobolevHolderInclusion (q := q) s t hr h a) =
      sobolevDistributionSynthesisCLM s a :=
  (weightedDistributionSynthesis_eq_iff _ _ _ _ _ _).mpr
    (fun n => WeightedCoeff.sobolevHolderInclusion_apply s t hr h a n)

/-- An arbitrary periodic input gains the target Fourier exponent under the Sobolev Hölder condition. -/
theorem periodicDistribution_sobolevHolder_existsUnique (s t : ℝ) (hr : r ≠ ⊤)
    (h : 1 < (s - t) * r.toReal) (T : 𝓢'(ℝ, ℂ)) (hT : IsPeriodTwoDistribution T)
    (ha : Memℓp (fun n : ℤ => (Weight.sobolev s n : ℂ) * T (coefficientTest n)) p) :
    ∃! b : WeightedCoeff (Weight.sobolev t) q, sobolevDistributionSynthesisCLM t b = T := by
  obtain ⟨a, ha, _⟩ := (periodicDistribution_sobolev_memlp_iff_existsUnique s T).mp ⟨hT, ha⟩
  let b := WeightedCoeff.sobolevHolderInclusion (q := q) s t hr h a
  have hb : sobolevDistributionSynthesisCLM t b = T :=
    (sobolevDistributionSynthesis_holderInclusion s t hr h a).trans ha
  exact ⟨b, hb, fun c hc => weightedDistributionSynthesis_injective _ _ (hc.trans hb.symm)⟩

end NLS.Fourier
