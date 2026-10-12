import NLS.ZakharovShabat.SourceParity
import NLS.ZakharovShabat.SourceResolventContours

/-! # Lemma 3.6 in the original source norms

Even potential support preserves each parity on the original one-derivative
domain. The canonical period-one embedding supplies this hypothesis.
An explicit odd potential shows why it cannot be dropped.
-/
noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem sourceOperator_mem_sourceParitySubspace (hp : p ≠ ⊤) (φ : CoeffPair p) (hφ : φ ∈ sourceParitySubspace 0)
    (r : ℤ) (a : WeightedCoeffPair (Weight.sobolev 1) p) (ha : a ∈ sourceDomainParitySubspace r) :
    sourceOperator hp φ a ∈ sourceParitySubspace r := by
  change (CoeffPair.toMax p) ((CoeffPair.toMax p).symm
    (operator hp (CoeffPair.toMax p φ) (WeightedCoeffPair.toMax (Weight.sobolev 1) p a))) ∈ pairParitySubspace r
  rw [ContinuousLinearEquiv.apply_symm_apply]
  exact operator_mem_pairParitySubspace hp _ hφ r _ ha

/-- Lemma 3.6 for every finite Banach exponent, with period one expressed canonically. -/
theorem sourceLemma3_6 (hp : p ≠ ⊤) (φ : CoeffPair p) (r : ℤ)
    (a : WeightedCoeffPair (Weight.sobolev 1) p) (ha : a ∈ sourceDomainParitySubspace r) :
    sourceOperator hp (periodOnePair φ) a ∈ sourceParitySubspace r :=
  sourceOperator_mem_sourceParitySubspace hp _ (periodOnePotential_mem φ) r a ha

theorem sourceParityProjection_commute_resolvent (hp : p ≠ ⊤) (φ : CoeffPair p) (hφ : φ ∈ sourceParitySubspace 0) (r : ℤ)
    (z : ℂ) (hz : z ∈ sourceResolventSet hp φ) : Commute (sourceParityProjection r) (sourceResolvent hp φ z) := by
  exact (pairParityProjection_commute_resolvent hp (CoeffPair.toMax p φ) hφ r z
    (by rwa [sourceResolventSet_eq] at hz)).map ((CoeffPair.toMax p).symm.conjContinuousAlgEquiv)

theorem sourceParityProjection_commute_circleIntegral (hp : p ≠ ⊤) (φ : CoeffPair p) (hφ : φ ∈ sourceParitySubspace 0) (r : ℤ)
    (c : ℂ) (R : ℝ) (hR : 0 ≤ R) (hc : Metric.sphere c R ⊆ sourceResolventSet hp φ) :
    Commute (sourceParityProjection r) (sourceResolventCircleIntegral hp φ c R) := by
  rw [sourceResolventCircleIntegral_eq_conj hp φ c R hR hc]
  exact (pairParityProjection_commute_contour hp (CoeffPair.toMax p φ) hφ r c R hR
    (by rwa [sourceResolventSet_eq] at hc)).map ((CoeffPair.toMax p).symm.conjContinuousAlgEquiv)

theorem sourceOperator_domainParityProjection (hp : p ≠ ⊤) (φ : CoeffPair p) (hφ : φ ∈ sourceParitySubspace 0) (r : ℤ)
    (a : WeightedCoeffPair (Weight.sobolev 1) p) :
    sourceOperator hp φ (sourceDomainParityProjection r a) = sourceParityProjection r (sourceOperator hp φ a) := by
  change (CoeffPair.toMax p).symm (operator hp (CoeffPair.toMax p φ)
    ((WeightedCoeffPair.toMax (Weight.sobolev 1) p) ((WeightedCoeffPair.toMax (Weight.sobolev 1) p).symm
      (domainParityProjection r (WeightedCoeffPair.toMax (Weight.sobolev 1) p a))))) =
    (CoeffPair.toMax p).symm (pairParityProjection r ((CoeffPair.toMax p) ((CoeffPair.toMax p).symm
      (operator hp (CoeffPair.toMax p φ) (WeightedCoeffPair.toMax (Weight.sobolev 1) p a)))))
  rw [ContinuousLinearEquiv.apply_symm_apply,ContinuousLinearEquiv.apply_symm_apply]
  exact congrArg (CoeffPair.toMax p).symm
    (operator_domainParityProjection hp (CoeffPair.toMax p φ) hφ r
      (WeightedCoeffPair.toMax (Weight.sobolev 1) p a))

def lemma3_6OddPotential : CoeffPair 1 := (CoeffPair.toMax 1).symm (lp.single 1 1 1,0)
def lemma3_6EvenInput : WeightedCoeffPair (Weight.sobolev 1) 1 :=
  (WeightedCoeffPair.toMax (Weight.sobolev 1) 1).symm (positiveMode 0)

/-- The counterexample input is a genuine even vector in the operator domain. -/
theorem lemma3_6EvenInput_mem : lemma3_6EvenInput ∈ sourceDomainParitySubspace 0 := by
  change (WeightedCoeffPair.toMax (Weight.sobolev 1) 1)
    ((WeightedCoeffPair.toMax (Weight.sobolev 1) 1).symm (positiveMode 0)) ∈ domainParitySubspace 0
  rw [ContinuousLinearEquiv.apply_symm_apply]
  exact positiveMode_mem_domainParitySubspace 0

/-- Dropping the period-one hypothesis fails already for an input in a single even mode. -/
theorem lemma3_6_even_support_needed : sourceOperator (by norm_num) lemma3_6OddPotential lemma3_6EvenInput ∉ sourceParitySubspace 0 := by
  intro h
  have hz := ((mem_sourceParitySubspace 0 _).mp h 1 (by norm_num)).1
  have hv : (sourceOperator (by norm_num) lemma3_6OddPotential lemma3_6EvenInput).fst 1 = 1 := by
    change (operator (by norm_num) (lp.single 1 1 1,0) (positiveMode 0)).1 1 = 1
    simp [operator_fst_apply,positiveMode,lp.single_apply,Pi.single_apply]
  rw [hv] at hz
  exact one_ne_zero hz

end NLS.ZakharovShabat
