import NLS.ZakharovShabat.SourceComplementaryCorrection
import NLS.ZakharovShabat.UnitWeightedRealization

/-!
# The Q-equation in the original differential domain

Unit weighting identifies the entire source derivative domain. The actual
Q-solution belongs to that domain and solves the original projected equation
uniquely. All statements include the endpoint p=1.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Unit weighting identifies the full original derivative domain, preserving raw coefficients. -/
def sourceUnitDomainEquiv : WeightedDomain SpectralWeight.one.toWeight p ≃L[ℂ]
    WeightedCoeffPair (Weight.sobolev 1) p :=
  unitDomainEquiv.trans (WeightedCoeffPair.toMax (Weight.sobolev 1) p).symm

@[simp] theorem sourceUnitDomainEquiv_apply (f : WeightedDomain SpectralWeight.one.toWeight p) :
    sourceUnitDomainEquiv f = sourceWeightedDomainInput SpectralWeight.one f := by
  change (WeightedCoeffPair.toMax (Weight.sobolev 1) p).symm (unitDomainEquiv f) = _
  rw [unitDomainEquiv_eq]
  rfl

/-- Forgetting the domain weight commutes with the actual complementary projection. -/
theorem sourceWeightedDomainInput_complementary (w : SpectralWeight) (n : ℤ)
    (f : WeightedDomain w.toWeight p) :
    sourceWeightedDomainInput w (complementaryProjection w.toWeight.oneDerivative n f) =
      complementaryProjection (Weight.sobolev 1) n (sourceWeightedDomainInput w f) := by
  apply weightedPair_ext <;> intro k <;> simp

/-- The complementary projection on the original coefficient pair. -/
def sourceComplementaryProjection (n : ℤ) : CoeffPair p →L[ℂ] CoeffPair p :=
  unitWeightedPairEquiv.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((complementaryProjection SpectralWeight.one.toWeight n).comp
      unitWeightedPairEquiv.toContinuousLinearEquiv.toContinuousLinearMap)

theorem sourceComplementaryProjection_weightedInput (w : SpectralWeight) (n : ℤ)
    (f : WeightedCoeffPair w.toWeight p) :
    sourceComplementaryProjection n (sourceWeightedPeriodTwoInput w f) =
      sourceWeightedPeriodTwoInput w (complementaryProjection w.toWeight n f) := by
  apply unitWeightedPairEquiv.injective
  simp only [sourceComplementaryProjection, ContinuousLinearMap.comp_apply,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.apply_symm_apply, unitWeightedPairEquiv_sourceWeightedInput]
  apply weightedPair_ext <;> intro k <;> simp

/-- The actual original Q-equation is equivalent to its weighted realization. -/
theorem sourceQEquation_iff (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (u v : WeightedDomain w.toWeight p) :
    sourceSpectralPencil hp 0 z (sourceWeightedDomainInput w v) =
      sourceComplementaryProjection n
        (sourceOperator hp (sourceWeightedPeriodTwoInput w φ) (sourceWeightedDomainInput w (u+v)) -
          sourceOperator hp 0 (sourceWeightedDomainInput w (u+v))) ↔
    weightedFreePencil w.toWeight z v =
      complementaryProjection w.toWeight n (weightedDomainPotential hp w φ (u+v)) := by
  rw [sourceWeightedFreePencil_eq, ← sourceWeightedDomainPotential_eq,
    sourceComplementaryProjection_weightedInput]
  exact (sourceWeightedPeriodTwoInput_injective w).eq_iff

/-- The unique complementary solution, valued in the full original derivative domain. -/
def sourceQSolution (hp : p ≠ ⊤) (φ : CoeffPair p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp SpectralWeight.one (unitWeightedPairEquiv φ) n z hz‖ < 1) :
    WeightedCoeffPair (Weight.sobolev 1) p →L[ℂ] WeightedCoeffPair (Weight.sobolev 1) p :=
  sourceUnitDomainEquiv.toContinuousLinearMap.comp
    ((weightedQSolution hp SpectralWeight.one (unitWeightedPairEquiv φ) n z hz h).comp
      sourceUnitDomainEquiv.symm.toContinuousLinearMap)

@[simp] theorem sourceQSolution_unitDomain (hp : p ≠ ⊤) (φ : CoeffPair p)
    (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp SpectralWeight.one (unitWeightedPairEquiv φ) n z hz‖ < 1)
    (u : WeightedDomain SpectralWeight.one.toWeight p) :
    sourceQSolution hp φ n z hz h (sourceUnitDomainEquiv u) =
      sourceUnitDomainEquiv (weightedQSolution hp SpectralWeight.one (unitWeightedPairEquiv φ) n z hz h u) := by
  simp only [sourceQSolution, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_apply_apply]

/-- The constructed solution is in Q_n in the original one-derivative domain. -/
theorem sourceQSolution_nonresonant (hp : p ≠ ⊤) (φ : CoeffPair p)
    (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp SpectralWeight.one (unitWeightedPairEquiv φ) n z hz‖ < 1)
    (u : WeightedCoeffPair (Weight.sobolev 1) p) :
    complementaryProjection (Weight.sobolev 1) n (sourceQSolution hp φ n z hz h u) =
      sourceQSolution hp φ n z hz h u := by
  obtain ⟨u,rfl⟩ := (sourceUnitDomainEquiv (p := p)).surjective u
  rw [sourceQSolution_unitDomain, sourceUnitDomainEquiv_apply,
    ← sourceWeightedDomainInput_complementary, weightedQSolution_nonresonant]

/-- The constructed solution satisfies the actual projected source differential equation. -/
theorem sourceQSolution_equation (hp : p ≠ ⊤) (φ : CoeffPair p)
    (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp SpectralWeight.one (unitWeightedPairEquiv φ) n z hz‖ < 1)
    (u : WeightedCoeffPair (Weight.sobolev 1) p) :
    sourceSpectralPencil hp 0 z (sourceQSolution hp φ n z hz h u) =
      sourceComplementaryProjection n
        (sourceOperator hp φ (u+sourceQSolution hp φ n z hz h u) -
          sourceOperator hp 0 (u+sourceQSolution hp φ n z hz h u)) := by
  obtain ⟨u,rfl⟩ := (sourceUnitDomainEquiv (p := p)).surjective u
  rw [sourceQSolution_unitDomain]
  have he := (sourceQEquation_iff hp SpectralWeight.one (unitWeightedPairEquiv φ) n z u
    (weightedQSolution hp SpectralWeight.one (unitWeightedPairEquiv φ) n z hz h u)).mpr
      (weightedQSolution_equation hp SpectralWeight.one (unitWeightedPairEquiv φ) n z hz h u)
  simpa only [sourceQSolution_unitDomain, sourceUnitDomainEquiv_apply,
    sourceWeightedInput_unitWeightedPairEquiv, map_add] using he

/-- Every original-domain complementary solution is the reconstructed one. -/
theorem sourceQSolution_unique (hp : p ≠ ⊤) (φ : CoeffPair p)
    (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp SpectralWeight.one (unitWeightedPairEquiv φ) n z hz‖ < 1)
    (u v : WeightedCoeffPair (Weight.sobolev 1) p)
    (hv : complementaryProjection (Weight.sobolev 1) n v = v)
    (he : sourceSpectralPencil hp 0 z v = sourceComplementaryProjection n
      (sourceOperator hp φ (u+v) - sourceOperator hp 0 (u+v))) :
    v = sourceQSolution hp φ n z hz h u := by
  obtain ⟨u,rfl⟩ := (sourceUnitDomainEquiv (p := p)).surjective u
  obtain ⟨v,rfl⟩ := (sourceUnitDomainEquiv (p := p)).surjective v
  have hv' : complementaryProjection SpectralWeight.one.toWeight.oneDerivative n v = v := by
    apply sourceWeightedDomainInput_injective SpectralWeight.one
    simpa only [sourceUnitDomainEquiv_apply, sourceWeightedDomainInput_complementary] using hv
  have he' := (sourceQEquation_iff hp SpectralWeight.one (unitWeightedPairEquiv φ) n z u v).mp
    (by simpa only [sourceUnitDomainEquiv_apply, sourceWeightedInput_unitWeightedPairEquiv, map_add] using he)
  rw [sourceQSolution_unitDomain, ← weightedQSolution_unique hp SpectralWeight.one
    (unitWeightedPairEquiv φ) n z hz h u v hv' he']

/-- The displayed Φv=T̂_n T_n Φu identity uses the original-source correction. -/
theorem sourceQSolution_potential (hp : p ≠ ⊤) (φ : CoeffPair p)
    (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp SpectralWeight.one (unitWeightedPairEquiv φ) n z hz‖ < 1)
    (hs : ‖(sourcePotentialInverse hp φ n z hz).comp (sourcePotentialInverse hp φ n z hz)‖ < 1)
    (u : WeightedCoeffPair (Weight.sobolev 1) p) :
    sourceOperator hp φ (sourceQSolution hp φ n z hz h u) -
      sourceOperator hp 0 (sourceQSolution hp φ n z hz h u) =
    sourceComplementaryCorrection hp φ n z hz hs
      (sourcePotentialInverse hp φ n z hz (sourceOperator hp φ u - sourceOperator hp 0 u)) := by
  obtain ⟨u,rfl⟩ := (sourceUnitDomainEquiv (p := p)).surjective u
  have hs' : ‖(sourcePotentialInverse hp
      (sourceWeightedPeriodTwoInput SpectralWeight.one (unitWeightedPairEquiv φ)) n z hz).comp
      (sourcePotentialInverse hp
        (sourceWeightedPeriodTwoInput SpectralWeight.one (unitWeightedPairEquiv φ)) n z hz)‖ < 1 := by
    simpa only [sourceWeightedInput_unitWeightedPairEquiv] using hs
  have he := sourceComplementaryCorrection_weightedInput hp SpectralWeight.one
    (unitWeightedPairEquiv φ) n z hz h hs'
    (weightedPotentialInverse hp SpectralWeight.one (unitWeightedPairEquiv φ) n z hz
      (weightedDomainPotential hp SpectralWeight.one (unitWeightedPairEquiv φ) u))
  rw [← weightedQSolution_potential_source, ← sourcePotentialInverse_weightedInput,
    sourceWeightedDomainPotential_eq, sourceWeightedDomainPotential_eq] at he
  rw [sourceQSolution_unitDomain]
  simpa only [sourceUnitDomainEquiv_apply, sourceWeightedInput_unitWeightedPairEquiv] using he

/-- The Q-equation has exactly one original-domain complementary solution for every input. -/
theorem exists_unique_sourceQSolution (hp : p ≠ ⊤) (φ : CoeffPair p)
    (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp SpectralWeight.one (unitWeightedPairEquiv φ) n z hz‖ < 1)
    (u : WeightedCoeffPair (Weight.sobolev 1) p) :
    ∃! v : WeightedCoeffPair (Weight.sobolev 1) p,
      complementaryProjection (Weight.sobolev 1) n v = v ∧
      sourceSpectralPencil hp 0 z v = sourceComplementaryProjection n
        (sourceOperator hp φ (u+v) - sourceOperator hp 0 (u+v)) := by
  exact ⟨sourceQSolution hp φ n z hz h u,
    ⟨sourceQSolution_nonresonant hp φ n z hz h u, sourceQSolution_equation hp φ n z hz h u⟩,
    fun v hv => sourceQSolution_unique hp φ n z hz h u v hv.1 hv.2⟩

end NLS.ZakharovShabat
