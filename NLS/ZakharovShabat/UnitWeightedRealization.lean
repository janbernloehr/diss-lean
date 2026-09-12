import NLS.ZakharovShabat.WeightedDomainPotential
import NLS.ZakharovShabat.PeriodicSpectrum

/-!
# Unit-weight realization of the original periodic operator

These coefficient-preserving equivalences connect the exact source pair norm
to the existing periodic operator and its full one-derivative domain. In
particular, the unit-weight eigenvector condition is the original periodic
spectral condition, with both directions and nonzero vectors preserved.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The unit-weight base space is continuously equivalent to the original pair space. -/
def unitBaseEquiv : WeightedCoeffPair SpectralWeight.one.toWeight p ≃L[ℂ] PairSpace p :=
  (WeightedCoeffPair.toMax SpectralWeight.one.toWeight p).trans
    ((WeightedCoeff.weightIsometry SpectralWeight.one.toWeight p).toContinuousLinearEquiv.prodCongr
      (WeightedCoeff.weightIsometry SpectralWeight.one.toWeight p).toContinuousLinearEquiv)

@[simp] theorem unitBaseEquiv_fst (f : WeightedCoeffPair SpectralWeight.one.toWeight p) (k : ℤ) :
    (unitBaseEquiv f).1 k = f.fst.val k := by
  change (SpectralWeight.one k : ℂ) * f.fst.val k = _
  simp
@[simp] theorem unitBaseEquiv_snd (f : WeightedCoeffPair SpectralWeight.one.toWeight p) (k : ℤ) :
    (unitBaseEquiv f).2 k = f.snd.val k := by
  change (SpectralWeight.one k : ℂ) * f.snd.val k = _
  simp

theorem unitBaseEquiv_eq (f : WeightedCoeffPair SpectralWeight.one.toWeight p) :
    unitBaseEquiv f = weightedBaseToPair SpectralWeight.one f := by
  apply Prod.ext <;> ext k <;> simp

/-- The unit-weight derivative is the ordinary one-derivative scalar domain. -/
def unitScalarDomainEquiv :
    WeightedCoeff SpectralWeight.one.toWeight.oneDerivative p ≃ₗᵢ[ℂ] ScalarDomain p :=
  (WeightedCoeff.weightIsometry SpectralWeight.one.toWeight.oneDerivative p).trans
    (WeightedCoeff.weightIsometry (Weight.sobolev 1) p).symm

@[simp] theorem unitScalarDomainEquiv_apply (f : WeightedCoeff SpectralWeight.one.toWeight.oneDerivative p) (k : ℤ) :
    (unitScalarDomainEquiv f).val k = f.val k := by
  change ((SpectralWeight.one.toWeight.oneDerivative k : ℂ) * f.val k) / (Weight.sobolev 1 k : ℂ) = _
  have hw : SpectralWeight.one.toWeight.oneDerivative k = Weight.sobolev 1 k := by
    simp [Weight.oneDerivative_apply, Weight.sobolev_apply]
  rw [hw]
  exact mul_div_cancel_left₀ _ ((Weight.sobolev 1).complex_ne_zero k)

/-- The full unit-weight derivative domain is the original operator domain. -/
def unitDomainEquiv : WeightedDomain SpectralWeight.one.toWeight p ≃L[ℂ] Domain p :=
  (WeightedCoeffPair.toMax SpectralWeight.one.toWeight.oneDerivative p).trans
    (unitScalarDomainEquiv.toContinuousLinearEquiv.prodCongr unitScalarDomainEquiv.toContinuousLinearEquiv)

@[simp] theorem unitDomainEquiv_fst (f : WeightedDomain SpectralWeight.one.toWeight p) (k : ℤ) :
    (unitDomainEquiv f).1.val k = f.fst.val k := unitScalarDomainEquiv_apply _ _
@[simp] theorem unitDomainEquiv_snd (f : WeightedDomain SpectralWeight.one.toWeight p) (k : ℤ) :
    (unitDomainEquiv f).2.val k = f.snd.val k := unitScalarDomainEquiv_apply _ _

theorem unitDomainEquiv_eq (f : WeightedDomain SpectralWeight.one.toWeight p) :
    unitDomainEquiv f = weightedDomainToDomain SpectralWeight.one f := by
  apply Prod.ext <;> apply Subtype.ext <;> funext k <;> simp

/-- The unit-weight differential equation is exactly the original periodic eigenvector equation. -/
theorem unit_weighted_eigen_equation_iff (hp : p ≠ ⊤)
    (φ : WeightedCoeffPair SpectralWeight.one.toWeight p) (z : ℂ)
    (f : WeightedDomain SpectralWeight.one.toWeight p) :
    weightedFreePencil SpectralWeight.one.toWeight z f = weightedDomainPotential hp SpectralWeight.one φ f ↔
      operator hp (weightedBaseToPair SpectralWeight.one φ) (unitDomainEquiv f) =
        z • domainInclusion (unitDomainEquiv f) := by
  rw [← (unitBaseEquiv (p := p)).injective.eq_iff]
  rw [unitBaseEquiv_eq, unitBaseEquiv_eq, weightedFreePencil_eq_original, weightedDomainPotential_eq_original,
    ← unitDomainEquiv_eq]
  change z • domainInclusion (unitDomainEquiv f) - freeOperator (unitDomainEquiv f) =
    potentialOperator hp (weightedBaseToPair SpectralWeight.one φ) (unitDomainEquiv f) ↔
    freeOperator (unitDomainEquiv f) + potentialOperator hp (weightedBaseToPair SpectralWeight.one φ) (unitDomainEquiv f) =
      z • domainInclusion (unitDomainEquiv f)
  constructor <;> intro he
  · rw [sub_eq_iff_eq_add] at he
    exact (he.trans (add_comm _ _)).symm
  · apply sub_eq_iff_eq_add.mpr
    exact he.symm.trans (add_comm _ _)

/-- Both realizations have exactly the same periodic eigenvalues. -/
theorem unit_weighted_eigenvector_iff_periodicSpectrum (hp : p ≠ ⊤)
    (φ : WeightedCoeffPair SpectralWeight.one.toWeight p) (z : ℂ) :
    (∃ f : WeightedDomain SpectralWeight.one.toWeight p, f ≠ 0 ∧
      weightedFreePencil SpectralWeight.one.toWeight z f = weightedDomainPotential hp SpectralWeight.one φ f) ↔
      z ∈ periodicSpectrum hp (weightedBaseToPair SpectralWeight.one φ) := by
  rw [mem_periodicSpectrum_iff_exists_eigenvector]
  constructor
  · rintro ⟨f, hf, he⟩
    refine ⟨unitDomainEquiv f, ?_, (unit_weighted_eigen_equation_iff hp φ z f).mp he⟩
    intro he0
    apply hf
    apply (unitDomainEquiv (p := p)).injective
    simpa only [map_zero] using he0
  · rintro ⟨f, hf, he⟩
    refine ⟨(unitDomainEquiv (p := p)).symm f, ?_, ?_⟩
    · intro he0
      apply hf
      apply (unitDomainEquiv (p := p)).symm.injective
      simpa only [map_zero] using he0
    · apply (unit_weighted_eigen_equation_iff hp φ z _).mpr
      simpa only [ContinuousLinearEquiv.apply_symm_apply] using he

end NLS.ZakharovShabat
