import NLS.ZakharovShabat.SourceLemma4_3
import NLS.ZakharovShabat.SourceResolvent
import NLS.ZakharovShabat.PeriodOneBoundaryAsymptotics
import NLS.ZakharovShabat.SourceBoundaryFourier

/-!
# Lemma 4.4 in the original Fourier–Lebesgue norms

The actual operator preserves each boundary space when the potential is
Dirichlet-reflected. Its restriction is bounded from the original one-derivative
domain to the original base space. The free mode action and the potential's
signed, unconditionally convergent mode expansion agree with page 32.
The interval extension requires 1<p<infinity; the restriction itself also
works at p=1 for an already-reflected potential. No source infinity norm is
identified with the auxiliary maximum norm.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
open BoundaryCondition
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The original component-sum base space with the selected boundary symmetry. -/
def sourceBoundaryBaseSubspace (b : BoundaryCondition) : Submodule ℂ (CoeffPair p) :=
  (space b).comap (CoeffPair.toMax p).toLinearMap

theorem mem_sourceBoundaryBaseSubspace (b : BoundaryCondition) (a : CoeffPair p) :
    a ∈ sourceBoundaryBaseSubspace b ↔ ∀ n : ℤ, a.fst n = b.extensionSign * a.snd (-n) := by
  cases b
  · change CoeffPair.toMax p a ∈ dirichletSubspace ↔ _
    simp [mem_dirichletSubspace, extensionSign]
  · change CoeffPair.toMax p a ∈ neumannSubspace ↔ _
    simp [mem_neumannSubspace, extensionSign]

/-- Removing the zero Sobolev weight preserves the original norm exactly. -/
def sourceBoundaryZeroWeightEquiv : WeightedCoeffPair (Weight.sobolev 0) p ≃ₗᵢ[ℂ] CoeffPair p :=
  (WeightedCoeff.weightIsometry (Weight.sobolev 0) p).withLpProdCongr p
    (WeightedCoeff.weightIsometry (Weight.sobolev 0) p)

theorem sourceBoundaryZeroWeightEquiv_fst (a : WeightedCoeffPair (Weight.sobolev 0) p) (n : ℤ) :
    (sourceBoundaryZeroWeightEquiv a).fst n = a.fst.val n := by
  change (Weight.sobolev 0 n : ℂ) * a.fst.val n = _
  simp

theorem sourceBoundaryZeroWeightEquiv_snd (a : WeightedCoeffPair (Weight.sobolev 0) p) (n : ℤ) :
    (sourceBoundaryZeroWeightEquiv a).snd n = a.snd.val n := by
  change (Weight.sobolev 0 n : ℂ) * a.snd.val n = _
  simp

theorem sourceBoundaryZeroWeightEquiv_mem (b : BoundaryCondition) (a : WeightedCoeffPair (Weight.sobolev 0) p) :
    sourceBoundaryZeroWeightEquiv a ∈ sourceBoundaryBaseSubspace b ↔ a ∈ sourceWeightedBoundarySubspace b 0 := by
  simp only [mem_sourceBoundaryBaseSubspace, mem_sourceWeightedBoundarySubspace,
    sourceBoundaryZeroWeightEquiv_fst, sourceBoundaryZeroWeightEquiv_snd]

/-- Both boundary restrictions use the same Dirichlet-reflected input potential. -/
def sourceReflectedPotential (hp1 : 1 < p) (hp : p ≠ ⊤) (φ : CoeffPair p) : CoeffPair p :=
  sourceBoundaryZeroWeightEquiv (sourceIntervalExtensionToBoundary .dirichlet hp1 hp φ).val

theorem sourceReflectedPotential_mem (hp1 : 1 < p) (hp : p ≠ ⊤) (φ : CoeffPair p) :
    sourceReflectedPotential hp1 hp φ ∈ sourceBoundaryBaseSubspace .dirichlet :=
  (sourceBoundaryZeroWeightEquiv_mem .dirichlet _).mpr (sourceIntervalExtensionToBoundary .dirichlet hp1 hp φ).property

theorem sourceOperator_mem_sourceBoundaryBaseSubspace (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (hφ : φ ∈ sourceBoundaryBaseSubspace .dirichlet)
    (a : WeightedCoeffPair (Weight.sobolev 1) p) (ha : a ∈ sourceWeightedBoundarySubspace b 1) :
    sourceOperator hp φ a ∈ sourceBoundaryBaseSubspace b := by
  change CoeffPair.toMax p ((CoeffPair.toMax p).symm
    (operator hp (CoeffPair.toMax p φ) (WeightedCoeffPair.toMax (Weight.sobolev 1) p a))) ∈ space b
  rw [ContinuousLinearEquiv.apply_symm_apply]
  exact operator_mem b hp _ hφ _ ha

/-- The actual operator restricted to its original weighted boundary domain. -/
def sourceBoundaryOperator (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (hφ : φ ∈ sourceBoundaryBaseSubspace .dirichlet) :
    sourceWeightedBoundarySubspace (p := p) b 1 →L[ℂ] sourceBoundaryBaseSubspace (p := p) b :=
  ((sourceOperator hp φ).comp (sourceWeightedBoundarySubspace b 1).subtypeL).codRestrict _
    (fun a => sourceOperator_mem_sourceBoundaryBaseSubspace b hp φ hφ a.val a.property)

/-- Lemma 4.4: the completed Dirichlet reflection preserves both boundary spaces. -/
theorem sourceLemma4_4 (b : BoundaryCondition) (hp1 : 1 < p) (hp : p ≠ ⊤) (φ : CoeffPair p)
    (a : WeightedCoeffPair (Weight.sobolev 1) p) (ha : a ∈ sourceWeightedBoundarySubspace b 1) :
    sourceOperator hp (sourceReflectedPotential hp1 hp φ) a ∈ sourceBoundaryBaseSubspace b :=
  sourceOperator_mem_sourceBoundaryBaseSubspace b hp _ (sourceReflectedPotential_mem hp1 hp φ) a ha

/-- A sufficient original-norm bound for the restricted operator. -/
theorem norm_sourceBoundaryOperator_le (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (hφ : φ ∈ sourceBoundaryBaseSubspace .dirichlet)
    (a : sourceWeightedBoundarySubspace (p := p) b 1) :
    ‖sourceBoundaryOperator b hp φ hφ a‖ ≤ (2 : ℝ)^(1/p.toReal) *
      (Real.pi + WeightedCoeff.sobolevEmbeddingConstant p hp * ‖φ‖) * ‖a‖ := by
  change ‖(CoeffPair.toMax p).symm (operator hp (CoeffPair.toMax p φ)
    (WeightedCoeffPair.toMax (Weight.sobolev 1) p a.val))‖ ≤ _
  calc
    _ ≤ (2 : ℝ)^(1/p.toReal) * ‖operator hp (CoeffPair.toMax p φ)
        (WeightedCoeffPair.toMax (Weight.sobolev 1) p a.val)‖ := CoeffPair.norm_toMax_symm_le hp _
    _ ≤ (2 : ℝ)^(1/p.toReal) *
        ((Real.pi + WeightedCoeff.sobolevEmbeddingConstant p hp * ‖CoeffPair.toMax p φ‖) *
          ‖WeightedCoeffPair.toMax (Weight.sobolev 1) p a.val‖) :=
      mul_le_mul_of_nonneg_left (norm_operator_apply_le hp _ _) (by positivity)
    _ ≤ (2 : ℝ)^(1/p.toReal) *
        ((Real.pi + WeightedCoeff.sobolevEmbeddingConstant p hp * ‖φ‖) * ‖a.val‖) := by
      gcongr
      · exact add_nonneg Real.pi_pos.le
          (mul_nonneg (WeightedCoeff.sobolevEmbeddingConstant_nonneg p hp) (norm_nonneg _))
      · exact WeightedCoeff.sobolevEmbeddingConstant_nonneg p hp
      · exact CoeffPair.norm_toMax_le φ
      · exact WeightedCoeffPair.norm_toMax_le _ a.val
    _ = _ := by rw [mul_assoc]; rfl

theorem toMax_sourceReflectedPotential (hp1 : 1 < p) (hp : p ≠ ⊤) (φ : CoeffPair p) :
    CoeffPair.toMax p (sourceReflectedPotential hp1 hp φ) = (periodOneBoundaryPotential hp hp1 φ).val := by
  apply Prod.ext <;> apply lp.ext <;> funext n
  · change (sourceBoundaryZeroWeightEquiv _).fst n = _
    rw [sourceBoundaryZeroWeightEquiv_fst, sourceIntervalExtensionToBoundary_fst]
    rfl
  · change (sourceBoundaryZeroWeightEquiv _).snd n = _
    rw [sourceBoundaryZeroWeightEquiv_snd, sourceIntervalExtensionToBoundary_snd]
    rfl

/-- Continuous change from original base norms to auxiliary maximum norms. -/
def sourceBoundaryBaseEquiv (b : BoundaryCondition) :
    sourceBoundaryBaseSubspace (p := p) b ≃L[ℂ] space (p := p) b :=
  (CoeffPair.toMax p).ofSubmodule' (space b)

/-- Continuous change from original domain norms to auxiliary maximum norms. -/
def sourceBoundaryDomainEquiv (b : BoundaryCondition) :
    sourceWeightedBoundarySubspace (p := p) b 1 ≃L[ℂ] domain (p := p) b :=
  (WeightedCoeffPair.toMax (Weight.sobolev 1) p).ofSubmodule' (domain b)

/-- The inclusion of the one-derivative boundary domain into its base space. -/
def sourceBoundaryInclusion (b : BoundaryCondition) :
    sourceWeightedBoundarySubspace (p := p) b 1 →L[ℂ] sourceBoundaryBaseSubspace (p := p) b :=
  ((sourceBoundaryBaseEquiv b).symm.toContinuousLinearMap.comp (inclusion b)).comp
    (sourceBoundaryDomainEquiv b).toContinuousLinearMap

/-- The restricted spectral pencil in the original norms. -/
def sourceBoundaryPencil (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (hφ : φ ∈ sourceBoundaryBaseSubspace .dirichlet) (z : ℂ) :
    sourceWeightedBoundarySubspace (p := p) b 1 →L[ℂ] sourceBoundaryBaseSubspace (p := p) b :=
  ((sourceBoundaryBaseEquiv b).symm.toContinuousLinearMap.comp (pencil b hp (CoeffPair.toMax p φ) hφ z)).comp
    (sourceBoundaryDomainEquiv b).toContinuousLinearMap

/-- The transported pencil is exactly z times inclusion minus the actual restriction. -/
theorem sourceBoundaryPencil_eq (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (hφ : φ ∈ sourceBoundaryBaseSubspace .dirichlet) (z : ℂ) :
    sourceBoundaryPencil b hp φ hφ z = z • sourceBoundaryInclusion b - sourceBoundaryOperator b hp φ hφ := by
  ext a : 1
  apply Subtype.ext
  change (CoeffPair.toMax p).symm (spectralPencil hp (CoeffPair.toMax p φ) z
    (WeightedCoeffPair.toMax (Weight.sobolev 1) p a.val)) =
    z • (CoeffPair.toMax p).symm (domainInclusion (WeightedCoeffPair.toMax (Weight.sobolev 1) p a.val)) -
      (CoeffPair.toMax p).symm (operator hp (CoeffPair.toMax p φ) (WeightedCoeffPair.toMax (Weight.sobolev 1) p a.val))
  rw [spectralPencil_apply, map_sub, map_smul]

/-- The full resolvent set, defined by bijectivity of the actual restricted pencil. -/
def sourceBoundaryResolventSet (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (hφ : φ ∈ sourceBoundaryBaseSubspace .dirichlet) : Set ℂ :=
  {z | Function.Bijective (sourceBoundaryPencil b hp φ hφ z)}

/-- Changing equivalent norms does not change the restricted resolvent set. -/
theorem sourceBoundaryResolventSet_eq (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (hφ : φ ∈ sourceBoundaryBaseSubspace .dirichlet) :
    sourceBoundaryResolventSet b hp φ hφ = BoundaryCondition.resolventSet b hp (CoeffPair.toMax p φ) hφ := by
  ext z
  change Function.Bijective ((sourceBoundaryBaseEquiv b).symm ∘
    pencil b hp (CoeffPair.toMax p φ) hφ z ∘ sourceBoundaryDomainEquiv b) ↔ _
  rw [Function.Bijective.of_comp_iff' (sourceBoundaryBaseEquiv b).symm.bijective,
    Function.Bijective.of_comp_iff _ (sourceBoundaryDomainEquiv b).bijective]
  rfl

/-- The unnormalized printed boundary mode in the original operator domain. -/
def sourceBoundaryDomainMode (b : BoundaryCondition) (n : ℤ) : WeightedCoeffPair (Weight.sobolev 1) p :=
  (WeightedCoeffPair.toMax (Weight.sobolev 1) p).symm (mode b n)

theorem sourceBoundaryDomainMode_mem (b : BoundaryCondition) (n : ℤ) :
    sourceBoundaryDomainMode (p := p) b n ∈ sourceWeightedBoundarySubspace b 1 := by
  change WeightedCoeffPair.toMax (Weight.sobolev 1) p
    ((WeightedCoeffPair.toMax (Weight.sobolev 1) p).symm (mode b n)) ∈ domain b
  rw [ContinuousLinearEquiv.apply_symm_apply]
  exact mode_mem b n

/-- The free operator acts on the nth boundary mode by pi times n. -/
theorem sourceBoundaryDomainMode_free (b : BoundaryCondition) (hp : p ≠ ⊤) (n : ℤ) :
    sourceOperator hp 0 (sourceBoundaryDomainMode (p := p) b n) =
      ((Real.pi : ℂ) * n) • sourceDomainInclusion (sourceBoundaryDomainMode b n) := by
  change (CoeffPair.toMax p).symm (operator hp (CoeffPair.toMax p 0)
    ((WeightedCoeffPair.toMax (Weight.sobolev 1) p) ((WeightedCoeffPair.toMax (Weight.sobolev 1) p).symm (mode b n)))) =
    ((Real.pi : ℂ) * n) • (CoeffPair.toMax p).symm (domainInclusion
      ((WeightedCoeffPair.toMax (Weight.sobolev 1) p) ((WeightedCoeffPair.toMax (Weight.sobolev 1) p).symm (mode b n))))
  rw [ContinuousLinearEquiv.apply_symm_apply, map_zero, operator_zero, freeOperator_mode, map_smul]

/-- Assemble an amplitude sequence with the selected reflected boundary sign. -/
def sourceBoundaryBaseAssembly (b : BoundaryCondition) : Coeff p →L[ℂ] CoeffPair p :=
  (CoeffPair.toMax p).symm.toContinuousLinearMap.comp
    ((b.extensionSign • (Coeff.reflection (p := p)).toContinuousLinearEquiv.toContinuousLinearMap).prod
      (ContinuousLinearMap.id ℂ (Coeff p)))

/-- The potential action is a shifted amplitude, with the boundary sign. -/
theorem sourceBoundaryDomainMode_potential (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (hφ : φ ∈ sourceBoundaryBaseSubspace .dirichlet) (n : ℤ) :
    sourceOperator hp φ (sourceBoundaryDomainMode b n) - sourceOperator hp 0 (sourceBoundaryDomainMode b n) =
      b.extensionSign • sourceBoundaryBaseAssembly b (Coeff.shift (-n) φ.snd) := by
  apply (CoeffPair.toMax p).injective
  change CoeffPair.toMax p ((CoeffPair.toMax p).symm (operator hp (CoeffPair.toMax p φ)
    (WeightedCoeffPair.toMax (Weight.sobolev 1) p (sourceBoundaryDomainMode b n))) -
    (CoeffPair.toMax p).symm (operator hp (CoeffPair.toMax p 0)
      (WeightedCoeffPair.toMax (Weight.sobolev 1) p (sourceBoundaryDomainMode b n)))) = _
  simp only [map_sub, ContinuousLinearEquiv.apply_symm_apply, sourceBoundaryDomainMode,
    map_zero, operator_zero]
  change operator hp (CoeffPair.toMax p φ) (mode b n) - freeOperator (mode b n) =
    CoeffPair.toMax p (b.extensionSign • sourceBoundaryBaseAssembly b (Coeff.shift (-n) φ.snd))
  rw [operator, add_apply, add_sub_cancel_left]
  cases b
  · simp only [mode]
    rw [potentialOperator_dirichletMode hp (CoeffPair.toMax p φ) hφ]
    simp [sourceBoundaryBaseAssembly, extensionSign, ReflectionSplit.positiveEmbedding_apply]
  · simp only [mode]
    rw [potentialOperator_neumannMode hp (CoeffPair.toMax p φ) hφ]
    simp [sourceBoundaryBaseAssembly, extensionSign, ReflectionSplit.negativeEmbedding_apply]

/-- The unnormalized printed boundary mode in the original base space. -/
def sourceBoundaryBaseMode (b : BoundaryCondition) (n : ℤ) : CoeffPair p :=
  sourceBoundaryBaseAssembly b (lp.single p n 1)

/-- Boundary-mode expansions converge unconditionally in the original finite-p norm. -/
theorem hasSum_sourceBoundaryBaseModes (b : BoundaryCondition) (hp : p ≠ ⊤) (a : Coeff p) :
    HasSum (fun n : ℤ => a n • sourceBoundaryBaseMode b n) (sourceBoundaryBaseAssembly b a) := by
  let L : Coeff p →L[ℂ] CoeffPair p := sourceBoundaryBaseAssembly b
  have h := L.hasSum (lp.hasSum_single hp a)
  convert h using 1
  funext n
  unfold sourceBoundaryBaseMode
  change a n • L (lp.single p n 1) = L (lp.single p n (a n))
  rw [← map_smul, ← lp.single_smul]
  simp

/-- The printed potential-action series, with positive Dirichlet and negative Neumann sign. -/
theorem sourceBoundaryDomainMode_potential_series (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (hφ : φ ∈ sourceBoundaryBaseSubspace .dirichlet) (n : ℤ) :
    HasSum (fun k : ℤ => (b.extensionSign * φ.snd k) • sourceBoundaryBaseMode b (k - n))
      (sourceOperator hp φ (sourceBoundaryDomainMode b n) - sourceOperator hp 0 (sourceBoundaryDomainMode b n)) := by
  have h := (Equiv.addRight (-n)).hasSum_iff.mpr
    (hasSum_sourceBoundaryBaseModes b hp (Coeff.shift (-n) φ.snd))
  have he := h.const_smul b.extensionSign
  rw [sourceBoundaryDomainMode_potential b hp φ hφ n]
  convert he using 1
  funext k
  simp [Coeff.shift_apply, sub_eq_add_neg, smul_smul]

/-- The original boundary base space is closed. -/
theorem isClosed_sourceBoundaryBaseSubspace (b : BoundaryCondition) :
    IsClosed (sourceBoundaryBaseSubspace (p := p) b : Set (CoeffPair p)) :=
  (isClosed_space b).preimage (CoeffPair.toMax p).continuous

/-- At p=2 these are the modes already identified with the actual physical waves. -/
theorem sourceBoundaryBaseMode_two (b : BoundaryCondition) (n : ℤ) :
    sourceBoundaryBaseMode (p := 2) b n = sourceBoundaryMode b n := rfl

/-- The domain mode includes into the same physical base mode at p=2. -/
theorem sourceBoundaryDomainMode_inclusion_two (b : BoundaryCondition) (n : ℤ) :
    sourceDomainInclusion (sourceBoundaryDomainMode (p := 2) b n) = sourceBoundaryMode b n := by
  rw [sourceBoundaryMode_eq]
  change (CoeffPair.toMax 2).symm (domainInclusion
    ((WeightedCoeffPair.toMax (Weight.sobolev 1) 2)
      ((WeightedCoeffPair.toMax (Weight.sobolev 1) 2).symm (mode b n)))) = _
  rw [ContinuousLinearEquiv.apply_symm_apply]

end NLS.ZakharovShabat
