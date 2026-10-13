import NLS.ZakharovShabat.SourceBoundarySpaces
import NLS.ZakharovShabat.ClassicalAuxiliarySpace
import NLS.ZakharovShabat.SourceLemma5_1
/-!
# Original weighted auxiliary boundary spaces

At every real Sobolev order, the auxiliary D* and N* spaces are closed
complements. Finite exponents use the original component-sum norm; infinity
uses the separate signed, frequencywise-sum supremum norm. The amplitude
maps have factors 2^(1/p) and 2 respectively. The physical H¹ equivalence
uses the actual auxiliary extension and endpoint-inclusive restriction.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The boundary subspace in raw scalar Fourier coordinates; for finite p its ambient norm is the source norm. -/
def sourceWeightedAuxiliarySubspace (b : BoundaryCondition) (s : ℝ) :
    Submodule ℂ (WeightedCoeffPair (Weight.sobolev s) p) :=
  (BoundaryCondition.auxiliaryWeightedSpace b s).comap (WeightedCoeffPair.toMax (Weight.sobolev s) p).toLinearMap

/-- The boundary subspace with the source infinity norm and signed first-component coordinates. -/
def sourceWeightedAuxiliarySubspaceInfty (b : BoundaryCondition) (s : ℝ) :
    Submodule ℂ (WeightedCoeffPairInfty (Weight.sobolev s)) :=
  (BoundaryCondition.auxiliaryWeightedSpace b s).comap (WeightedCoeffPairInfty.toScalarMax s).toLinearMap

/-- Closedness in the original component-sum topology. -/
theorem isClosed_sourceWeightedAuxiliarySubspace (b : BoundaryCondition) (s : ℝ) :
    IsClosed (sourceWeightedAuxiliarySubspace (p := p) b s : Set (WeightedCoeffPair (Weight.sobolev s) p)) :=
  (BoundaryCondition.isClosed_auxiliaryWeightedSpace b s).preimage (WeightedCoeffPair.toMax (Weight.sobolev s) p).continuous

/-- Closedness in the actual coupled supremum topology. -/
theorem isClosed_sourceWeightedAuxiliarySubspaceInfty (b : BoundaryCondition) (s : ℝ) :
    IsClosed (sourceWeightedAuxiliarySubspaceInfty b s : Set (WeightedCoeffPairInfty (Weight.sobolev s))) :=
  (BoundaryCondition.isClosed_auxiliaryWeightedSpace b s).preimage (WeightedCoeffPairInfty.toScalarMax s).continuous

private theorem isCompl_comap_equiv {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (e : E ≃L[ℂ] F) (A B : Submodule ℂ F)
    (h : IsCompl A B) : IsCompl (A.comap e.toLinearMap) (B.comap e.toLinearMap) := by
  constructor
  · apply Submodule.disjoint_def.mpr
    intro x hx hy
    apply e.injective
    rw [map_zero]
    exact (Submodule.disjoint_def.mp h.disjoint) _ hx hy
  · rw [codisjoint_iff_le_sup]
    intro x _
    have hx : e x ∈ A ⊔ B := by rw [h.sup_eq_top]; trivial
    obtain ⟨a,ha,b,hb,he⟩ := Submodule.mem_sup.mp hx
    refine Submodule.mem_sup.mpr ⟨e.symm a,?_,e.symm b,?_,?_⟩
    · change e (e.symm a) ∈ A
      simpa using ha
    · change e (e.symm b) ∈ B
      simpa using hb
    · rw [← map_add,he,e.symm_apply_apply]

/-- The finite-exponent source spaces have zero intersection and span the entire ambient space. -/
theorem isCompl_sourceWeightedAuxiliarySubspaces (s : ℝ) :
    IsCompl (sourceWeightedAuxiliarySubspace (p := p) .dirichlet s) (sourceWeightedAuxiliarySubspace .neumann s) :=
  isCompl_comap_equiv (WeightedCoeffPair.toMax (Weight.sobolev s) p) _ _ (BoundaryCondition.isCompl_auxiliaryWeightedSpaces s)

/-- The same direct-sum decomposition with the source infinity norm. -/
theorem isCompl_sourceWeightedAuxiliarySubspacesInfty (s : ℝ) :
    IsCompl (sourceWeightedAuxiliarySubspaceInfty .dirichlet s) (sourceWeightedAuxiliarySubspaceInfty .neumann s) :=
  isCompl_comap_equiv (WeightedCoeffPairInfty.toScalarMax s) _ _ (BoundaryCondition.isCompl_auxiliaryWeightedSpaces s)

/-- The original boundary decomposition is a topological direct sum. -/
theorem isTopCompl_sourceWeightedAuxiliarySubspaces (s : ℝ) :
    Submodule.IsTopCompl (sourceWeightedAuxiliarySubspace (p := p) .dirichlet s) (sourceWeightedAuxiliarySubspace .neumann s) :=
  Submodule.IsCompl.isTopCompl_of_isClosed (isCompl_sourceWeightedAuxiliarySubspaces s)
    (isClosed_sourceWeightedAuxiliarySubspace _ s) (isClosed_sourceWeightedAuxiliarySubspace _ s)

/-- The coupled-supremum boundary decomposition is a topological direct sum. -/
theorem isTopCompl_sourceWeightedAuxiliarySubspacesInfty (s : ℝ) :
    Submodule.IsTopCompl (sourceWeightedAuxiliarySubspaceInfty .dirichlet s) (sourceWeightedAuxiliarySubspaceInfty .neumann s) :=
  Submodule.IsCompl.isTopCompl_of_isClosed (isCompl_sourceWeightedAuxiliarySubspacesInfty s)
    (isClosed_sourceWeightedAuxiliarySubspaceInfty _ s) (isClosed_sourceWeightedAuxiliarySubspaceInfty _ s)

/-- Scalar amplitudes assemble the actual auxiliary weighted maximum-norm space. -/
def weightedAuxiliaryAmplitudeEquiv (b : BoundaryCondition) (s : ℝ) :
    WeightedCoeff (Weight.sobolev s) p ≃ₗᵢ[ℂ] BoundaryCondition.auxiliaryWeightedSpace (p := p) b s :=
  (weightedBoundaryAmplitudeEquiv b s).trans
    (LinearIsometryEquiv.submoduleMap (weightedBoundarySubspace b s)
      (auxiliaryPhase (WeightedCoeff (Weight.sobolev s) p)))

/-- Scalar amplitudes identify the original finite-exponent boundary space continuously. -/
def sourceWeightedAuxiliaryAmplitudeEquiv (b : BoundaryCondition) (s : ℝ) :
    WeightedCoeff (Weight.sobolev s) p ≃L[ℂ] sourceWeightedAuxiliarySubspace (p := p) b s :=
  (weightedAuxiliaryAmplitudeEquiv b s).toContinuousLinearEquiv.trans
    ((WeightedCoeffPair.toMax (Weight.sobolev s) p).ofSubmodule' (BoundaryCondition.auxiliaryWeightedSpace b s)).symm

/-- Scalar amplitudes identify the actual source infinity boundary space continuously. -/
def sourceWeightedAuxiliaryAmplitudeEquivInfty (b : BoundaryCondition) (s : ℝ) :
    WeightedCoeff (Weight.sobolev s) ⊤ ≃L[ℂ] sourceWeightedAuxiliarySubspaceInfty b s :=
  (weightedAuxiliaryAmplitudeEquiv b s).toContinuousLinearEquiv.trans
    ((WeightedCoeffPairInfty.toScalarMax s).ofSubmodule' (BoundaryCondition.auxiliaryWeightedSpace b s)).symm

/-- Raw scalar auxiliary coordinates reverse the first component frequency. -/
theorem mem_sourceWeightedAuxiliarySubspace (b : BoundaryCondition) (s : ℝ)
    (u : WeightedCoeffPair (Weight.sobolev s) p) :
    u ∈ sourceWeightedAuxiliarySubspace b s ↔
      ∀ n : ℤ, u.fst.val n = -Complex.I * b.extensionSign * u.snd.val (-n) := by
  change WeightedCoeffPair.toMax (Weight.sobolev s) p u ∈ b.auxiliaryWeightedSpace s ↔ _
  rw [BoundaryCondition.mem_auxiliaryWeightedSpace]
  cases b <;> simp [BoundaryCondition.extensionSign]

/-- Signed infinity coordinates compare the auxiliary components at the same index. -/
theorem mem_sourceWeightedAuxiliarySubspaceInfty (b : BoundaryCondition) (s : ℝ)
    (u : WeightedCoeffPairInfty (Weight.sobolev s)) :
    u ∈ sourceWeightedAuxiliarySubspaceInfty b s ↔
      ∀ n : ℤ, u.1.val n = -Complex.I * b.extensionSign * u.2.val n := by
  change WeightedCoeffPairInfty.toScalarMax s u ∈ b.auxiliaryWeightedSpace s ↔ _
  rw [BoundaryCondition.mem_auxiliaryWeightedSpace]
  cases b <;> simp only [WeightedCoeffPairInfty.toScalarMax_apply,
    WeightedCoeff.reflection_apply, BoundaryCondition.extensionSign, mul_one, neg_mul, mul_neg,
    neg_neg] <;> constructor <;> intro h n <;> simpa only [neg_neg] using h (-n)

/-- The actual finite-exponent amplitude assembly, including sign and frequency reversal. -/
theorem sourceWeightedAuxiliaryAmplitudeEquiv_apply (b : BoundaryCondition) (s : ℝ)
    (a : WeightedCoeff (Weight.sobolev s) p) :
    (sourceWeightedAuxiliaryAmplitudeEquiv b s a).val =
      WithLp.toLp p (b.extensionSign • WeightedCoeff.reflection s a, Complex.I • a) := by
  cases b <;> simp only [BoundaryCondition.extensionSign, one_smul, neg_one_smul] <;> rfl

/-- The actual infinity assembly in signed coordinates. -/
theorem sourceWeightedAuxiliaryAmplitudeEquivInfty_apply (b : BoundaryCondition) (s : ℝ)
    (a : WeightedCoeff (Weight.sobolev s) ⊤) :
    (sourceWeightedAuxiliaryAmplitudeEquivInfty b s a).val =
      WeightedCoeffPairInfty.ofPair (Weight.sobolev s) (b.extensionSign • a) (Complex.I • a) := by
  cases b
  · change ((WeightedCoeff.reflection s).symm ((WeightedCoeff.reflection s) a),Complex.I • a) = (1 • a,Complex.I • a)
    rw [LinearIsometryEquiv.symm_apply_apply,one_smul]
  · change ((WeightedCoeff.reflection s).symm (-(WeightedCoeff.reflection s) a),Complex.I • a) = ((-1 : ℂ) • a,Complex.I • a)
    rw [map_neg,LinearIsometryEquiv.symm_apply_apply,neg_one_smul]

/-- Exact amplitude norm in the original finite-exponent component-sum norm. -/
theorem norm_sourceWeightedAuxiliaryAmplitudeEquiv (hp : p ≠ ⊤) (b : BoundaryCondition) (s : ℝ)
    (a : WeightedCoeff (Weight.sobolev s) p) :
    ‖sourceWeightedAuxiliaryAmplitudeEquiv b s a‖ = (2 : ℝ) ^ (1 / p.toReal) * ‖a‖ := by
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos
    (ne_of_gt (zero_lt_one.trans_le (show 1 ≤ p from Fact.out))) hp
  have hs : ‖b.extensionSign‖ = 1 := by cases b <;> simp [BoundaryCondition.extensionSign]
  change ‖(sourceWeightedAuxiliaryAmplitudeEquiv b s a).val‖ = _
  rw [sourceWeightedAuxiliaryAmplitudeEquiv_apply,WithLp.prod_norm_eq_add hp0]
  simp only [WithLp.toLp_fst,WithLp.toLp_snd,norm_smul,hs,Complex.norm_I,LinearIsometryEquiv.norm_map,one_mul]
  rw [← two_mul,Real.mul_rpow (by norm_num) (by positivity),
    ← Real.rpow_mul (norm_nonneg _),mul_one_div_cancel hp0.ne',Real.rpow_one]

/-- Exact amplitude norm in the source frequencywise sum supremum norm. -/
theorem norm_sourceWeightedAuxiliaryAmplitudeEquivInfty (b : BoundaryCondition) (s : ℝ)
    (a : WeightedCoeff (Weight.sobolev s) ⊤) :
    ‖sourceWeightedAuxiliaryAmplitudeEquivInfty b s a‖ = 2 * ‖a‖ := by
  have hs : ‖b.extensionSign‖ = 1 := by cases b <;> simp [BoundaryCondition.extensionSign]
  change ‖(sourceWeightedAuxiliaryAmplitudeEquivInfty b s a).val‖ = _
  rw [sourceWeightedAuxiliaryAmplitudeEquivInfty_apply,
    ← WeightedCoeffPairInfty.norm_diagonal (Weight.sobolev s) a,
    WeightedCoeffPairInfty.norm_eq_ciSup,WeightedCoeffPairInfty.norm_eq_ciSup]
  congr 1
  funext n
  simp [WeightedCoeffPairInfty.ofPair,WeightedCoeff.smul_val,hs]

/-- The page-34 auxiliary isomorphism in the physical H¹ and original Fourier norms. -/
def sourceClassicalAuxiliaryBoundaryEquiv (b : BoundaryCondition) :
    BoundaryCondition.ClassicalAuxiliaryDomain b ≃L[ℂ] sourceWeightedAuxiliarySubspace (p := 2) b 1 :=
  (BoundaryCondition.classicalAuxiliaryIntervalEquiv b).trans
    ((WeightedCoeffPair.toMax (Weight.sobolev 1) 2).ofSubmodule' (BoundaryCondition.auxiliaryWeightedSpace b 1)).symm

/-- The forward map is the actual reflected function’s original Fourier coefficients. -/
theorem sourceClassicalAuxiliaryBoundaryEquiv_ofFunction (b : BoundaryCondition) (f : ℝ → ℂ × ℂ)
    (hf : BoundaryCondition.HasClassicalAuxiliaryDomain b f) :
    (sourceClassicalAuxiliaryBoundaryEquiv b (BoundaryCondition.classicalAuxiliaryDomainOfFunction b f hf)).val =
      sourceClassicalAuxiliaryExtension b f hf := by
  change (WeightedCoeffPair.toMax (Weight.sobolev 1) 2).symm
    ((BoundaryCondition.classicalAuxiliaryIntervalEquiv b (BoundaryCondition.classicalAuxiliaryDomainOfFunction b f hf)).val) = _
  rw [BoundaryCondition.classicalAuxiliaryIntervalEquiv_ofFunction]
  rfl

/-- The inverse is physical restriction at every point of the closed unit interval. -/
theorem sourceClassicalAuxiliaryBoundaryEquiv_symm_apply (b : BoundaryCondition)
    (a : sourceWeightedAuxiliarySubspace (p := 2) b 1) (x : Set.Icc (0 : ℝ) 1) :
    ((sourceClassicalAuxiliaryBoundaryEquiv b).symm a).val x =
      BoundaryCondition.classicalIntervalRestriction (WeightedCoeffPair.toMax (Weight.sobolev 1) 2 a.val) x.val :=
  BoundaryCondition.classicalAuxiliaryIntervalEquiv_symm_apply b _ x

end NLS.ZakharovShabat
