import NLS.ZakharovShabat.IntervalExtension
import NLS.ZakharovShabat.ClassicalIntervalIsomorphism
import NLS.ZakharovShabat.SourceLemma4_1
import NLS.SequenceSpaces.WeightedPairNormInfty
import Mathlib.Analysis.Normed.Module.Complemented

/-!
# Original-norm boundary subspaces and Lemma 4.2

The Dirichlet and Neumann spaces form closed topological complements at every
real Sobolev order. For finite exponents the ambient space has the original
component-sum norm. At infinity the separate signed coefficient space carries
the source's frequencywise sum supremum norm. Amplitude equivalences are
continuous linear equivalences, with exact norm factors, not isometries.
The classical equivalence uses the original physical interval H¹ norm and
has the actual signed extension and physical restriction as its two maps.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Select the established boundary subspace in the auxiliary maximum norm. -/
def weightedBoundarySubspace (b : BoundaryCondition) (s : ℝ) :
    Submodule ℂ (WeightedCoeff (Weight.sobolev s) p × WeightedCoeff (Weight.sobolev s) p) :=
  match b with | .dirichlet => weightedDirichletSubspace s | .neumann => weightedNeumannSubspace s

/-- Both auxiliary boundary subspaces are closed. -/
theorem isClosed_weightedBoundarySubspace (b : BoundaryCondition) (s : ℝ) :
    IsClosed (weightedBoundarySubspace (p := p) b s : Set (WeightedCoeff (Weight.sobolev s) p × WeightedCoeff (Weight.sobolev s) p)) := by
  cases b
  · exact isClosed_weightedDirichletSubspace s
  · exact isClosed_weightedNeumannSubspace s

/-- The boundary subspace in raw scalar Fourier coordinates; for finite p its ambient norm is the source norm. -/
def sourceWeightedBoundarySubspace (b : BoundaryCondition) (s : ℝ) :
    Submodule ℂ (WeightedCoeffPair (Weight.sobolev s) p) :=
  (weightedBoundarySubspace b s).comap (WeightedCoeffPair.toMax (Weight.sobolev s) p).toLinearMap

/-- The boundary subspace with the source infinity norm and signed first-component coordinates. -/
def sourceWeightedBoundarySubspaceInfty (b : BoundaryCondition) (s : ℝ) :
    Submodule ℂ (WeightedCoeffPairInfty (Weight.sobolev s)) :=
  (weightedBoundarySubspace b s).comap (WeightedCoeffPairInfty.toScalarMax s).toLinearMap

/-- Closedness in the original component-sum topology. -/
theorem isClosed_sourceWeightedBoundarySubspace (b : BoundaryCondition) (s : ℝ) :
    IsClosed (sourceWeightedBoundarySubspace (p := p) b s : Set (WeightedCoeffPair (Weight.sobolev s) p)) :=
  (isClosed_weightedBoundarySubspace b s).preimage (WeightedCoeffPair.toMax (Weight.sobolev s) p).continuous

/-- Closedness in the actual coupled supremum topology. -/
theorem isClosed_sourceWeightedBoundarySubspaceInfty (b : BoundaryCondition) (s : ℝ) :
    IsClosed (sourceWeightedBoundarySubspaceInfty b s : Set (WeightedCoeffPairInfty (Weight.sobolev s))) :=
  (isClosed_weightedBoundarySubspace b s).preimage (WeightedCoeffPairInfty.toScalarMax s).continuous

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
theorem isCompl_sourceWeightedBoundarySubspaces (s : ℝ) :
    IsCompl (sourceWeightedBoundarySubspace (p := p) .dirichlet s) (sourceWeightedBoundarySubspace .neumann s) :=
  isCompl_comap_equiv (WeightedCoeffPair.toMax (Weight.sobolev s) p) _ _ (isCompl_weightedDirichlet_neumann s)

/-- The same direct-sum decomposition with the source infinity norm. -/
theorem isCompl_sourceWeightedBoundarySubspacesInfty (s : ℝ) :
    IsCompl (sourceWeightedBoundarySubspaceInfty .dirichlet s) (sourceWeightedBoundarySubspaceInfty .neumann s) :=
  isCompl_comap_equiv (WeightedCoeffPairInfty.toScalarMax s) _ _ (isCompl_weightedDirichlet_neumann s)

/-- The original boundary decomposition is a topological direct sum. -/
theorem isTopCompl_sourceWeightedBoundarySubspaces (s : ℝ) :
    Submodule.IsTopCompl (sourceWeightedBoundarySubspace (p := p) .dirichlet s) (sourceWeightedBoundarySubspace .neumann s) :=
  Submodule.IsCompl.isTopCompl_of_isClosed (isCompl_sourceWeightedBoundarySubspaces s)
    (isClosed_sourceWeightedBoundarySubspace _ s) (isClosed_sourceWeightedBoundarySubspace _ s)

/-- The coupled-supremum boundary decomposition is a topological direct sum. -/
theorem isTopCompl_sourceWeightedBoundarySubspacesInfty (s : ℝ) :
    Submodule.IsTopCompl (sourceWeightedBoundarySubspaceInfty .dirichlet s) (sourceWeightedBoundarySubspaceInfty .neumann s) :=
  Submodule.IsCompl.isTopCompl_of_isClosed (isCompl_sourceWeightedBoundarySubspacesInfty s)
    (isClosed_sourceWeightedBoundarySubspaceInfty _ s) (isClosed_sourceWeightedBoundarySubspaceInfty _ s)

/-- Scalar amplitudes identify the auxiliary maximum-norm boundary space isometrically. -/
def weightedBoundaryAmplitudeEquiv (b : BoundaryCondition) (s : ℝ) :
    WeightedCoeff (Weight.sobolev s) p ≃ₗᵢ[ℂ] weightedBoundarySubspace (p := p) b s :=
  match b with | .dirichlet => weightedDirichletEquivalence s | .neumann => weightedNeumannEquivalence s

/-- Scalar amplitudes identify the original finite-exponent boundary space continuously. -/
def sourceWeightedBoundaryAmplitudeEquiv (b : BoundaryCondition) (s : ℝ) :
    WeightedCoeff (Weight.sobolev s) p ≃L[ℂ] sourceWeightedBoundarySubspace (p := p) b s :=
  (weightedBoundaryAmplitudeEquiv b s).toContinuousLinearEquiv.trans
    ((WeightedCoeffPair.toMax (Weight.sobolev s) p).ofSubmodule' (weightedBoundarySubspace b s)).symm

/-- Scalar amplitudes identify the actual source infinity boundary space continuously. -/
def sourceWeightedBoundaryAmplitudeEquivInfty (b : BoundaryCondition) (s : ℝ) :
    WeightedCoeff (Weight.sobolev s) ⊤ ≃L[ℂ] sourceWeightedBoundarySubspaceInfty b s :=
  (weightedBoundaryAmplitudeEquiv b s).toContinuousLinearEquiv.trans
    ((WeightedCoeffPairInfty.toScalarMax s).ofSubmodule' (weightedBoundarySubspace b s)).symm

/-- Raw scalar coordinates reverse the first component frequency. -/
theorem mem_sourceWeightedBoundarySubspace (b : BoundaryCondition) (s : ℝ)
    (u : WeightedCoeffPair (Weight.sobolev s) p) :
    u ∈ sourceWeightedBoundarySubspace b s ↔
      ∀ n : ℤ, u.fst.val n = b.extensionSign * u.snd.val (-n) := by
  cases b
  · change WeightedCoeffPair.toMax (Weight.sobolev s) p u ∈ weightedDirichletSubspace s ↔ _
    simp [mem_weightedDirichletSubspace, BoundaryCondition.extensionSign]
  · change WeightedCoeffPair.toMax (Weight.sobolev s) p u ∈ weightedNeumannSubspace s ↔ _
    simp [mem_weightedNeumannSubspace, BoundaryCondition.extensionSign]

/-- Signed source coordinates compare the two components at the same index. -/
theorem mem_sourceWeightedBoundarySubspaceInfty (b : BoundaryCondition) (s : ℝ)
    (u : WeightedCoeffPairInfty (Weight.sobolev s)) :
    u ∈ sourceWeightedBoundarySubspaceInfty b s ↔
      ∀ n : ℤ, u.1.val n = b.extensionSign * u.2.val n := by
  have he : u ∈ sourceWeightedBoundarySubspaceInfty b s ↔
      ∀ n : ℤ, u.1.val (-n) = b.extensionSign * u.2.val (-n) := by
    cases b
    · change WeightedCoeffPairInfty.toScalarMax s u ∈ weightedDirichletSubspace s ↔ _
      simp [mem_weightedDirichletSubspace, WeightedCoeffPairInfty.toScalarMax_apply,
        WeightedCoeff.reflection_apply, BoundaryCondition.extensionSign]
    · change WeightedCoeffPairInfty.toScalarMax s u ∈ weightedNeumannSubspace s ↔ _
      simp [mem_weightedNeumannSubspace, WeightedCoeffPairInfty.toScalarMax_apply,
        WeightedCoeff.reflection_apply, BoundaryCondition.extensionSign]
  rw [he]
  constructor
  · intro h n; simpa only [neg_neg] using h (-n)
  · intro h n; exact h (-n)

/-- The actual finite-exponent amplitude assembly, including sign and frequency reversal. -/
theorem sourceWeightedBoundaryAmplitudeEquiv_apply (b : BoundaryCondition) (s : ℝ)
    (a : WeightedCoeff (Weight.sobolev s) p) :
    (sourceWeightedBoundaryAmplitudeEquiv b s a).val =
      WithLp.toLp p (b.extensionSign • WeightedCoeff.reflection s a, a) := by
  cases b <;> simp only [BoundaryCondition.extensionSign, one_smul, neg_one_smul] <;> rfl

/-- The actual infinity assembly in signed coordinates. -/
theorem sourceWeightedBoundaryAmplitudeEquivInfty_apply (b : BoundaryCondition) (s : ℝ)
    (a : WeightedCoeff (Weight.sobolev s) ⊤) :
    (sourceWeightedBoundaryAmplitudeEquivInfty b s a).val =
      WeightedCoeffPairInfty.ofPair (Weight.sobolev s) (b.extensionSign • a) a := by
  cases b
  · change ((WeightedCoeff.reflection s).symm ((WeightedCoeff.reflection s) a),a) = (1 • a,a)
    rw [LinearIsometryEquiv.symm_apply_apply,one_smul]
  · change ((WeightedCoeff.reflection s).symm (-(WeightedCoeff.reflection s) a),a) = ((-1 : ℂ) • a,a)
    rw [map_neg,LinearIsometryEquiv.symm_apply_apply,neg_one_smul]

/-- Exact amplitude norm in the original finite-exponent component-sum norm. -/
theorem norm_sourceWeightedBoundaryAmplitudeEquiv (hp : p ≠ ⊤) (b : BoundaryCondition) (s : ℝ)
    (a : WeightedCoeff (Weight.sobolev s) p) :
    ‖sourceWeightedBoundaryAmplitudeEquiv b s a‖ = (2 : ℝ) ^ (1 / p.toReal) * ‖a‖ := by
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos
    (ne_of_gt (zero_lt_one.trans_le (show 1 ≤ p from Fact.out))) hp
  have hs : ‖b.extensionSign‖ = 1 := by cases b <;> simp [BoundaryCondition.extensionSign]
  change ‖(sourceWeightedBoundaryAmplitudeEquiv b s a).val‖ = _
  rw [sourceWeightedBoundaryAmplitudeEquiv_apply,WithLp.prod_norm_eq_add hp0]
  simp only [WithLp.toLp_fst,WithLp.toLp_snd,norm_smul,hs,LinearIsometryEquiv.norm_map,one_mul]
  rw [← two_mul,Real.mul_rpow (by norm_num) (by positivity),
    ← Real.rpow_mul (norm_nonneg _),mul_one_div_cancel hp0.ne',Real.rpow_one]

/-- Exact amplitude norm in the source frequencywise sum supremum norm. -/
theorem norm_sourceWeightedBoundaryAmplitudeEquivInfty (b : BoundaryCondition) (s : ℝ)
    (a : WeightedCoeff (Weight.sobolev s) ⊤) :
    ‖sourceWeightedBoundaryAmplitudeEquivInfty b s a‖ = 2 * ‖a‖ := by
  have hs : ‖b.extensionSign‖ = 1 := by cases b <;> simp [BoundaryCondition.extensionSign]
  change ‖(sourceWeightedBoundaryAmplitudeEquivInfty b s a).val‖ = _
  rw [sourceWeightedBoundaryAmplitudeEquivInfty_apply,
    ← WeightedCoeffPairInfty.norm_diagonal (Weight.sobolev s) a,
    WeightedCoeffPairInfty.norm_eq_ciSup,WeightedCoeffPairInfty.norm_eq_ciSup]
  congr 1
  funext n
  simp [WeightedCoeffPairInfty.ofPair,WeightedCoeff.smul_val,hs]

/-- Lemma 4.2 with the original physical H¹ domain and original component-sum Fourier norm. -/
def sourceClassicalBoundaryEquiv (b : BoundaryCondition) :
    BoundaryCondition.ClassicalIntervalDomain b ≃L[ℂ] sourceWeightedBoundarySubspace (p := 2) b 1 :=
  (BoundaryCondition.classicalIntervalEquiv b).trans
    ((WeightedCoeffPair.toMax (Weight.sobolev 1) 2).ofSubmodule' (weightedBoundarySubspace b 1)).symm

/-- The forward map is the actual reflected function’s original Fourier coefficients. -/
theorem sourceClassicalBoundaryEquiv_ofFunction (b : BoundaryCondition) (f : ℝ → ℂ × ℂ)
    (hf : BoundaryCondition.HasClassicalIntervalDomain b f) :
    (sourceClassicalBoundaryEquiv b (BoundaryCondition.classicalDomainOfFunction b f hf)).val =
      sourceClassicalIntervalExtension b f hf := by
  change (WeightedCoeffPair.toMax (Weight.sobolev 1) 2).symm
    ((BoundaryCondition.classicalIntervalEquiv b (BoundaryCondition.classicalDomainOfFunction b f hf)).val) = _
  rw [BoundaryCondition.classicalIntervalEquiv_ofFunction]
  rfl

/-- The inverse is physical restriction at every point of the closed unit interval. -/
theorem sourceClassicalBoundaryEquiv_symm_apply (b : BoundaryCondition)
    (a : sourceWeightedBoundarySubspace (p := 2) b 1) (x : Set.Icc (0 : ℝ) 1) :
    ((sourceClassicalBoundaryEquiv b).symm a).val x =
      BoundaryCondition.classicalIntervalRestriction (WeightedCoeffPair.toMax (Weight.sobolev 1) 2 a.val) x.val :=
  BoundaryCondition.classicalIntervalEquiv_symm_apply b _ x

end NLS.ZakharovShabat
