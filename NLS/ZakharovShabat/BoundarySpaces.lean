import NLS.SequenceSpaces.Reflection
import NLS.FunctionalAnalysis.ReflectionSplit
import NLS.ZakharovShabat.Operator

/-!
# Dirichlet and Neumann Fourier spaces

Chapter 1, §4, equations (1.8)–(1.9), printed p. 30. In the raw period-two
coefficient convention, Dirichlet amplitudes give `(a(-n), a(n))`, and Neumann
amplitudes give `(-b(-n), b(n))`. These are closed complementary spaces, both
in the base norm and at every Sobolev regularity. The projections below split
an existing period-two sequence; they are not the interval-extension maps of
Lemmas 4.1–4.3. At exponent two, `ClassicalIntervalExtension` and `ClassicalIntervalRestriction`
identify these domains with the original physical endpoint conditions.
-/

open scoped ENNReal
noncomputable section
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Dirichlet Fourier coefficients, with the source's signed mode convention. -/
def dirichletSubspace : Submodule ℂ (PairSpace p) :=
  ReflectionSplit.positive Coeff.reflection

/-- Neumann Fourier coefficients, with the source's signed mode convention. -/
def neumannSubspace : Submodule ℂ (PairSpace p) :=
  ReflectionSplit.negative Coeff.reflection

@[simp] theorem mem_dirichletSubspace (f : PairSpace p) :
    f ∈ dirichletSubspace ↔ ∀ n, f.1 n = f.2 (-n) := by
  rw [dirichletSubspace, ReflectionSplit.mem_positive]
  exact ⟨fun h n => congrArg (fun a : Coeff p => a n) h,
    fun h => lp.ext (funext h)⟩

@[simp] theorem mem_neumannSubspace (f : PairSpace p) :
    f ∈ neumannSubspace ↔ ∀ n, f.1 n = -f.2 (-n) := by
  rw [neumannSubspace, ReflectionSplit.mem_negative]
  exact ⟨fun h n => congrArg (fun a : Coeff p => a n) h,
    fun h => lp.ext (funext h)⟩

theorem isClosed_dirichletSubspace : IsClosed (dirichletSubspace (p := p) : Set (PairSpace p)) :=
  ReflectionSplit.isClosed_positive _

theorem isClosed_neumannSubspace : IsClosed (neumannSubspace (p := p) : Set (PairSpace p)) :=
  ReflectionSplit.isClosed_negative _

theorem isCompl_dirichlet_neumann :
    IsCompl (dirichletSubspace (p := p)) neumannSubspace := ReflectionSplit.isCompl _

/-- Dirichlet amplitudes are linearly isometric to the Dirichlet space. -/
def dirichletEquivalence : Coeff p ≃ₗᵢ[ℂ] ↥(dirichletSubspace (p := p)) :=
  ReflectionSplit.positiveEquivalence Coeff.reflection

/-- Neumann amplitudes are linearly isometric to the Neumann space. -/
def neumannEquivalence : Coeff p ≃ₗᵢ[ℂ] ↥(neumannSubspace (p := p)) :=
  ReflectionSplit.negativeEquivalence Coeff.reflection

/-- Dirichlet projection of a period-two pair. -/
def dirichletProjection : PairSpace p →L[ℂ] PairSpace p :=
  ReflectionSplit.positiveProjection Coeff.reflection

/-- Neumann projection of a period-two pair. -/
def neumannProjection : PairSpace p →L[ℂ] PairSpace p :=
  ReflectionSplit.negativeProjection Coeff.reflection

theorem dirichlet_neumann_decomposition (f : PairSpace p) :
    dirichletProjection f + neumannProjection f = f := ReflectionSplit.decomposition _ f

theorem norm_dirichletProjection_le (f : PairSpace p) : ‖dirichletProjection f‖ ≤ ‖f‖ :=
  ReflectionSplit.norm_positiveProjection_le _ f

theorem norm_neumannProjection_le (f : PairSpace p) : ‖neumannProjection f‖ ≤ ‖f‖ :=
  ReflectionSplit.norm_negativeProjection_le _ f

/-- The Dirichlet subspace at arbitrary real Sobolev regularity. -/
def weightedDirichletSubspace (s : ℝ) :
    Submodule ℂ (WeightedCoeff (Weight.sobolev s) p × WeightedCoeff (Weight.sobolev s) p) :=
  ReflectionSplit.positive (WeightedCoeff.reflection s)

/-- The Neumann subspace at arbitrary real Sobolev regularity. -/
def weightedNeumannSubspace (s : ℝ) :
    Submodule ℂ (WeightedCoeff (Weight.sobolev s) p × WeightedCoeff (Weight.sobolev s) p) :=
  ReflectionSplit.negative (WeightedCoeff.reflection s)

@[simp] theorem mem_weightedDirichletSubspace (s : ℝ)
    (f : WeightedCoeff (Weight.sobolev s) p × WeightedCoeff (Weight.sobolev s) p) :
    f ∈ weightedDirichletSubspace s ↔ ∀ n, f.1.val n = f.2.val (-n) := by
  rw [weightedDirichletSubspace, ReflectionSplit.mem_positive]
  constructor
  · intro h n
    simpa only [WeightedCoeff.neg_val, WeightedCoeff.reflection_apply] using
      congrArg (fun a : WeightedCoeff (Weight.sobolev s) p => a.val n) h
  · intro h
    apply Subtype.ext
    funext n
    simpa only [WeightedCoeff.neg_val, WeightedCoeff.reflection_apply] using h n

@[simp] theorem mem_weightedNeumannSubspace (s : ℝ)
    (f : WeightedCoeff (Weight.sobolev s) p × WeightedCoeff (Weight.sobolev s) p) :
    f ∈ weightedNeumannSubspace s ↔ ∀ n, f.1.val n = -f.2.val (-n) := by
  rw [weightedNeumannSubspace, ReflectionSplit.mem_negative]
  constructor
  · intro h n
    simpa only [WeightedCoeff.neg_val, WeightedCoeff.reflection_apply] using
      congrArg (fun a : WeightedCoeff (Weight.sobolev s) p => a.val n) h
  · intro h
    apply Subtype.ext
    funext n
    simpa only [WeightedCoeff.neg_val, WeightedCoeff.reflection_apply] using h n

theorem isClosed_weightedDirichletSubspace (s : ℝ) :
    IsClosed (weightedDirichletSubspace (p := p) s : Set (WeightedCoeff (Weight.sobolev s) p × WeightedCoeff (Weight.sobolev s) p)) :=
  ReflectionSplit.isClosed_positive _

theorem isClosed_weightedNeumannSubspace (s : ℝ) :
    IsClosed (weightedNeumannSubspace (p := p) s : Set (WeightedCoeff (Weight.sobolev s) p × WeightedCoeff (Weight.sobolev s) p)) :=
  ReflectionSplit.isClosed_negative _

theorem isCompl_weightedDirichlet_neumann (s : ℝ) :
    IsCompl (weightedDirichletSubspace (p := p) s) (weightedNeumannSubspace s) :=
  ReflectionSplit.isCompl _

/-- The same amplitude identification holds at every Sobolev regularity. -/
def weightedDirichletEquivalence (s : ℝ) : WeightedCoeff (Weight.sobolev s) p ≃ₗᵢ[ℂ]
    ↥(weightedDirichletSubspace (p := p) s) :=
  ReflectionSplit.positiveEquivalence (WeightedCoeff.reflection s)

def weightedNeumannEquivalence (s : ℝ) : WeightedCoeff (Weight.sobolev s) p ≃ₗᵢ[ℂ]
    ↥(weightedNeumannSubspace (p := p) s) :=
  ReflectionSplit.negativeEquivalence (WeightedCoeff.reflection s)

/-- The operator-domain condition agrees with the included base-space condition. -/
theorem domainInclusion_mem_dirichlet (f : Domain p) :
    domainInclusion f ∈ dirichletSubspace ↔ f ∈ weightedDirichletSubspace 1 := by
  simp

theorem domainInclusion_mem_neumann (f : Domain p) :
    domainInclusion f ∈ neumannSubspace ↔ f ∈ weightedNeumannSubspace 1 := by
  simp

@[simp] theorem scalarInclusion_reflection (f : ScalarDomain p) :
    scalarInclusion (WeightedCoeff.reflection 1 f) = Coeff.reflection (scalarInclusion f) := by
  ext n
  simp

/-- Dirichlet projection in the stronger one-derivative domain norm. -/
def domainDirichletProjection : Domain p →L[ℂ] Domain p :=
  ReflectionSplit.positiveProjection (WeightedCoeff.reflection 1)

/-- Neumann projection in the stronger one-derivative domain norm. -/
def domainNeumannProjection : Domain p →L[ℂ] Domain p :=
  ReflectionSplit.negativeProjection (WeightedCoeff.reflection 1)

theorem domainInclusion_dirichletProjection (f : Domain p) :
    domainInclusion (domainDirichletProjection f) = dirichletProjection (domainInclusion f) := by
  apply Prod.ext <;>
    simp [domainDirichletProjection, dirichletProjection, ReflectionSplit.positiveProjection,
      ReflectionSplit.positiveEmbedding, ReflectionSplit.positiveAmplitude,
      map_smul, map_add]

theorem domainInclusion_neumannProjection (f : Domain p) :
    domainInclusion (domainNeumannProjection f) = neumannProjection (domainInclusion f) := by
  apply Prod.ext <;>
    simp [domainNeumannProjection, neumannProjection, ReflectionSplit.negativeProjection,
      ReflectionSplit.negativeEmbedding, ReflectionSplit.negativeAmplitude,
      map_smul, map_sub]

/-- The source's free Dirichlet mode `Eₙ^dir = eₙ⁺ + eₙ⁻`. -/
def dirichletMode (n : ℤ) : Domain p := positiveMode n + negativeMode n

/-- The source's free Neumann mode `Eₙ^neu = eₙ⁺ - eₙ⁻`. -/
def neumannMode (n : ℤ) : Domain p := positiveMode n - negativeMode n

theorem dirichletMode_mem (n : ℤ) :
    dirichletMode (p := p) n ∈ weightedDirichletSubspace 1 := by
  rw [mem_weightedDirichletSubspace]
  intro k
  simp [dirichletMode, positiveMode, negativeMode,
    show k = -n ↔ -k = n by omega]

theorem neumannMode_mem (n : ℤ) :
    neumannMode (p := p) n ∈ weightedNeumannSubspace 1 := by
  rw [mem_weightedNeumannSubspace]
  intro k
  simp [neumannMode, positiveMode, negativeMode,
    show k = -n ↔ -k = n by omega]

theorem domainInclusion_dirichletMode_ne_zero (n : ℤ) :
    domainInclusion (dirichletMode (p := p) n) ≠ 0 := by
  intro h
  have hc := congrArg (fun a : PairSpace p => a.2 n) h
  simp [dirichletMode, positiveMode, negativeMode] at hc

theorem domainInclusion_neumannMode_ne_zero (n : ℤ) :
    domainInclusion (neumannMode (p := p) n) ≠ 0 := by
  intro h
  have hc := congrArg (fun a : PairSpace p => a.2 n) h
  simp [neumannMode, positiveMode, negativeMode] at hc

theorem freeOperator_dirichletMode (n : ℤ) :
    freeOperator (dirichletMode (p := p) n) =
      ((Real.pi : ℂ) * n) • domainInclusion (dirichletMode n) := by
  simp [dirichletMode, map_add, freeOperator_positiveMode, freeOperator_negativeMode, smul_add]

theorem freeOperator_neumannMode (n : ℤ) :
    freeOperator (neumannMode (p := p) n) =
      ((Real.pi : ℂ) * n) • domainInclusion (neumannMode n) := by
  simp [neumannMode, map_sub, freeOperator_positiveMode, freeOperator_negativeMode, smul_sub]

end NLS.ZakharovShabat
