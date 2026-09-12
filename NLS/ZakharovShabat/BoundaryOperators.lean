import NLS.ZakharovShabat.BoundarySpaces

/-!
# Operators on Dirichlet and Neumann Fourier spaces

This proves the coefficient-space invariance in Chapter 1, Lemma 4.4,
printed p. 32. The potential is assumed already in the reflected Dirichlet
space. Under that hypothesis the proof works for every `1 ≤ p < ∞`.
The source's interval-extension map for `1 < p < ∞`, which supplies such
potentials from period-one data, is a separate obligation.
-/

open scoped ENNReal
noncomputable section
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Potential multiplication is equivariant under simultaneous reflection. -/
theorem potentialMul_reflection (hp : p ≠ ⊤) (φ : Coeff p) (f : ScalarDomain p) :
    Coeff.reflection (potentialMul hp φ f) =
      potentialMul hp (Coeff.reflection φ) (WeightedCoeff.reflection 1 f) := by
  ext n
  simp only [Coeff.reflection_apply, potentialMul_apply, WeightedCoeff.reflection_apply]
  rw [← (Equiv.neg ℤ).tsum_eq (fun k : ℤ => φ (-n - k) * f.val k)]
  apply tsum_congr
  intro k
  simp only [Equiv.neg_apply]
  rw [show -n - -k = -(n - k) by omega]

/-- Multiplication by a single input mode shifts the potential coefficients. -/
theorem potentialMul_scalarMode (hp : p ≠ ⊤) (φ : Coeff p) (k : ℤ) (c : ℂ) :
    potentialMul hp φ (scalarMode k c) = c • Coeff.shift k φ := by
  ext n
  simp [potentialMul_apply, mul_comm]

/-- The positive sign in the potential action on `Eₙ^dir` in Lemma 4.4. -/
theorem potentialOperator_dirichletMode (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) (n : ℤ) :
    potentialOperator hp φ (dirichletMode n) =
      ReflectionSplit.positiveEmbedding Coeff.reflection (Coeff.shift (-n) φ.2) := by
  apply Prod.ext <;> ext k
  · simp only [potentialOperator_apply, dirichletMode, positiveMode, negativeMode,
      Prod.snd_add, add_zero, potentialMul_scalarMode, one_smul,
      ReflectionSplit.positiveEmbedding_apply, Coeff.reflection_apply, Coeff.shift_apply]
    rw [(mem_dirichletSubspace φ).mp hφ]
    rw [show -(k - n) = -k - -n by omega]
  · simp [dirichletMode, positiveMode, negativeMode, potentialMul_scalarMode]

/-- The negative sign in the potential action on `Eₙ^neu` in Lemma 4.4. -/
theorem potentialOperator_neumannMode (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) (n : ℤ) :
    potentialOperator hp φ (neumannMode n) =
      -ReflectionSplit.negativeEmbedding Coeff.reflection (Coeff.shift (-n) φ.2) := by
  apply Prod.ext <;> ext k
  · simp only [potentialOperator_apply, neumannMode, positiveMode, negativeMode,
      Prod.snd_sub, sub_zero, ReflectionSplit.negativeEmbedding_apply, Prod.fst_neg,
      neg_neg, potentialMul_scalarMode, one_smul, Coeff.reflection_apply, Coeff.shift_apply]
    rw [(mem_dirichletSubspace φ).mp hφ]
    rw [show -(k - n) = -k - -n by omega]
  · simp [neumannMode, positiveMode, negativeMode, potentialMul_scalarMode]

/-- Lemma 4.4 for an already Dirichlet-reflected potential: Dirichlet invariance. -/
theorem operator_mem_dirichlet (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) (f : Domain p) (hf : f ∈ weightedDirichletSubspace 1) :
    operator hp φ f ∈ dirichletSubspace := by
  have hφ' : φ.1 = Coeff.reflection φ.2 := (ReflectionSplit.mem_positive _ _).mp hφ
  have hf' : f.1 = WeightedCoeff.reflection 1 f.2 :=
    (ReflectionSplit.mem_positive _ _).mp hf
  have hv : potentialMul hp φ.1 f.2 = Coeff.reflection (potentialMul hp φ.2 f.1) := by
    rw [potentialMul_reflection, hφ', hf', WeightedCoeff.reflection_reflection]
  rw [mem_dirichletSubspace]
  intro n
  change (freeOperator f).1 n + potentialMul hp φ.1 f.2 n =
    (freeOperator f).2 (-n) + potentialMul hp φ.2 f.1 (-n)
  rw [hv, Coeff.reflection_apply]
  congr 1
  simp only [freeOperator_fst_apply, freeOperator_snd_apply, Int.cast_neg]
  rw [(mem_weightedDirichletSubspace 1 f).mp hf n]
  ring

/-- Lemma 4.4 for an already Dirichlet-reflected potential: Neumann invariance. -/
theorem operator_mem_neumann (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) (f : Domain p) (hf : f ∈ weightedNeumannSubspace 1) :
    operator hp φ f ∈ neumannSubspace := by
  have hφ' : φ.1 = Coeff.reflection φ.2 := (ReflectionSplit.mem_positive _ _).mp hφ
  have hf' : f.1 = -WeightedCoeff.reflection 1 f.2 :=
    (ReflectionSplit.mem_negative _ _).mp hf
  have hv : potentialMul hp φ.1 f.2 = -Coeff.reflection (potentialMul hp φ.2 f.1) := by
    rw [potentialMul_reflection, hφ', hf', map_neg, WeightedCoeff.reflection_reflection,
      map_neg, neg_neg]
  rw [mem_neumannSubspace]
  intro n
  change (freeOperator f).1 n + potentialMul hp φ.1 f.2 n =
    -((freeOperator f).2 (-n) + potentialMul hp φ.2 f.1 (-n))
  rw [hv]
  change (freeOperator f).1 n + -potentialMul hp φ.2 f.1 (-n) = _
  simp only [freeOperator_fst_apply, freeOperator_snd_apply, Int.cast_neg]
  rw [(mem_weightedNeumannSubspace 1 f).mp hf n]
  ring

/-- The boundary projections intertwine the domain-to-base operator. -/
theorem operator_dirichletProjection (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) (f : Domain p) :
    dirichletProjection (operator hp φ f) = operator hp φ (domainDirichletProjection f) := by
  have hd := operator_mem_dirichlet hp φ hφ (domainDirichletProjection f)
    (ReflectionSplit.positiveProjection_mem _ f)
  have hn := operator_mem_neumann hp φ hφ (domainNeumannProjection f)
    (ReflectionSplit.negativeProjection_mem _ f)
  have hs : domainDirichletProjection f + domainNeumannProjection f = f :=
    ReflectionSplit.decomposition _ f
  conv_lhs => rw [← hs, map_add, map_add]
  exact (congrArg₂ (· + ·) (ReflectionSplit.positiveProjection_eq_self _ hd)
    (ReflectionSplit.positiveProjection_eq_zero _ hn)).trans (add_zero _)

theorem operator_neumannProjection (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) (f : Domain p) :
    neumannProjection (operator hp φ f) = operator hp φ (domainNeumannProjection f) := by
  have hd := operator_mem_dirichlet hp φ hφ (domainDirichletProjection f)
    (ReflectionSplit.positiveProjection_mem _ f)
  have hn := operator_mem_neumann hp φ hφ (domainNeumannProjection f)
    (ReflectionSplit.negativeProjection_mem _ f)
  have hs : domainDirichletProjection f + domainNeumannProjection f = f :=
    ReflectionSplit.decomposition _ f
  conv_lhs => rw [← hs, map_add, map_add]
  exact (congrArg₂ (· + ·) (ReflectionSplit.negativeProjection_eq_zero _ hd)
    (ReflectionSplit.negativeProjection_eq_self _ hn)).trans (zero_add _)

/-- The bounded Dirichlet operator from its weighted domain into its base space. -/
def dirichletOperator (hp : p ≠ ⊤) (φ : PairSpace p) (hφ : φ ∈ dirichletSubspace) :
    ↥(weightedDirichletSubspace (p := p) 1) →L[ℂ] ↥(dirichletSubspace (p := p)) :=
  ((operator hp φ).comp (weightedDirichletSubspace 1).subtypeL).codRestrict
    dirichletSubspace (fun f => operator_mem_dirichlet hp φ hφ f.val f.property)

/-- The bounded Neumann operator, using the same Dirichlet-reflected potential. -/
def neumannOperator (hp : p ≠ ⊤) (φ : PairSpace p) (hφ : φ ∈ dirichletSubspace) :
    ↥(weightedNeumannSubspace (p := p) 1) →L[ℂ] ↥(neumannSubspace (p := p)) :=
  ((operator hp φ).comp (weightedNeumannSubspace 1).subtypeL).codRestrict
    neumannSubspace (fun f => operator_mem_neumann hp φ hφ f.val f.property)

@[simp] theorem dirichletOperator_apply (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) (f : weightedDirichletSubspace (p := p) 1) :
    (dirichletOperator hp φ hφ f).val = operator hp φ f.val := rfl

@[simp] theorem neumannOperator_apply (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) (f : weightedNeumannSubspace (p := p) 1) :
    (neumannOperator hp φ hφ f).val = operator hp φ f.val := rfl

theorem norm_dirichletOperator_apply_le (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) (f : weightedDirichletSubspace (p := p) 1) :
    ‖dirichletOperator hp φ hφ f‖ ≤
      (Real.pi + WeightedCoeff.sobolevEmbeddingConstant p hp * ‖φ‖) * ‖f‖ :=
  norm_operator_apply_le hp φ f.val

theorem norm_neumannOperator_apply_le (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) (f : weightedNeumannSubspace (p := p) 1) :
    ‖neumannOperator hp φ hφ f‖ ≤
      (Real.pi + WeightedCoeff.sobolevEmbeddingConstant p hp * ‖φ‖) * ‖f‖ :=
  norm_operator_apply_le hp φ f.val

end NLS.ZakharovShabat
