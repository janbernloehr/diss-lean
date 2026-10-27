import NLS.FunctionalAnalysis.LinearPMapRootSpace
import NLS.ZakharovShabat.SourceParityUnboundedOperator
import NLS.ZakharovShabat.ParityRootMultiplicity

/-! # Complete original root chains in each separate Fourier parity -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open NLS.FunctionalAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The original sector root chains use the full weighted parity domain at each step. -/
def sourceParityRootSpace (hp : p ≠ ⊤) (φ : CoeffPair p)
    (hφ : φ ∈ sourceParitySubspace 0) (r : ℤ) (z : ℂ) : ℕ → Submodule ℂ (sourceParitySubspace (p := p) r) :=
  pencilRootSpace (sourceParityDomainInclusion r).toLinearMap (sourceParitySpectralPencil hp φ hφ r z).toLinearMap

private theorem inclusion_toMax (r : ℤ) (a : sourceDomainParitySubspace (p := p) r) :
    CoeffPair.toMax p (sourceParityDomainInclusion r a : CoeffPair p) =
      domainInclusion (WeightedCoeffPair.toMax (Weight.sobolev 1) p a.val) := by
  change (CoeffPair.toMax p) ((CoeffPair.toMax p).symm _) = _
  rw [ContinuousLinearEquiv.apply_symm_apply]
  rfl

private theorem pencil_toMax (hp : p ≠ ⊤) (φ : CoeffPair p)
    (hφ : φ ∈ sourceParitySubspace 0) (r : ℤ) (z : ℂ) (a : sourceDomainParitySubspace (p := p) r) :
    CoeffPair.toMax p (sourceParitySpectralPencil hp φ hφ r z a : CoeffPair p) =
      spectralPencil hp (CoeffPair.toMax p φ) z (WeightedCoeffPair.toMax (Weight.sobolev 1) p a.val) := by
  rw [sourceParitySpectralPencil_coe]
  change (CoeffPair.toMax p) ((CoeffPair.toMax p).symm _) = _
  rw [ContinuousLinearEquiv.apply_symm_apply]
  rfl

/-- The separate sector recursion recovers exactly the original root vectors of that parity. -/
theorem mem_sourceParityRootSpace_iff (hp : p ≠ ⊤) (φ : CoeffPair p)
    (hφ : φ ∈ sourceParitySubspace 0) (r : ℤ) (z : ℂ) (n : ℕ)
    (x : sourceParitySubspace (p := p) r) :
    x ∈ sourceParityRootSpace hp φ hφ r z n ↔
      CoeffPair.toMax p x.val ∈ periodicRootSpace hp (CoeffPair.toMax p φ) z n := by
  induction n generalizing x with
  | zero =>
    change x = 0 ↔ CoeffPair.toMax p x.val = 0
    constructor
    · rintro rfl
      exact map_zero _
    · intro hx
      apply Subtype.ext
      exact (CoeffPair.toMax p).injective (hx.trans (map_zero _).symm)
  | succ n ih =>
    change x ∈ pencilRootSpace _ _ (n+1) ↔ _
    rw [mem_pencilRootSpace_succ,mem_periodicRootSpace_succ]
    constructor
    · rintro ⟨a,ha,hprev⟩
      change sourceParityDomainInclusion r a = x at ha
      refine ⟨WeightedCoeffPair.toMax (Weight.sobolev 1) p a.val,?_,?_⟩
      · rw [← inclusion_toMax,ha]
      · rw [← pencil_toMax hp φ hφ r z]
        exact (ih _).mp hprev
    · rintro ⟨f,hf,hprev⟩
      let a : sourceDomainParitySubspace (p := p) r :=
        ⟨(WeightedCoeffPair.toMax (Weight.sobolev 1) p).symm f,by
          change (WeightedCoeffPair.toMax (Weight.sobolev 1) p)
            ((WeightedCoeffPair.toMax (Weight.sobolev 1) p).symm f) ∈ domainParitySubspace r
          rw [ContinuousLinearEquiv.apply_symm_apply,mem_domainParitySubspace,hf]
          exact x.property⟩
      refine ⟨a,?_,?_⟩
      · change sourceParityDomainInclusion r a = x
        apply Subtype.ext
        apply (CoeffPair.toMax p).injective
        rw [inclusion_toMax]
        change domainInclusion ((WeightedCoeffPair.toMax (Weight.sobolev 1) p)
          ((WeightedCoeffPair.toMax (Weight.sobolev 1) p).symm f)) = _
        rwa [ContinuousLinearEquiv.apply_symm_apply]
      · change sourceParitySpectralPencil hp φ hφ r z a ∈ sourceParityRootSpace hp φ hφ r z n
        apply (ih _).mpr
        rw [pencil_toMax]
        change spectralPencil hp (CoeffPair.toMax p φ) z
          ((WeightedCoeffPair.toMax (Weight.sobolev 1) p)
            ((WeightedCoeffPair.toMax (Weight.sobolev 1) p).symm f)) ∈ _
        rwa [ContinuousLinearEquiv.apply_symm_apply]

/-- The full sector root space is the union of its actual finite chains. -/
def sourceParityRootSpaceTop (hp : p ≠ ⊤) (φ : CoeffPair p)
    (hφ : φ ∈ sourceParitySubspace 0) (r : ℤ) (z : ℂ) : Submodule ℂ (sourceParitySubspace (p := p) r) :=
  pencilRootSpaceTop (sourceParityDomainInclusion r).toLinearMap (sourceParitySpectralPencil hp φ hφ r z).toLinearMap

theorem mem_sourceParityRootSpaceTop_iff (hp : p ≠ ⊤) (φ : CoeffPair p)
    (hφ : φ ∈ sourceParitySubspace 0) (r : ℤ) (z : ℂ) (x : sourceParitySubspace (p := p) r) :
    x ∈ sourceParityRootSpaceTop hp φ hφ r z ↔
      CoeffPair.toMax p x.val ∈ periodicRootSpaceTop hp (CoeffPair.toMax p φ) z := by
  rw [periodicRootSpaceTop]
  change x ∈ pencilRootSpaceTop _ _ ↔ _
  rw [mem_pencilRootSpaceTop,← periodicRootSpaceTop,mem_periodicRootSpaceTop]
  exact exists_congr fun n => mem_sourceParityRootSpace_iff hp φ hφ r z n x

/-- Exact full-root equivalence preserves the original source parity and every generalized vector. -/
def sourceParityRootSpaceTopEquiv (hp : p ≠ ⊤) (φ : CoeffPair p)
    (hφ : φ ∈ sourceParitySubspace 0) (r : ℤ) (z : ℂ) :
    sourceParityRootSpaceTop hp φ hφ r z ≃ₗ[ℂ]
      ↥(periodicRootSpaceTop hp (CoeffPair.toMax p φ) z ⊓ pairParitySubspace r) where
  toFun x := ⟨CoeffPair.toMax p x.val.val,
    ⟨(mem_sourceParityRootSpaceTop_iff hp φ hφ r z x.val).mp x.property,x.val.property⟩⟩
  invFun y := ⟨⟨(CoeffPair.toMax p).symm y.val,by
    change CoeffPair.toMax p ((CoeffPair.toMax p).symm y.val) ∈ pairParitySubspace r
    rw [ContinuousLinearEquiv.apply_symm_apply]
    exact y.property.2⟩,by
      apply (mem_sourceParityRootSpaceTop_iff hp φ hφ r z _).mpr
      change CoeffPair.toMax p ((CoeffPair.toMax p).symm y.val) ∈ _
      rw [ContinuousLinearEquiv.apply_symm_apply]
      exact y.property.1⟩
  left_inv x := Subtype.ext (Subtype.ext ((CoeffPair.toMax p).symm_apply_apply x.val.val))
  right_inv y := Subtype.ext ((CoeffPair.toMax p).apply_symm_apply y.val)
  map_add' x y := Subtype.ext (map_add (CoeffPair.toMax p) x.val.val y.val.val)
  map_smul' c x := Subtype.ext (map_smul (CoeffPair.toMax p) c x.val.val)

theorem finiteDimensional_sourceParityRootSpaceTop (hp : p ≠ ⊤) (φ : CoeffPair p)
    (hφ : φ ∈ sourceParitySubspace 0) (r : ℤ) (z : ℂ) :
    FiniteDimensional ℂ (sourceParityRootSpaceTop hp φ hφ r z) := by
  let : FiniteDimensional ℂ ↥(periodicRootSpaceTop hp (CoeffPair.toMax p φ) z ⊓ pairParitySubspace r) :=
    finiteDimensional_parityRootSpace hp (CoeffPair.toMax p φ) r z
  exact FiniteDimensional.of_injective (sourceParityRootSpaceTopEquiv hp φ hφ r z).toLinearMap
    (sourceParityRootSpaceTopEquiv hp φ hφ r z).injective

theorem exists_sourceParityRootSpace_eq_top (hp : p ≠ ⊤) (φ : CoeffPair p)
    (hφ : φ ∈ sourceParitySubspace 0) (r : ℤ) (z : ℂ) :
    ∃ n : ℕ, sourceParityRootSpace hp φ hφ r z n = sourceParityRootSpaceTop hp φ hφ r z := by
  obtain ⟨n,hn⟩ := exists_periodicRootSpace_eq_top hp (CoeffPair.toMax p φ) z
  refine ⟨n,?_⟩
  ext x
  rw [mem_sourceParityRootSpace_iff,mem_sourceParityRootSpaceTop_iff,hn]

end NLS.ZakharovShabat
