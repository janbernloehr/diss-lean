import NLS.ZakharovShabat.SourceResolvent
import NLS.ZakharovShabat.PeriodOneEmbedding

/-! # Parity subspaces in the original finite-exponent source norms

The even and odd coefficient masks are closed topological complements.
Their bounded projections are contractive at finite exponents. Period
one is identified isometrically with the even subspace.
-/
noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Coefficients supported in the residue class `r` modulo two. -/
def sourceParitySubspace (r : ℤ) : Submodule ℂ (CoeffPair p) :=
  (pairParitySubspace r).comap (CoeffPair.toMax p).toLinearMap

/-- The same support condition on the original one-derivative domain. -/
def sourceDomainParitySubspace (r : ℤ) : Submodule ℂ (WeightedCoeffPair (Weight.sobolev 1) p) :=
  (domainParitySubspace r).comap (WeightedCoeffPair.toMax (Weight.sobolev 1) p).toLinearMap

/-- The bounded parity mask in the original pair norm. -/
def sourceParityProjection (r : ℤ) : CoeffPair p →L[ℂ] CoeffPair p :=
  (CoeffPair.toMax p).symm.conjContinuousAlgEquiv (pairParityProjection r)

theorem isClosed_sourceParitySubspace (r : ℤ) : IsClosed (sourceParitySubspace (p := p) r : Set (CoeffPair p)) :=
  (isClosed_pairParitySubspace r).preimage (CoeffPair.toMax p).continuous

theorem mem_sourceParitySubspace (r : ℤ) (a : CoeffPair p) : a ∈ sourceParitySubspace r ↔
    ∀ n : ℤ, n%2 ≠ r%2 → a.fst n = 0 ∧ a.snd n = 0 := by
  change CoeffPair.toMax p a ∈ pairParitySubspace r ↔ _
  rw [mem_pairParitySubspace,Coeff.mem_paritySubspace,Coeff.mem_paritySubspace]
  constructor
  · rintro ⟨hf,hs⟩ n hn
    exact ⟨hf n hn,hs n hn⟩
  · intro h
    exact ⟨fun n hn => (h n hn).1,fun n hn => (h n hn).2⟩

theorem sourceParityProjection_mem (r : ℤ) (a : CoeffPair p) : sourceParityProjection r a ∈ sourceParitySubspace r := by
  change (CoeffPair.toMax p) ((CoeffPair.toMax p).symm
    (pairParityProjection r (CoeffPair.toMax p a))) ∈ pairParitySubspace r
  rw [ContinuousLinearEquiv.apply_symm_apply]
  exact pairParityProjection_mem r _

theorem sourceParityProjection_zero_add_one (a : CoeffPair p) : sourceParityProjection 0 a + sourceParityProjection 1 a = a := by
  change (CoeffPair.toMax p).symm (pairParityProjection 0 (CoeffPair.toMax p a)) +
    (CoeffPair.toMax p).symm (pairParityProjection 1 (CoeffPair.toMax p a)) = a
  rw [← map_add,pairParityProjection_zero_add_one,ContinuousLinearEquiv.symm_apply_apply]

theorem isCompl_sourceParitySubspaces : IsCompl (sourceParitySubspace (p := p) 0) (sourceParitySubspace 1) := by
  constructor
  · apply Submodule.disjoint_def.mpr
    intro a ha hb
    apply (CoeffPair.toMax p).injective
    rw [map_zero]
    exact (Submodule.disjoint_def.mp isCompl_pairParitySubspaces.disjoint) _ ha hb
  · rw [codisjoint_iff_le_sup]
    intro a _
    exact Submodule.mem_sup.mpr ⟨sourceParityProjection 0 a,sourceParityProjection_mem 0 a,sourceParityProjection 1 a,sourceParityProjection_mem 1 a,sourceParityProjection_zero_add_one a⟩

/-- Doubling frequencies identifies period-one pairs isometrically with the even subspace. -/
def sourcePeriodOneEquiv : CoeffPair p ≃ₗᵢ[ℂ] sourceParitySubspace (p := p) 0 where
  toFun a := ⟨periodOnePair a,periodOnePotential_mem a⟩
  invFun a := WithLp.toLp p (Coeff.periodHalve a.val.fst,Coeff.periodHalve a.val.snd)
  left_inv a := by
    apply WithLp.ofLp_injective
    exact Prod.ext (Coeff.periodHalve_periodDouble a.fst) (Coeff.periodHalve_periodDouble a.snd)
  right_inv a := by
    apply Subtype.ext
    apply WithLp.ofLp_injective
    exact Prod.ext
      ((Coeff.periodDouble_periodHalve a.val.fst).trans
        ((Coeff.parityProjection_eq_self_iff 0 a.val.fst).mpr a.property.1))
      ((Coeff.periodDouble_periodHalve a.val.snd).trans
        ((Coeff.parityProjection_eq_self_iff 0 a.val.snd).mpr a.property.2))
  map_add' a b := by apply Subtype.ext; exact periodOnePair.map_add a b
  map_smul' c a := by apply Subtype.ext; exact periodOnePair.map_smul c a
  norm_map' := norm_periodOnePair

theorem mem_sourceDomainParitySubspace (r : ℤ) (a : WeightedCoeffPair (Weight.sobolev 1) p) :
    a ∈ sourceDomainParitySubspace r ↔ sourceDomainInclusion a ∈ sourceParitySubspace r := by
  change WeightedCoeffPair.toMax (Weight.sobolev 1) p a ∈ domainParitySubspace r ↔
    (CoeffPair.toMax p) ((CoeffPair.toMax p).symm
      (domainInclusion (WeightedCoeffPair.toMax (Weight.sobolev 1) p a))) ∈ pairParitySubspace r
  rw [ContinuousLinearEquiv.apply_symm_apply,mem_domainParitySubspace]

theorem isClosed_sourceDomainParitySubspace (r : ℤ) :
    IsClosed (sourceDomainParitySubspace (p := p) r : Set (WeightedCoeffPair (Weight.sobolev 1) p)) :=
  (isClosed_domainParitySubspace r).preimage (WeightedCoeffPair.toMax (Weight.sobolev 1) p).continuous

theorem norm_sourceParityProjection_apply_le (hp : p ≠ ⊤) (r : ℤ) (a : CoeffPair p) : ‖sourceParityProjection r a‖ ≤ ‖a‖ := by
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos
    (zero_lt_one.trans_le (show 1 ≤ p from Fact.out)).ne' hp
  rw [WithLp.prod_norm_eq_add hp0,WithLp.prod_norm_eq_add hp0]
  change (‖Coeff.parityProjection r a.fst‖^p.toReal+‖Coeff.parityProjection r a.snd‖^p.toReal)^(1/p.toReal) ≤ _
  gcongr
  · exact Coeff.norm_parityProjection_apply_le r a.fst
  · exact Coeff.norm_parityProjection_apply_le r a.snd

/-- The bounded parity mask on the one-derivative domain. -/
def sourceDomainParityProjection (r : ℤ) : WeightedCoeffPair (Weight.sobolev 1) p →L[ℂ] WeightedCoeffPair (Weight.sobolev 1) p :=
  (WeightedCoeffPair.toMax (Weight.sobolev 1) p).symm.conjContinuousAlgEquiv (domainParityProjection r)

theorem sourceParityProjection_eq_self_iff (r : ℤ) (a : CoeffPair p) : sourceParityProjection r a = a ↔ a ∈ sourceParitySubspace r := by
  change (CoeffPair.toMax p).symm (pairParityProjection r (CoeffPair.toMax p a)) = a ↔
    CoeffPair.toMax p a ∈ pairParitySubspace r
  rw [← pairParityProjection_eq_self_iff]
  constructor
  · intro h
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using congrArg (CoeffPair.toMax p) h
  · intro h
    rw [h,ContinuousLinearEquiv.symm_apply_apply]

theorem sourceParityProjection_idempotent (r : ℤ) : IsIdempotentElem (sourceParityProjection (p := p) r) :=
  (pairParityProjection_idempotent (p := p) r).map ((CoeffPair.toMax p).symm.conjContinuousAlgEquiv)

theorem range_sourceParityProjection (r : ℤ) : (sourceParityProjection (p := p) r).range = sourceParitySubspace r := by
  ext a
  constructor
  · rintro ⟨x,rfl⟩
    exact sourceParityProjection_mem r x
  · intro ha
    exact ⟨a,(sourceParityProjection_eq_self_iff r a).mpr ha⟩

theorem ker_sourceParityProjection_zero : (sourceParityProjection (p := p) 0).ker = sourceParitySubspace 1 := by
  ext a
  change sourceParityProjection 0 a = 0 ↔ a ∈ sourceParitySubspace 1
  rw [← sourceParityProjection_eq_self_iff]
  constructor
  · intro h
    simpa only [h,zero_add] using sourceParityProjection_zero_add_one a
  · intro h
    have hs := sourceParityProjection_zero_add_one a
    rw [h] at hs
    exact add_right_cancel (hs.trans (zero_add a).symm)

theorem isTopCompl_sourceParitySubspaces : Submodule.IsTopCompl (sourceParitySubspace (p := p) 0) (sourceParitySubspace 1) := by
  have h := ContinuousLinearMap.IsIdempotentElem.isTopCompl (sourceParityProjection_idempotent (p := p) 0)
  rwa [range_sourceParityProjection,ker_sourceParityProjection_zero] at h


/-- The printed even-subspace condition, including negative frequencies. -/
theorem mem_sourceParitySubspace_zero_iff (a : CoeffPair p) :
    a ∈ sourceParitySubspace 0 ↔ ∀ m : ℤ, a.fst (2*m+1) = 0 ∧ a.snd (2*m+1) = 0 := by
  rw [mem_sourceParitySubspace]
  constructor
  · intro h m
    exact h (2*m+1) (by omega)
  · intro h n hn
    have he : n = 2*(n/2)+1 := by omega
    simpa only [← he] using h (n/2)

/-- The printed odd-subspace condition, including negative frequencies. -/
theorem mem_sourceParitySubspace_one_iff (a : CoeffPair p) :
    a ∈ sourceParitySubspace 1 ↔ ∀ m : ℤ, a.fst (2*m) = 0 ∧ a.snd (2*m) = 0 := by
  rw [mem_sourceParitySubspace]
  constructor
  · intro h m
    exact h (2*m) (by omega)
  · intro h n hn
    have he : n = 2*(n/2) := by omega
    simpa only [← he] using h (n/2)

@[simp] theorem sourceParityProjection_fst (r : ℤ) (a : CoeffPair p) (n : ℤ) :
    (sourceParityProjection r a).fst n = if n%2 = r%2 then a.fst n else 0 :=
  Coeff.parityProjection_apply r a.fst n

@[simp] theorem sourceParityProjection_snd (r : ℤ) (a : CoeffPair p) (n : ℤ) :
    (sourceParityProjection r a).snd n = if n%2 = r%2 then a.snd n else 0 :=
  Coeff.parityProjection_apply r a.snd n

@[simp] theorem sourcePeriodOneEquiv_val (a : CoeffPair p) :
    (sourcePeriodOneEquiv a).val = periodOnePair a := rfl

@[simp] theorem sourcePeriodOneEquiv_symm_fst (a : sourceParitySubspace (p := p) 0) (n : ℤ) :
    (sourcePeriodOneEquiv.symm a).fst n = a.val.fst (2*n) := rfl

@[simp] theorem sourcePeriodOneEquiv_symm_snd (a : sourceParitySubspace (p := p) 0) (n : ℤ) :
    (sourcePeriodOneEquiv.symm a).snd n = a.val.snd (2*n) := rfl

end NLS.ZakharovShabat
