import NLS.ZakharovShabat.OriginalFiniteChains
import NLS.ZakharovShabat.ClassicalBoundaryJets

/-!
# Finite boundary Taylor kernels and original parity chains

For a chain of length `n+1`, the actual boundary series defines a linear map
on `n+1` two-coordinate Taylor coefficients. Its kernel parametrizes exactly
the original finite parity chains, with a unique original top vector.
-/

noncomputable section
open Set Complex MeasureTheory NLS.Fourier NLS.LinearVolterra
open scoped Matrix.Norms.Elementwise
namespace NLS.ZakharovShabat

/-- A prescribed initial jet gives a unique original chain precisely when all boundary Taylor equations vanish. -/
theorem existsUnique_originalParityChain_iff_boundaryJets (φ : PairSpace 2) (hφ : φ ∈ pairParitySubspace 0)
    (Φ : Curve (ℂ × ℂ)) (hΦ : physicalBase φ =ᵐ[volume.restrict (Ioc 0 1)] extend Φ)
    (z : ℂ) (r : ℤ) (v : ℕ → ℂ × ℂ) (n : ℕ) :
    (∃! a : Domain 2, IsOriginalParityChain φ z r v n a) ↔
      ∀ j ≤ n, classicalBoundaryJet Φ z (wave r 1) (signedInitialJet v) j = 0 := by
  simp_rw [classicalBoundaryJet_signed_eq_zero_iff]
  rw [← exists_originalParityChain_iff_endpoints φ hφ Φ hΦ z r v n]
  constructor
  · exact ExistsUnique.exists
  · rintro ⟨a,ha⟩
    exact ⟨a,ha,fun b hb => hb.unique Φ hΦ ha⟩

/-- Extend a finite two-coordinate jet by zero outside its specified range. -/
def initialJetExtension (N : ℕ) : (Fin N → ℂ × ℂ) →ₗ[ℂ] (ℕ → ℂ × ℂ) where
  toFun w j := if h : j < N then w ⟨j,h⟩ else 0
  map_add' := by intro u v; funext j; by_cases h : j < N <;> simp [h]
  map_smul' := by intro c v; funext j; by_cases h : j < N <;> simp [h]

/-- The finite lower triangular convolution map of the actual boundary Taylor coefficients. -/
def finiteBoundaryJetMap (Φ : Curve (ℂ × ℂ)) (z σ : ℂ) (N : ℕ) :
    (Fin N → ℂ × ℂ) →ₗ[ℂ] (Fin N → ℂ × ℂ) where
  toFun w k := classicalBoundaryJet Φ z σ (initialJetExtension N w) k
  map_add' := by
    intro u v
    funext k
    simp only [map_add,classicalBoundaryJet,Pi.add_apply,Finset.sum_add_distrib]
  map_smul' := by
    intro c v
    funext k
    simp only [map_smul,classicalBoundaryJet,Pi.smul_apply,Finset.smul_sum,RingHom.id_apply]

/-- Membership in the finite kernel is exactly the first `N` boundary Taylor equations. -/
theorem mem_ker_finiteBoundaryJetMap_iff (Φ : Curve (ℂ × ℂ)) (z σ : ℂ) (N : ℕ)
    (w : Fin N → ℂ × ℂ) : w ∈ LinearMap.ker (finiteBoundaryJetMap Φ z σ N) ↔
      ∀ j < N, classicalBoundaryJet Φ z σ (initialJetExtension N w) j = 0 := by
  rw [LinearMap.mem_ker]
  constructor
  · intro h j hj
    exact congrFun h ⟨j,hj⟩
  · intro h
    funext k
    exact h k k.isLt

/-- Every vector in the finite Taylor kernel gives one and only one original parity-chain top vector. -/
theorem existsUnique_originalParityChain_iff_finiteKernel (φ : PairSpace 2) (hφ : φ ∈ pairParitySubspace 0)
    (Φ : Curve (ℂ × ℂ)) (hΦ : physicalBase φ =ᵐ[volume.restrict (Ioc 0 1)] extend Φ)
    (z : ℂ) (r : ℤ) (n : ℕ) (w : Fin (n+1) → ℂ × ℂ) :
    (∃! a : Domain 2, IsOriginalParityChain φ z r (signedInitialJet (initialJetExtension (n+1) w)) n a) ↔
      w ∈ LinearMap.ker (finiteBoundaryJetMap Φ z (wave r 1) (n+1)) := by
  rw [existsUnique_originalParityChain_iff_boundaryJets φ hφ Φ hΦ,
    signedInitialJet_involutive,mem_ker_finiteBoundaryJetMap_iff]
  simp only [Nat.lt_succ_iff]

/-- A top vector determines its entire finite Taylor jet; unused infinite tails introduce no ambiguity. -/
theorem finite_initialJet_unique (φ : PairSpace 2) (z : ℂ) (r : ℤ) (n : ℕ)
    (w u : Fin (n+1) → ℂ × ℂ) (a : Domain 2)
    (hw : IsOriginalParityChain φ z r (signedInitialJet (initialJetExtension (n+1) w)) n a)
    (hu : IsOriginalParityChain φ z r (signedInitialJet (initialJetExtension (n+1) u)) n a) : w = u := by
  funext j
  have he := hw.initial_eq hu j (Nat.le_of_lt_succ j.isLt)
  simp only [signedInitialJet,initialJetExtension,LinearMap.coe_mk,AddHom.coe_mk,dif_pos j.isLt] at he
  exact (smul_right_injective (ℂ × ℂ) (pow_ne_zero _ (neg_ne_zero.mpr (one_ne_zero : (1 : ℂ) ≠ 0)))) he

/-- Every original finite parity root vector is represented by a finite Taylor jet. -/
theorem mem_parity_rootSpace_iff_finite_initial_chain (φ : PairSpace 2) (hφ : φ ∈ pairParitySubspace 0)
    (z : ℂ) (r : ℤ) (n : ℕ) (a : Domain 2) :
    (domainInclusion a ∈ periodicRootSpace (by simp) φ z (n+1) ∧ a ∈ domainParitySubspace r) ↔
      ∃ w : Fin (n+1) → ℂ × ℂ,
        IsOriginalParityChain φ z r (signedInitialJet (initialJetExtension (n+1) w)) n a := by
  rw [mem_parity_rootSpace_iff_exists_initial_chain φ hφ z r n a]
  constructor
  · rintro ⟨v,hv⟩
    refine ⟨fun j => signedInitialJet v j,hv.congr_initial ?_⟩
    intro j hj
    have hj' : j < n+1 := Nat.lt_succ_of_le hj
    simp only [signedInitialJet,initialJetExtension,LinearMap.coe_mk,AddHom.coe_mk,dif_pos hj',
      smul_smul,← mul_pow,neg_one_mul,neg_neg,one_pow,one_smul]
  · rintro ⟨w,hw⟩
    exact ⟨_,hw⟩

/-- A finite original root vector has a unique representing vector in the actual boundary Taylor kernel. -/
theorem mem_parity_rootSpace_iff_existsUnique_boundaryJet (φ : PairSpace 2) (hφ : φ ∈ pairParitySubspace 0)
    (Φ : Curve (ℂ × ℂ)) (hΦ : physicalBase φ =ᵐ[volume.restrict (Ioc 0 1)] extend Φ)
    (z : ℂ) (r : ℤ) (n : ℕ) (a : Domain 2) :
    (domainInclusion a ∈ periodicRootSpace (by simp) φ z (n+1) ∧ a ∈ domainParitySubspace r) ↔
      ∃! w : Fin (n+1) → ℂ × ℂ,
        w ∈ LinearMap.ker (finiteBoundaryJetMap Φ z (wave r 1) (n+1)) ∧
        IsOriginalParityChain φ z r (signedInitialJet (initialJetExtension (n+1) w)) n a := by
  rw [mem_parity_rootSpace_iff_finite_initial_chain φ hφ z r n a]
  constructor
  · rintro ⟨w,hw⟩
    have hk := (existsUnique_originalParityChain_iff_finiteKernel φ hφ Φ hΦ z r n w).mp
      ⟨a,hw,fun b hb => hb.unique Φ hΦ hw⟩
    exact ⟨w,⟨hk,hw⟩,fun u hu => finite_initialJet_unique φ z r n u w a hu.2 hw⟩
  · rintro ⟨w,hw,_⟩
    exact ⟨w,hw.2⟩

end NLS.ZakharovShabat
