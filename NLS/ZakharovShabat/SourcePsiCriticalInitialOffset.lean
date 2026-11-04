import NLS.ZakharovShabat.SourcePsiCriticalFilledTail
import NLS.ZakharovShabat.SourceCriticalHalfExponentOffsets
import NLS.SequenceSpaces.DeletedOperatorExtension

/-! # The initial gap-normalized actual root difference

A single scalar sequence is used throughout the exponent bootstrap:
the critical-filled actual root difference divided by the actual gap,
with value zero on collapsed gaps. Original squared-gap estimates
construct its half-exponent bound uniformly in the deleted index.
-/
noncomputable section
set_option autoImplicit false
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Fill the omitted root critically, then subtract the actual critical displacement. -/
def sourcePsiCriticalDifference (hp : p ≠ ⊤) (hp1 : 1 < p)
    (s : (n : ℤ) → CoeffPair p → DeletedCoeff p n) (n : ℤ) (ψ : CoeffPair p) : Coeff p :=
  sourcePsiFillDeletedRoot n (s n ψ) (sourceCriticalRoot hp hp1 ψ n)-sourceCriticalDisplacement hp hp1 ψ

@[simp] theorem sourcePsiCriticalDifference_same (hp : p ≠ ⊤) (hp1 : 1 < p)
    (s : (n : ℤ) → CoeffPair p → DeletedCoeff p n) (n : ℤ) (ψ : CoeffPair p) :
    sourcePsiCriticalDifference hp hp1 s n ψ n = 0 := by
  have h := displacedRoots_sourcePsiFillDeletedRoot_same n (s n ψ) (sourceCriticalRoot hp hp1 ψ n)
  simp only [displacedRoots,sourceCriticalRoot] at h
  simp only [sourcePsiCriticalDifference,lp.coeFn_sub,Pi.sub_apply,sourceCriticalDisplacement,
    canonicalCriticalDisplacement_apply,sourceCriticalRoot]
  linear_combination h

/-- At every retained index this is the actual root difference, with no free lattice term. -/
theorem sourcePsiCriticalDifference_other (hp : p ≠ ⊤) (hp1 : 1 < p)
    (s : (n : ℤ) → CoeffPair p → DeletedCoeff p n) (n k : ℤ) (hkn : k ≠ n) (ψ : CoeffPair p) :
    sourcePsiCriticalDifference hp hp1 s n ψ k =
      displacedRoots (s n ψ : Coeff p) k-sourceCriticalRoot hp hp1 ψ k := by
  simp only [sourcePsiCriticalDifference,lp.coeFn_sub,Pi.sub_apply,
    sourcePsiFillDeletedRoot_apply_other n k hkn,sourceCriticalDisplacement,
    canonicalCriticalDisplacement_apply,displacedRoots,sourceCriticalRoot]
  ring

/-- The fixed scalar sequence whose membership is improved by the bootstrap. -/
def sourcePsiCriticalGapNormalized (hp : p ≠ ⊤) (hp1 : 1 < p)
    (s : (n : ℤ) → CoeffPair p → DeletedCoeff p n) (n : ℤ) (ψ : CoeffPair p) (k : ℤ) : ℂ :=
  sourcePsiCriticalDifference hp hp1 s n ψ k/sourcePeriodicGapDisplacement hp hp1 ψ k

/-- Initial squared-gap offsets and their norm bound for the actual critical difference. -/
theorem SourceLemma12_11Data.exists_local_critical_difference_squared_gap
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W : Set (CoeffPair p)}
    {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
    (H : SourceLemma12_11Data hp hp1 W₀ W s)
    (φ : realTypeSourceLocus p) (hφ : φ.val ∈ W) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ.val ∈ V ∧ V ⊆ W ∧
      ∃ A : ℝ, 0 ≤ A ∧ ∀ ψ ∈ V, ∀ n : ℤ, ∃ β : Coeff p, ‖β‖ ≤ A ∧
        ∀ k : ℤ, sourcePsiCriticalDifference hp hp1 s n ψ k =
          (sourcePeriodicGapDisplacement hp hp1 ψ k)^2*β k := by
  obtain ⟨Va,hVa,hφa,hVaW,L,hL,ha⟩ := H.previous.psi.locally_uniform_offsets φ.val hφ
  obtain ⟨Vq,hVq,hφq,Q,hQ,hq⟩ :=
    exists_local_uniform_sourceCriticalGapQuotient hp hp1 φ.val φ.property
  refine ⟨Va ∩ Vq,hVa.inter hVq,⟨hφa,hφq⟩,fun _ h => hVaW h.1,L+Q,by positivity,?_⟩
  intro ψ hψ n
  obtain ⟨α,hαn,hα,hαnorm⟩ := ha ψ hψ.1 n
  let β := Coeff.deleteCoordinate n (α-sourceCriticalGapQuotient hp hp1 ψ)
  have hβnorm : ‖β‖ ≤ L+Q := by
    have hb : ‖β‖ ≤ ‖α-sourceCriticalGapQuotient hp hp1 ψ‖ := by
      apply lp.norm_mono (zero_lt_one.trans hp1).ne'
      intro m
      by_cases hm : m=n
      · subst m
        simp only [β,Coeff.deleteCoordinate_apply_same,norm_zero]
        exact norm_nonneg _
      · rw [show β m = (α-sourceCriticalGapQuotient hp hp1 ψ) m from
          Coeff.deleteCoordinate_apply_other n m hm _]
    exact hb.trans ((norm_sub_le _ _).trans (add_le_add hαnorm (hq ψ hψ.2).1))
  refine ⟨β,hβnorm,?_⟩
  intro k
  by_cases hkn : k=n
  · subst k
    simp only [sourcePsiCriticalDifference_same,β,Coeff.deleteCoordinate_apply_same,mul_zero]
  · rw [sourcePsiCriticalDifference_other hp hp1 s n k hkn]
    dsimp only [β]
    rw [Coeff.deleteCoordinate_apply_other n k hkn]
    have hc := (hq ψ hψ.2).2 k
    rw [hα k hkn]
    simp only [sourceCriticalRoot,sourceStandardRootMidpoint,lp.coeFn_sub,Pi.sub_apply]
    linear_combination -hc

/-- One actual normalized difference belongs to the half-exponent space, including collapsed gaps. -/
theorem SourceLemma12_11Data.exists_local_critical_gapNormalized_half_exponent
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W : Set (CoeffPair p)}
    {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
    (H : SourceLemma12_11Data hp hp1 W₀ W s)
    (φ : realTypeSourceLocus p) (hφ : φ.val ∈ W) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ.val ∈ V ∧ V ⊆ W ∧
      ∃ A : ℝ, 0 ≤ A ∧ ∀ ψ ∈ V, ∀ n : ℤ,
        ∃ a : Coeff (p/2), ‖a‖ ≤ A ∧
          (∀ k, a k = sourcePsiCriticalGapNormalized hp hp1 s n ψ k) ∧
          ∀ k, sourcePsiCriticalDifference hp hp1 s n ψ k = sourcePeriodicGapDisplacement hp hp1 ψ k*a k := by
  obtain ⟨Vb,hVb,hφb,hVbW,B,hB,hb⟩ := H.exists_local_critical_difference_squared_gap φ hφ
  obtain ⟨_,_,Vg,hVg,hφg,G,hG,hg⟩ :=
    exists_uniform_small_sourcePeriodicGapDisplacement hp hp1 φ.val (by norm_num : (0:ℝ)<1)
  refine ⟨Vb ∩ Vg,hVb.inter hVg,⟨hφb,hφg⟩,fun _ h => hVbW h.1,G*B,by positivity,?_⟩
  intro ψ hψ n
  obtain ⟨β,hβ,hfactor⟩ := hb ψ hψ.1 n
  let : p.HolderTriple p (p/2) := Coeff.holderTriple_half p
  let a := Coeff.quasiHolderProduct (r := p/2) (sourcePeriodicGapDisplacement hp hp1 ψ) β
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos (zero_lt_one.trans hp1).ne' hp
  refine ⟨a,(Coeff.norm_quasiHolderProduct_le hp0 hp0 _ _).trans
    (mul_le_mul (hg ψ hψ.2).1 hβ (lp.norm_nonneg' _) hG),?_,?_⟩
  · intro k
    unfold sourcePsiCriticalGapNormalized
    rw [hfactor k]
    change sourcePeriodicGapDisplacement hp hp1 ψ k*β k = _
    by_cases hk : sourcePeriodicGapDisplacement hp hp1 ψ k = 0
    · rw [hk]; simp only [zero_mul,zero_pow (by decide : (2:ℕ) ≠ 0),zero_div]
    · field_simp
  · intro k
    rw [hfactor k]
    change _ = _*(_*β k)
    ring

end NLS.ZakharovShabat
