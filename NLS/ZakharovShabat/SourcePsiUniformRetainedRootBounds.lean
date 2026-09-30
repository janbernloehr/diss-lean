import NLS.ZakharovShabat.SourcePsiLemma12_12
import NLS.ZakharovShabat.SourcePeriodicGapTails

/-!
# Uniform scalar bounds for actual retained psi roots and chi

The squared-gap offset sequence has a locally bounded norm independent
of the deleted index. The midpoint and gap sequence norms then bound
every retained root's displacement from the free lattice. The chi tail
majorants likewise give one scalar bound for all sufficiently distant
selected discs and all deleted indices.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

namespace SourcePsiSquaredGapComplexExtension
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- One local bound controls every actual retained root, uniformly in
both integer indices, at any complex source in the psi domain. -/
theorem exists_local_uniform_retainedRoot_displacement_bound
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 W s) (φ : CoeffPair p) (hφ : φ ∈ W) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧ V ⊆ W ∧
      ∃ A : ℝ, 0 < A ∧ ∀ ψ ∈ V, ∀ n m : ℤ, m ≠ n →
        ‖displacedRoots (s n ψ : Coeff p) m-(Real.pi:ℂ)*m‖ ≤ A := by
  obtain ⟨Va,hVa,hφa,hVaW,L,hL,hoffset⟩ := hs.locally_uniform_squared_gap_offsets φ hφ
  obtain ⟨_,_,Vm,hVm,hφm,D,hD,hmid⟩ :=
    exists_uniform_small_sourcePeriodicMidpointDisplacement hp hp1 φ (by norm_num : 0 < (1:ℝ))
  obtain ⟨_,_,Vg,hVg,hφg,G,hG,hgap⟩ :=
    exists_uniform_small_sourcePeriodicGapDisplacement hp hp1 φ (by norm_num : 0 < (1:ℝ))
  let V := (Va ∩ Vm) ∩ Vg
  let A := D+G^2*L+1
  have hA : 0 < A := by dsimp only [A]; positivity
  refine ⟨V,(hVa.inter hVm).inter hVg,⟨⟨hφa,hφm⟩,hφg⟩,
    (fun ψ hψ => hVaW hψ.1.1),A,hA,?_⟩
  intro ψ hψ n m hmn
  obtain ⟨α,_,hfactor,hα⟩ := hoffset ψ hψ.1.1 n
  have hαm : ‖α m‖ ≤ L :=
    (lp.norm_apply_le_norm (zero_lt_one.trans hp1).ne' α m).trans hα
  have hgm : ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖ ≤ G :=
    (lp.norm_apply_le_norm (zero_lt_one.trans hp1).ne' _ m).trans (hgap ψ hψ.2).1
  have htm : ‖sourceStandardRootMidpoint hp hp1 ψ m-(Real.pi:ℂ)*m‖ ≤ D := by
    simpa only [sourcePeriodicMidpointDisplacement_apply,sourceStandardRootMidpoint] using
      (lp.norm_apply_le_norm (zero_lt_one.trans hp1).ne' _ m).trans (hmid ψ hψ.1.2).1
  rw [hfactor m hmn,show sourceStandardRootMidpoint hp hp1 ψ m+
    (sourcePeriodicGapDisplacement hp hp1 ψ m)^2*α m-(Real.pi:ℂ)*m =
      (sourceStandardRootMidpoint hp hp1 ψ m-(Real.pi:ℂ)*m)+
        (sourcePeriodicGapDisplacement hp hp1 ψ m)^2*α m by ring]
  calc
    _ ≤ ‖sourceStandardRootMidpoint hp hp1 ψ m-(Real.pi:ℂ)*m‖+
        ‖(sourcePeriodicGapDisplacement hp hp1 ψ m)^2*α m‖ := norm_add_le _ _
    _ ≤ D+G^2*L := by
      rw [norm_mul,norm_pow]
      exact add_le_add htm (mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hgm 2) hαm
        (norm_nonneg _) (sq_nonneg _))
    _ ≤ A := by dsimp only [A]; linarith

end SourcePsiSquaredGapComplexExtension

namespace SourcePsiFactorMajorantComplexExtension
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- The existing sequence majorants give one scalar chi bound on all
selected tail discs, uniformly in both indices on a source neighborhood. -/
theorem exists_local_uniform_midpointFilledRegularFactor_tail_bound
    (hs : SourcePsiFactorMajorantComplexExtension hp hp1 W s) (φ : CoeffPair p) (hφ : φ ∈ W) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧ V ⊆ W ∧
      ∃ K : ℕ, ∃ M : ℝ, 0 < M ∧ ∀ ψ ∈ V, ∀ n m : ℤ, K ≤ m.natAbs → m ≠ n →
        ∀ z ∈ closedBall ((Real.pi:ℂ)*m) (Real.pi/8),
          ‖sourcePsiMidpointFilledRegularFactor hp hp1 n m (s n ψ) ψ z‖ ≤ M := by
  obtain ⟨V,hV,hφV,hVW,K,C,hC,hmajor⟩ := hs.locally_uniform_factor_tail_majorants φ hφ
  refine ⟨V,hV,hφV,hVW,K,C+2,by linarith,?_⟩
  intro ψ hψ n m hm hmn z hz
  obtain ⟨E,hE,hbound⟩ := hmajor ψ hψ n
  have hpoint := (hbound m hm hmn z hz).trans
    ((lp.norm_apply_le_norm (zero_lt_one.trans hp1).ne' E m).trans hE)
  have htri := norm_sub_le (sourcePsiMidpointFilledRegularFactor hp hp1 n m (s n ψ) ψ z-I) (-I)
  rw [sub_neg_eq_add,sub_add_cancel,norm_neg,norm_I] at htri
  linarith

end SourcePsiFactorMajorantComplexExtension
end NLS.ZakharovShabat
