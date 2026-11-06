import NLS.Articles.KdVConvexity.GlobalArnoldCoercivity
import NLS.KdV.HillFiniteActionRealization

/-! # Physical realization of every finite head of the weighted Arnold cone -/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.Articles.KdVConvexity
open NLS.KdV

def baseActionHeadSet (N : ℕ) : Finset ℤ :=
  (Finset.range N).image (fun k => actionIndexEquiv.symm ⟨k+1,by omega⟩)

theorem mem_baseActionHeadSet (N : ℕ) (n : ℕ+) :
    actionIndexEquiv.symm n ∈ baseActionHeadSet N ↔ (n : ℕ) ≤ N := by
  classical
  simp only [baseActionHeadSet, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨k,hk,he⟩
    have he' := congrArg (fun m : ℕ+ => (m : ℕ)) (actionIndexEquiv.symm.injective he)
    change k+1 = (n : ℕ) at he'
    omega
  · intro hn
    refine ⟨(n : ℕ)-1,by have := n.pos; omega,?_⟩
    apply congrArg actionIndexEquiv.symm
    apply Subtype.ext
    exact Nat.sub_add_cancel n.pos

theorem exists_source_finite_Arnold_head
    (I : PeriodOneHminusOne → BaseActionSpace)
    (hrec : ∀ q (hr : IsRealPeriodOneHminusOne q) (n : ℕ+),
      (I q).val (actionIndexEquiv.symm n) = hillHminusRealGapContourMoment q hr n 0)
    (b : BaseActionSpace) (hb : b ∈ WeightedCoeff.nonnegativeLocus baseActionWeight 1)
    (N : ℕ) :
    ∃ q : PeriodOneHminusOne, ∃ _hr : IsRealPeriodOneHminusOne q,
      q.val 0 = 0 ∧ I q = WeightedCoeff.truncate baseActionWeight 1 (baseActionHeadSet N) b := by
  classical
  let a : ℕ → ℝ := fun k => (b.val (actionIndexEquiv.symm ⟨k+1,by omega⟩)).re
  obtain ⟨p,hp⟩ := exists_hillOriginalSource_finite_actions a
    (fun k => (hb _).2) (Finset.range N)
  let q := hillOriginalHminusSource p.val.val
  have hr : IsRealPeriodOneHminusOne q := hillOriginalHminusSource_real p.val.val p.val.property.2
  refine ⟨q,hr,?_,?_⟩
  · rw [hillOriginalHminusSource_apply, mul_zero]
    exact (mem_hillRealMeanZeroSourceSubmodule p.val).mp p.property
  · apply Subtype.ext
    funext k
    let n := actionIndexEquiv k
    have hn : (n : ℕ)-1+1 = (n : ℕ) := by have := n.pos; omega
    have hi := hp ((n : ℕ)-1)
    rw [hn] at hi
    have hn' : (⟨(n : ℕ)-1+1,by omega⟩ : ℕ+) = n := Subtype.ext hn
    dsimp only [a] at hi
    rw [hn'] at hi
    have hrb : ((b.val k).re : ℂ) = b.val k := by
      apply Complex.ext <;> simp only [ofReal_re,ofReal_im]
      exact (hb k).1.symm
    have hk : actionIndexEquiv.symm n = k := Equiv.symm_apply_apply _ _
    rw [←hk, hrec q hr n, hillHminusRealGapContourMoment_original_source
      (⟨p.val.val,p.val.property⟩ : RealPeriodOneHillPotential), hi,
      WeightedCoeff.truncate_apply]
    have hcond : (n : ℕ)-1 < N ↔ (n : ℕ) ≤ N := by have := n.pos; omega
    have hmem : k ∈ baseActionHeadSet N ↔ (n : ℕ) ≤ N := by
      simpa only [hk] using mem_baseActionHeadSet N n
    simp only [Finset.mem_range,hcond,hk,hmem]
    split_ifs <;> simp only [ofReal_zero,hrb]

end NLS.Articles.KdVConvexity
