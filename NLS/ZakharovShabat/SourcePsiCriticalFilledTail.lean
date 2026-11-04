import NLS.ZakharovShabat.SourcePsiOriginalRootFamily
import NLS.ZakharovShabat.SourcePsiQuotientUniformGapProductTail
import NLS.ZakharovShabat.SourceCriticalDisplacementContinuity
import NLS.ZakharovShabat.SourcePsiCriticalRootComparison
import NLS.ZakharovShabat.SourceCriticalRootRatioSourceAnalytic

/-! # Uniform small tails for the critical-filled actual psi products

The original analytic root branches are equicontinuous in the deleted
index. Norm continuity of the actual critical displacement allows its
insertion at that index without losing equicontinuity. At a real source,
every resulting root lies in its actual periodic gap, so the existing
compact-gap-product quotient estimate applies to the whole family.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W : Set (CoeffPair p)}
variable {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- Filling by the actual critical point preserves a common graph radius at real sources. -/
theorem SourceLemma12_11Data.critical_filled_graph_radius
    (H : SourceLemma12_11Data hp hp1 W₀ W s)
    (φ : realTypeSourceLocus p) (hφ : φ.val ∈ W) (ε : ℝ) (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ ball φ.val r ⊆ W ∧ ∀ ψ ∈ ball φ.val r, ∀ n : ℤ,
      dist (sourcePsiFillDeletedRoot n (s n ψ) (sourceCriticalRoot hp hp1 ψ n),ψ)
        (sourcePsiFillDeletedRoot n (s n φ.val) (sourceCriticalRoot hp hp1 φ.val n),φ.val) < ε := by
  obtain ⟨R,L,hR,hL,hRW,hbranch⟩ := H.original_branch_dist_bound φ.val hφ
  obtain ⟨η,hη,hηball⟩ := Metric.mem_nhds_iff.mp
    ((continuousAt_sourceCriticalDisplacement_of_realType hp hp1 φ.val φ.property).preimage_mem_nhds
      (ball_mem_nhds _ (by positivity : 0 < ε/4)))
  let r := min R (min η (ε/(4*(L+1))))
  have hr : 0 < r := lt_min hR (lt_min hη (by positivity))
  have hrR : r ≤ R := min_le_left _ _
  have hrη : r ≤ η := (min_le_right _ _).trans (min_le_left _ _)
  have hrε : r ≤ ε/(4*(L+1)) := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨r,hr,(ball_subset_ball hrR).trans hRW,?_⟩
  intro ψ hψ n
  have hψdist : dist ψ φ.val < ε/(4*(L+1)) := (mem_ball.mp hψ).trans_le hrε
  have hcritseq : ‖sourceCriticalDisplacement hp hp1 ψ-sourceCriticalDisplacement hp hp1 φ.val‖ < ε/4 := by
    simpa only [mem_preimage,mem_ball,dist_eq_norm] using hηball (ball_subset_ball hrη hψ)
  have hcrit : ‖sourceCriticalRoot hp hp1 ψ n-sourceCriticalRoot hp hp1 φ.val n‖ < ε/4 := by
    have h := (lp.norm_apply_le_norm (zero_lt_one.trans hp1).ne'
      (sourceCriticalDisplacement hp hp1 ψ-sourceCriticalDisplacement hp hp1 φ.val) n).trans_lt hcritseq
    simpa only [lp.coeFn_sub,Pi.sub_apply,sourceCriticalDisplacement,canonicalCriticalDisplacement_apply,
      sourceCriticalRoot,sub_sub_sub_cancel_right] using h
  have heq : sourcePsiFillDeletedRoot n (s n ψ) (sourceCriticalRoot hp hp1 ψ n)-
      sourcePsiFillDeletedRoot n (s n φ.val) (sourceCriticalRoot hp hp1 φ.val n) =
      ((s n ψ:Coeff p)-(s n φ.val:Coeff p))+
        lp.single p n (sourceCriticalRoot hp hp1 ψ n-sourceCriticalRoot hp hp1 φ.val n) := by
    unfold sourcePsiFillDeletedRoot
    rw [add_sub_add_comm,← lp.single_sub]
    congr 2
    ring
  have hfilled : dist
      (sourcePsiFillDeletedRoot n (s n ψ) (sourceCriticalRoot hp hp1 ψ n))
      (sourcePsiFillDeletedRoot n (s n φ.val) (sourceCriticalRoot hp hp1 φ.val n)) ≤ L*dist ψ φ.val+ε/4 := by
    rw [dist_eq_norm,heq]
    exact (norm_add_le _ _).trans (add_le_add (by
      change ‖s n ψ-s n φ.val‖ ≤ L*dist ψ φ.val
      simpa only [dist_eq_norm] using hbranch ψ (ball_subset_ball hrR hψ) n)
      (by simpa only [lp.norm_single (zero_lt_one.trans hp1)] using hcrit.le))
  rw [Prod.dist_eq,max_lt_iff]
  have hsmall : (L+1)*dist ψ φ.val < ε/4 := by
    have h := (lt_div_iff₀ (by positivity : 0 < 4*(L+1))).mp hψdist
    nlinarith
  constructor <;> nlinarith [dist_nonneg (x := ψ) (y := φ.val),mul_nonneg hL (dist_nonneg (x := ψ) (y := φ.val))]

/-- At real sources, critical filling keeps the actual full family in the compact gap product. -/
theorem SourceLemma12_11Data.critical_filled_mem_gapProduct
    (H : SourceLemma12_11Data hp hp1 W₀ W s) (φ : realTypeSourceLocus p) (n : ℤ) :
    sourcePsiFillDeletedRoot n (s n φ.val) (sourceCriticalRoot hp hp1 φ.val n) ∈
      sourcePeriodicGapRootSet hp hp1 φ.val := by
  intro m
  by_cases hm : m=n
  · subst m
    rw [displacedRoots_sourcePsiFillDeletedRoot_same]
    exact sourceCanonicalCriticalPoint_mem_periodicSegment_of_realType hp hp1 n φ.val φ.property
  · rw [displacedRoots_sourcePsiFillDeletedRoot_other n m hm,H.previous.psi.real_agreement n φ]
    exact sourcePsiGapRoot_mem_periodicSegment hp hp1 n m hm φ

/-- The full critical-filled root difference has one local norm bound for every deleted index.
This bounds the exponential in the relative-product estimate uniformly in that index. -/
theorem SourceLemma12_11Data.exists_local_uniform_critical_filled_difference_norm_bound
    (H : SourceLemma12_11Data hp hp1 W₀ W s)
    (φ : realTypeSourceLocus p) (hφ : φ.val ∈ W) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ.val ∈ V ∧ V ⊆ W ∧
      ∃ L : ℝ, 0 ≤ L ∧ ∀ ψ ∈ V, ∀ n : ℤ,
        ‖sourcePsiFillDeletedRoot n (s n ψ) (sourceCriticalRoot hp hp1 ψ n)-
          sourceCriticalDisplacement hp hp1 ψ‖ ≤ L := by
  obtain ⟨r,hr,hrW,hgraph⟩ := H.critical_filled_graph_radius φ hφ 1 (by norm_num)
  obtain ⟨η,hη,hηball⟩ := Metric.mem_nhds_iff.mp
    ((continuousAt_sourceCriticalDisplacement_of_realType hp hp1 φ.val φ.property).preimage_mem_nhds
      (ball_mem_nhds _ (by norm_num : (0:ℝ)<1)))
  let A := ‖canonicalPeriodicLeftDisplacement hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val)‖+
    ‖sourcePeriodicGapDisplacement hp hp1 φ.val‖
  let B := ‖sourceCriticalDisplacement hp hp1 φ.val‖
  refine ⟨ball φ.val r ∩ ball φ.val η,isOpen_ball.inter isOpen_ball,
    ⟨mem_ball_self hr,mem_ball_self hη⟩,fun _ h => hrW h.1,A+B+2,by dsimp [A,B]; positivity,?_⟩
  intro ψ hψ n
  have ha0 : ‖sourcePsiFillDeletedRoot n (s n φ.val) (sourceCriticalRoot hp hp1 φ.val n)‖ ≤ A :=
    norm_gapRoot_le_gap_displacements hp hp1 φ.val _ (H.critical_filled_mem_gapProduct φ n)
  have hgraph' := hgraph ψ hψ.1 n
  rw [Prod.dist_eq,max_lt_iff] at hgraph'
  have ha : ‖sourcePsiFillDeletedRoot n (s n ψ) (sourceCriticalRoot hp hp1 ψ n)‖ ≤ A+1 := by
    have ht := norm_sub_le_norm_sub_add_norm_sub
      (sourcePsiFillDeletedRoot n (s n ψ) (sourceCriticalRoot hp hp1 ψ n))
      (sourcePsiFillDeletedRoot n (s n φ.val) (sourceCriticalRoot hp hp1 φ.val n)) 0
    simp only [sub_zero] at ht
    rw [dist_eq_norm] at hgraph'
    linarith [hgraph'.1]
  have hb : ‖sourceCriticalDisplacement hp hp1 ψ‖ ≤ B+1 := by
    have he : ‖sourceCriticalDisplacement hp hp1 ψ-sourceCriticalDisplacement hp hp1 φ.val‖ < 1 := by
      simpa only [mem_preimage,mem_ball,dist_eq_norm] using hηball hψ.2
    have ht := norm_sub_le_norm_sub_add_norm_sub
      (sourceCriticalDisplacement hp hp1 ψ) (sourceCriticalDisplacement hp hp1 φ.val) 0
    simp only [sub_zero] at ht
    dsimp [B]
    linarith
  exact (norm_sub_le _ _).trans (by linarith)

/-- Actual critical-filled quotients approach one uniformly in both spectral indices
on one complex neighborhood of each real source. -/
theorem SourceLemma12_11Data.exists_local_critical_filled_quotient_small_tail
    (H : SourceLemma12_11Data hp hp1 W₀ W s)
    (φ : realTypeSourceLocus p) (hφ : φ.val ∈ W) (ε : ℝ) (hε : 0 < ε) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ.val ∈ V ∧ V ⊆ W ∧ ∃ K : ℕ,
      ∀ ψ ∈ V, ∀ n k : ℤ, K ≤ k.natAbs →
        sourcePeriodicSegment hp hp1 ψ k ⊆ ball ((Real.pi:ℂ)*k) (Real.pi/8) ∧
        ∀ z ∈ closedBall ((Real.pi:ℂ)*k) (Real.pi/8),
          ‖sourcePsiCriticalFilledQuotient hp hp1 n k (s n ψ) ψ z-1‖ < ε := by
  obtain ⟨δ,hδ,K,htail⟩ := exists_sourcePsiQuotient_uniformSmallTail_near_gapProduct hp hp1 φ ε hε
  obtain ⟨r,hr,hrW,hgraph⟩ := H.critical_filled_graph_radius φ hφ δ hδ
  refine ⟨ball φ.val r,isOpen_ball,mem_ball_self hr,hrW,K,?_⟩
  intro ψ hψ n k hk
  have hmem : (sourcePsiFillDeletedRoot n (s n ψ) (sourceCriticalRoot hp hp1 ψ n),ψ) ∈
      cthickening δ (sourcePeriodicGapRootSet hp hp1 φ.val ×ˢ {φ.val}) :=
    mem_cthickening_of_dist_le _
      (sourcePsiFillDeletedRoot n (s n φ.val) (sourceCriticalRoot hp hp1 φ.val n),φ.val) δ _
      ⟨H.critical_filled_mem_gapProduct φ n,mem_singleton φ.val⟩ (hgraph ψ hψ n).le
  exact htail _ hmem k hk

end NLS.ZakharovShabat
