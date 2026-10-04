import NLS.ZakharovShabat.SourcePsiExtensionUniformFilledStability
import NLS.ZakharovShabat.SourcePsiGapProductDiscBound
import NLS.ZakharovShabat.SourcePsiMidpointShiftedDiscBound
import NLS.ZakharovShabat.SourceAbelianUniformDiscFamily

/-! # Uniform actual psi bounds on central complex gaps

Compactness of the real gap-root product and uniform filled-branch
stability control the quotient on a selected enclosing disc. The collar
between the inner and outer discs separates every other midpoint. A
bounded midpoint displacement then controls the lattice-scaled denominator
for all deleted indices at once, without a deleted-index cutoff.
-/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A positive collar and a bounded displacement control the chi factor
on a shifted disc, uniformly even when the deleted index is nearby. -/
theorem norm_sourcePsiMidpointFilledRegularFactor_le_of_collar
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n k : ℤ) (a : DeletedCoeff p n)
    (ψ : CoeffPair p) (z c : ℂ) (R d D M : ℝ)
    (hd : 0 < d) (hD : 0 ≤ D) (hM : 0 ≤ M)
    (hz : ‖z-c‖ ≤ R)
    (hmid : ‖sourceStandardRootMidpoint hp hp1 ψ n-(Real.pi:ℂ)*n‖ ≤ D)
    (hden : d ≤ ‖sourceStandardRootMidpoint hp hp1 ψ n-z‖)
    (hQ : ‖sourceSingleRootQuotientJointProduct hp hp1 k
      (z,(sourcePsiFillDeletedRoot n a (sourceStandardRootMidpoint hp hp1 ψ n),ψ))‖ ≤ M) :
    ‖sourcePsiMidpointFilledRegularFactor hp hp1 n k a ψ z‖ ≤
      M*(1+(D+R+‖c-(Real.pi:ℂ)*k‖)/d) := by
  let b := D+R+‖c-(Real.pi:ℂ)*k‖
  have hb : 0 ≤ b := by dsimp [b]; linarith [norm_nonneg (z-c),norm_nonneg (c-(Real.pi:ℂ)*k)]
  have htri : Real.pi*|((n-k:ℤ):ℝ)| ≤ ‖sourceStandardRootMidpoint hp hp1 ψ n-z‖+b := by
    have h := norm_add_le ((Real.pi:ℂ)*n-sourceStandardRootMidpoint hp hp1 ψ n)
      (sourceStandardRootMidpoint hp hp1 ψ n-z)
    have h' := norm_add_le ((Real.pi:ℂ)*n-z) (z-c)
    have h'' := norm_add_le ((Real.pi:ℂ)*n-c) (c-(Real.pi:ℂ)*k)
    simp only [sub_add_sub_cancel] at h h' h''
    nth_rw 2 [norm_sub_rev] at h
    rw [norm_free_center_sub n k] at h''
    dsimp only [b]
    linarith
  have hpos := hd.trans_le hden
  simp only [sourcePsiMidpointFilledRegularFactor,sourcePsiGapRegularFactor,
    displacedRoots_sourcePsiFillDeletedRoot_same,norm_mul,norm_div,norm_I,one_mul,
    Complex.norm_real,Real.norm_of_nonneg Real.pi_pos.le,Complex.norm_intCast]
  rw [← mul_div_assoc]
  apply (div_le_iff₀ hpos).mpr
  have hbd : b ≤ b/d*‖sourceStandardRootMidpoint hp hp1 ψ n-z‖ := by
    calc
      b = b/d*d := (div_mul_cancel₀ _ hd.ne').symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hden (div_nonneg hb hd.le)
  calc
    _ ≤ Real.pi*|((n-k:ℤ):ℝ)| * M := mul_le_mul_of_nonneg_left hQ (by positivity)
    _ ≤ (‖sourceStandardRootMidpoint hp hp1 ψ n-z‖+b)*M := mul_le_mul_of_nonneg_right htri hM
    _ ≤ M*(1+b/d)*‖sourceStandardRootMidpoint hp hp1 ψ n-z‖ := by nlinarith

/-- On each selected moving gap, the actual quotient and chi errors
share one bound for every deleted index, including collapsed gaps. -/
theorem SourcePsiIsolatingComplexExtension.exists_local_selectedGap_bounds
    {hp : p ≠ ⊤} {hp1 : 1 < p} {V : Set (CoeffPair p)}
    {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
    (hs : SourcePsiIsolatingComplexExtension hp hp1 V s)
    (φ : realTypeSourceSubmodule p) (k : ℤ) :
    ∃ T : Set (CoeffPair p), IsOpen T ∧ φ.val ∈ T ∧ T ⊆ V ∧
      ∃ M : ℝ, 0 ≤ M ∧ ∀ ψ ∈ T, ∀ n : ℤ, ∀ z ∈ sourcePeriodicSegment hp hp1 ψ k,
        ‖sourceSingleRootQuotientJointProduct hp hp1 k
          (z,(sourcePsiFillDeletedRoot n (s n ψ) (sourceStandardRootMidpoint hp hp1 ψ n),ψ))-1‖ ≤ M ∧
        (k ≠ n → ‖sourcePsiMidpointFilledRegularFactor hp hp1 n k (s n ψ) ψ z-Complex.I‖ ≤ M) := by
  obtain ⟨A,hA⟩ := exists_sourceAbelianUniformDiscFamily hp hp1 univ isOpen_univ φ (mem_univ _)
  have hbase : φ.val ∈ ball A.source.val A.sourceRadius := by rw [hA]; exact mem_ball_self A.sourceRadius_pos
  obtain ⟨δ,Q,hδ,hQ,hquot⟩ := exists_sourcePsiQuotient_disc_bound_near_gapProduct hp hp1 φ k
    (A.center k) (A.outer k) (A.avoids_other φ.val hbase k)
  obtain ⟨r,hr,hrV,hgraph⟩ := hs.exists_uniform_midpointFilled_graph_radius φ δ hδ
  obtain ⟨_,_,G,hG,hφG,D,hD,hmid⟩ := exists_uniform_small_sourcePeriodicMidpointDisplacement hp hp1 φ.val
    (by norm_num : (0:ℝ) < 1)
  let d := A.outer k-A.inner k
  have hd : 0 < d := sub_pos.mpr (A.inner_lt k)
  let b := D+A.inner k+‖A.center k-(Real.pi:ℂ)*k‖
  have hinner := (A.inner_pos k).le
  have hb : 0 ≤ b := by dsimp [b]; positivity
  let M := Q*(1+b/d)+Q+1
  have hM : 0 ≤ M := by dsimp [M]; positivity
  refine ⟨ball φ.val r ∩ (ball A.source.val A.sourceRadius ∩ G),
    isOpen_ball.inter (isOpen_ball.inter hG),⟨mem_ball_self hr,hbase,hφG⟩,
    fun _ h => hrV h.1,M,hM,?_⟩
  intro ψ hψ n z hz
  have hzinner := mem_ball.mp (A.segment_subset ψ hψ.2.1 k hz)
  rw [dist_eq_norm] at hzinner
  have hzouter : z ∈ closedBall (A.center k) (A.outer k) := by
    rw [mem_closedBall,dist_eq_norm]
    exact hzinner.le.trans (A.inner_lt k).le
  let q₀ := (sourcePsiFillDeletedRoot n (sourcePsiGapRoot hp hp1 n φ)
    (sourceStandardRootMidpoint hp hp1 φ.val n),φ.val)
  have hq₀ : q₀ ∈ sourcePeriodicGapRootSet hp hp1 φ.val ×ˢ {φ.val} :=
    ⟨sourcePsiGapRoot_filled_mem_periodicGapRootSet hp hp1 φ n,rfl⟩
  have hnear := mem_cthickening_of_dist_le _ q₀ δ _ hq₀ (hgraph ψ hψ.1 n).le
  have hq := hquot _ hnear z hzouter
  have hqerr : ‖sourceSingleRootQuotientJointProduct hp hp1 k
      (z,(sourcePsiFillDeletedRoot n (s n ψ) (sourceStandardRootMidpoint hp hp1 ψ n),ψ))-1‖ ≤ Q+1 := by
    exact (norm_sub_le _ _).trans (by simpa only [norm_one] using add_le_add hq (le_refl (1:ℝ)))
  refine ⟨hqerr.trans (by dsimp [M]; nlinarith [mul_nonneg hQ (show 0 ≤ 1+b/d by positivity)]),?_⟩
  intro hkn
  have hout : sourceStandardRootMidpoint hp hp1 ψ n ∉ closedBall (A.center k) (A.outer k) := by
    intro hin
    exact A.avoids_other ψ hψ.2.1 k hin n hkn.symm (sourcePeriodicMidpoint_mem_segment hp hp1 ψ n)
  have hdist : A.outer k < ‖sourceStandardRootMidpoint hp hp1 ψ n-A.center k‖ := by
    simpa only [mem_closedBall,dist_eq_norm,not_le] using hout
  have hden : d ≤ ‖sourceStandardRootMidpoint hp hp1 ψ n-z‖ := by
    have htri := norm_add_le (sourceStandardRootMidpoint hp hp1 ψ n-z) (z-A.center k)
    rw [sub_add_sub_cancel] at htri
    dsimp [d]
    linarith
  have hmidpoint : ‖sourceStandardRootMidpoint hp hp1 ψ n-(Real.pi:ℂ)*n‖ ≤ D := by
    have h := (lp.norm_apply_le_norm (zero_lt_one.trans hp1).ne'
      (sourcePeriodicMidpointDisplacement hp hp1 ψ) n).trans (hmid ψ hψ.2.2).1
    simpa only [sourcePeriodicMidpointDisplacement_apply,sourceStandardRootMidpoint] using h
  have hc := norm_sourcePsiMidpointFilledRegularFactor_le_of_collar hp hp1 n k (s n ψ) ψ z
    (A.center k) (A.inner k) d D Q hd hD hQ hzinner.le hmidpoint hden hq
  exact (norm_sub_le _ _).trans (by
    rw [norm_I]
    dsimp only [M,b] at *
    linarith)

/-- A finite selected family has a common bound and source neighborhood;
the bound is uniform over the entire infinite deleted-index family. -/
theorem SourcePsiIsolatingComplexExtension.exists_local_finiteGap_bounds
    {hp : p ≠ ⊤} {hp1 : 1 < p} {V : Set (CoeffPair p)}
    {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
    (hs : SourcePsiIsolatingComplexExtension hp hp1 V s)
    (φ : realTypeSourceSubmodule p) (F : Finset ℤ) :
    ∃ T : Set (CoeffPair p), IsOpen T ∧ φ.val ∈ T ∧ T ⊆ V ∧
      ∃ M : ℝ, 0 ≤ M ∧ ∀ ψ ∈ T, ∀ n : ℤ, ∀ k ∈ F, ∀ z ∈ sourcePeriodicSegment hp hp1 ψ k,
        ‖sourceSingleRootQuotientJointProduct hp hp1 k
          (z,(sourcePsiFillDeletedRoot n (s n ψ) (sourceStandardRootMidpoint hp hp1 ψ n),ψ))-1‖ ≤ M ∧
        (k ≠ n → ‖sourcePsiMidpointFilledRegularFactor hp hp1 n k (s n ψ) ψ z-Complex.I‖ ≤ M) := by
  classical
  choose T hT hφT hTV M hM hbound using hs.exists_local_selectedGap_bounds φ
  let O := T 0 ∩ ⋂ k ∈ F, T k
  refine ⟨O,(hT 0).inter (isOpen_biInter_finset (fun k _ => hT k)),
    ⟨hφT 0,by simp only [mem_iInter]; exact fun k _ => hφT k⟩,
    fun _ h => hTV 0 h.1,∑ k ∈ F, M k,Finset.sum_nonneg (fun k _ => hM k),?_⟩
  intro ψ hψ n k hk z hz
  have hψk := (mem_iInter.mp (mem_iInter.mp hψ.2 k)) hk
  have hMk : M k ≤ ∑ j ∈ F, M j := Finset.single_le_sum (fun j _ => hM j) hk
  exact ⟨((hbound k ψ hψk n z hz).1).trans hMk,
    fun hkn => ((hbound k ψ hψk n z hz).2 hkn).trans hMk⟩

end NLS.ZakharovShabat
