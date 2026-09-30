import NLS.ZakharovShabat.SourcePsiQuotientUniformGapProductTail
import NLS.ZakharovShabat.SourcePsiFiniteHeadMidpointLowerBound

/-!
# Uniform midpoint lower bounds for every actual chi factor

All regular quotient midpoint values stay bounded away from zero
near the compact real gap product. Uniform filled-branch stability
puts every deleted-index branch in that same neighborhood. The
midpoint displacement norm controls the lattice ratio from below,
while assigned spectral isolation separates the moving midpoints.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Near every real source, one positive midpoint factor lower bound
works for all omitted and retained indices of the actual analytic
root family. This includes collapsed periodic gaps. -/
theorem SourcePsiIsolatingComplexRootAtlas.exists_local_uniform_midpoint_factor_lowerBound
    {hp : p ≠ ⊤} {hp1 : 1 < p} {U : Set (CoeffPair p)}
    (A : SourcePsiIsolatingComplexRootAtlas hp hp1 U) (φ : realTypeSourceLocus p) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ.val ∈ V ∧
      V ⊆ A.toSourcePsiComplexRootAtlas.sourceBall φ ∧
      ∃ C : ℝ, 0 < C ∧ ∀ ψ ∈ V, ∀ n m : ℤ, m ≠ n →
        C ≤ ‖sourcePsiMidpointFilledRegularFactor hp hp1 n m
          (A.toSourcePsiComplexRootAtlas.branch n ψ) ψ
          (sourceStandardRootMidpoint hp hp1 ψ m)‖ := by
  let B := A.toSourcePsiComplexRootAtlas
  let S := B.localBranch φ
  obtain ⟨δ,c,hδ,hc,hquot⟩ :=
    exists_sourcePsi_midpointQuotient_uniform_lowerBound_near_gapProduct hp hp1 φ
  obtain ⟨r,hr,hrS,hgraph⟩ := S.exists_uniform_midpointFilled_graph_radius δ hδ
  obtain ⟨Vm,hVm,hφVm,D,hD,_,hmiddata⟩ :=
    exists_local_sourcePeriodicMidpoint_tail_lattice_separation hp hp1 φ.val
  let V := ball φ.val r ∩ Vm
  let C := (Real.pi/(Real.pi+2*D))*c
  have hC : 0 < C := by
    dsimp only [C]
    exact mul_pos (div_pos Real.pi_pos (by linarith [Real.pi_pos])) hc
  refine ⟨V,isOpen_ball.inter hVm,⟨mem_ball_self hr,hφVm⟩,
    (fun ψ hψ => ball_subset_ball hrS hψ.1),C,hC,?_⟩
  intro ψ hψ n m hmn
  have hψS : ψ ∈ B.sourceBall φ := ball_subset_ball hrS hψ.1
  have hnear := hgraph ψ hψ.1 n
  rw [← B.eq_local n φ hψS] at hnear
  let q := (sourcePsiFillDeletedRoot n (B.branch n ψ)
    (sourceStandardRootMidpoint hp hp1 ψ n),ψ)
  let q₀ := (sourcePsiFillDeletedRoot n (sourcePsiGapRoot hp hp1 n φ)
    (sourceStandardRootMidpoint hp hp1 φ.val n),φ.val)
  let K := sourcePeriodicGapRootSet hp hp1 φ.val ×ˢ {φ.val}
  have hq₀ : q₀ ∈ K :=
    ⟨sourcePsiGapRoot_filled_mem_periodicGapRootSet hp hp1 φ n,rfl⟩
  have hq : q ∈ cthickening δ K :=
    mem_cthickening_of_dist_le q q₀ δ K hq₀ hnear.le
  have hQ := hquot q hq m
  have hmid k : ‖sourceStandardRootMidpoint hp hp1 ψ k-(Real.pi : ℂ)*k‖ ≤ D := by
    have h := (lp.norm_apply_le_norm (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
      (sourcePeriodicMidpointDisplacement hp hp1 ψ) k).trans (hmiddata ψ hψ.2).1
    simpa only [sourcePeriodicMidpointDisplacement_apply,sourceStandardRootMidpoint] using h
  have hdisc k : sourceStandardRootMidpoint hp hp1 ψ k ∈
      sourceIsolatingDisc hp hp1 φ.val (A.cutoff φ) (A.enlargement φ) k :=
    sourcePeriodicSegment_subset_isolatingDisc hp hp1 φ.val ψ (A.cutoff φ) (A.enlargement φ) k
      (A.clusters φ ψ hψS k) (sourcePeriodicMidpoint_mem_segment hp hp1 ψ k)
  have hne : sourceStandardRootMidpoint hp hp1 ψ n ≠
      sourceStandardRootMidpoint hp hp1 ψ m := by
    intro heq
    have hn := hdisc n
    rw [heq] at hn
    exact Set.disjoint_left.mp (A.disjoint φ m n hmn) (hdisc m) hn
  exact sourcePsiMidpointFilledRegularFactor_midpoint_lowerBound_of_quotient
    hp hp1 n m hmn (B.branch n ψ) ψ D c hD hc (hmid n) (hmid m) hne hQ

end NLS.ZakharovShabat
