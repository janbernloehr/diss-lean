import NLS.ZakharovShabat.SourcePsiMidpointQuotientFiniteHeadLowerBound
import NLS.ZakharovShabat.SourcePsiUniformFilledBranchStability
import NLS.ZakharovShabat.SourcePsiMidpointDenominator
import NLS.ZakharovShabat.SourcePsiQuadraticRootOffset
import NLS.ZakharovShabat.SourcePsiIsolatingComplexRootAtlas

/-!
# Uniform finite-head midpoint lower bounds for the actual chi factors

The ratio pi(n-m)/(tau_n-tau_m) has a positive lower bound from
the common midpoint displacement norm. A compact-gap-product lower
bound for the regular quotient therefore gives a chi midpoint lower
bound on any finite selected head. Uniform stability places every
actual filled analytic branch in the same compact neighborhood, and
assigned-disc isolation separates the two moving midpoints.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The common midpoint displacement bound controls the index ratio
from below, so a positive quotient bound gives a positive chi bound. -/
theorem sourcePsiMidpointFilledRegularFactor_midpoint_lowerBound_of_quotient
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n m : ℤ) (hmn : m ≠ n)
    (a : DeletedCoeff p n) (ψ : CoeffPair p) (D c : ℝ) (hD : 0 ≤ D) (hc : 0 < c)
    (hmidn : ‖sourceStandardRootMidpoint hp hp1 ψ n-(Real.pi : ℂ)*n‖ ≤ D)
    (hmidm : ‖sourceStandardRootMidpoint hp hp1 ψ m-(Real.pi : ℂ)*m‖ ≤ D)
    (hne : sourceStandardRootMidpoint hp hp1 ψ n ≠ sourceStandardRootMidpoint hp hp1 ψ m)
    (hquot : c ≤ ‖sourceSingleRootQuotientJointProduct hp hp1 m
      (sourceStandardRootMidpoint hp hp1 ψ m,
        (sourcePsiFillDeletedRoot n a (sourceStandardRootMidpoint hp hp1 ψ n),ψ))‖) :
    (Real.pi/(Real.pi+2*D))*c ≤ ‖sourcePsiMidpointFilledRegularFactor hp hp1 n m a ψ
      (sourceStandardRootMidpoint hp hp1 ψ m)‖ := by
  let τn := sourceStandardRootMidpoint hp hp1 ψ n
  let τm := sourceStandardRootMidpoint hp hp1 ψ m
  let Q := sourceSingleRootQuotientJointProduct hp hp1 m
    (τm,(sourcePsiFillDeletedRoot n a τn,ψ))
  let d : ℝ := |((n-m : ℤ) : ℝ)|
  have hd : 1 ≤ d := by
    dsimp only [d]
    exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hmn.symm)
  have hden : 0 < ‖τn-τm‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have hP : 0 < Real.pi+2*D := by linarith [Real.pi_pos]
  have hdenle : ‖τn-τm‖ ≤ (Real.pi+2*D)*d := by
    have heq : τn-τm = (τn-(Real.pi : ℂ)*n)+
        ((Real.pi : ℂ)*n-(Real.pi : ℂ)*m)+((Real.pi : ℂ)*m-τm) := by ring
    have hlast : ‖(Real.pi : ℂ)*m-τm‖ ≤ D := by simpa only [norm_sub_rev] using hmidm
    have htri : ‖τn-τm‖ ≤ D+Real.pi*d+D := by
      rw [heq]
      exact ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)).trans
        (add_le_add (add_le_add hmidn (norm_free_center_sub n m).le) hlast)
    nlinarith [mul_nonneg hD (sub_nonneg.mpr hd)]
  have hnorm : ‖sourcePsiMidpointFilledRegularFactor hp hp1 n m a ψ τm‖ =
      Real.pi*d*‖Q‖/‖τn-τm‖ := by
    simp only [sourcePsiMidpointFilledRegularFactor,sourcePsiGapRegularFactor,
      displacedRoots_sourcePsiFillDeletedRoot_same,norm_mul,norm_div,norm_I,one_mul,
      Complex.norm_real,Real.norm_of_nonneg Real.pi_pos.le,Complex.norm_intCast]
    dsimp only [Q,τn,τm,d]
    ring
  rw [hnorm]
  apply (le_div_iff₀ hden).mpr
  calc
    (Real.pi/(Real.pi+2*D)*c)*‖τn-τm‖ ≤
        (Real.pi/(Real.pi+2*D)*c)*((Real.pi+2*D)*d) :=
      mul_le_mul_of_nonneg_left hdenle (by positivity)
    _ = Real.pi*d*c := by field_simp [hP.ne']
    _ ≤ Real.pi*d*‖Q‖ := mul_le_mul_of_nonneg_left hquot (by positivity)

/-- Every fixed finite selected head has a common positive chi
midpoint bound near a real source, uniformly over all omitted indices
of the actual analytic branch family, including collapsed gaps. -/
theorem SourcePsiIsolatingComplexRootAtlas.exists_local_finiteHead_midpoint_factor_lowerBound
    {hp : p ≠ ⊤} {hp1 : 1 < p} {U : Set (CoeffPair p)}
    (A : SourcePsiIsolatingComplexRootAtlas hp hp1 U) (φ : realTypeSourceLocus p) (s : Finset ℤ) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ.val ∈ V ∧ V ⊆ A.toSourcePsiComplexRootAtlas.sourceBall φ ∧
      ∃ C : ℝ, 0 < C ∧ ∀ ψ ∈ V, ∀ n : ℤ, ∀ m ∈ s, m ≠ n →
        C ≤ ‖sourcePsiMidpointFilledRegularFactor hp hp1 n m
          (A.toSourcePsiComplexRootAtlas.branch n ψ) ψ (sourceStandardRootMidpoint hp hp1 ψ m)‖ := by
  let B := A.toSourcePsiComplexRootAtlas
  let S := B.localBranch φ
  obtain ⟨δ,c,hδ,hc,hquot⟩ :=
    exists_sourcePsi_midpointQuotient_finiteHead_lowerBound_near_gapProduct hp hp1 φ s
  obtain ⟨r,hr,hrS,hgraph⟩ := S.exists_uniform_midpointFilled_graph_radius δ hδ
  obtain ⟨Vm,hVm,hφVm,D,hD,_,hmiddata⟩ :=
    exists_local_sourcePeriodicMidpoint_tail_lattice_separation hp hp1 φ.val
  let V := ball φ.val r ∩ Vm
  let C := (Real.pi/(Real.pi+2*D))*c
  have hC : 0 < C := by dsimp only [C]; exact mul_pos (div_pos Real.pi_pos (by linarith [Real.pi_pos])) hc
  refine ⟨V,isOpen_ball.inter hVm,⟨mem_ball_self hr,hφVm⟩,
    (fun ψ hψ => ball_subset_ball hrS hψ.1),C,hC,?_⟩
  intro ψ hψ n m hm hmn
  have hψS : ψ ∈ B.sourceBall φ := ball_subset_ball hrS hψ.1
  have hnear := hgraph ψ hψ.1 n
  rw [← B.eq_local n φ hψS] at hnear
  let q := (sourcePsiFillDeletedRoot n (B.branch n ψ) (sourceStandardRootMidpoint hp hp1 ψ n),ψ)
  let q₀ := (sourcePsiFillDeletedRoot n (sourcePsiGapRoot hp hp1 n φ)
    (sourceStandardRootMidpoint hp hp1 φ.val n),φ.val)
  let K := sourcePeriodicGapRootSet hp hp1 φ.val ×ˢ {φ.val}
  have hq₀ : q₀ ∈ K := ⟨sourcePsiGapRoot_filled_mem_periodicGapRootSet hp hp1 φ n,rfl⟩
  have hq : q ∈ cthickening δ K := mem_cthickening_of_dist_le q q₀ δ K hq₀ hnear.le
  have hQ := hquot q hq m hm
  have hmid k : ‖sourceStandardRootMidpoint hp hp1 ψ k-(Real.pi : ℂ)*k‖ ≤ D := by
    have h := (lp.norm_apply_le_norm (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
      (sourcePeriodicMidpointDisplacement hp hp1 ψ) k).trans (hmiddata ψ hψ.2).1
    simpa only [sourcePeriodicMidpointDisplacement_apply,sourceStandardRootMidpoint] using h
  have hdisc k : sourceStandardRootMidpoint hp hp1 ψ k ∈
      sourceIsolatingDisc hp hp1 φ.val (A.cutoff φ) (A.enlargement φ) k :=
    sourcePeriodicSegment_subset_isolatingDisc hp hp1 φ.val ψ (A.cutoff φ) (A.enlargement φ) k
      (A.clusters φ ψ hψS k) (sourcePeriodicMidpoint_mem_segment hp hp1 ψ k)
  have hne : sourceStandardRootMidpoint hp hp1 ψ n ≠ sourceStandardRootMidpoint hp hp1 ψ m := by
    intro heq
    have hn := hdisc n
    rw [heq] at hn
    exact Set.disjoint_left.mp (A.disjoint φ m n hmn) (hdisc m) hn
  exact sourcePsiMidpointFilledRegularFactor_midpoint_lowerBound_of_quotient
    hp hp1 n m hmn (B.branch n ψ) ψ D c hD hc (hmid n) (hmid m) hne hQ

end NLS.ZakharovShabat
