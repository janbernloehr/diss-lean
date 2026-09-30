import NLS.ZakharovShabat.SourcePsiMidpointFilledFactorMajorant
import NLS.ZakharovShabat.SourcePsiComplexRootAtlas
import NLS.ZakharovShabat.SourcePsiGapProductCompact

/-!
# Chi error majorants for the actual analytic psi branches

Every real canonical root vector has a common norm bound from the
full gap product. The common root radius gives the same bound for all
local complex branches. Consequently the bounded-input chi estimate
applies to the actual glued analytic roots, on one neighborhood of
each real source and with a norm bound uniform in the deleted index.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Every real canonical deleted root vector is bounded by the same
left-endpoint and gap displacement norms, independently of its index. -/
theorem norm_sourcePsiGapRoot_le_gap_displacements
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceLocus p) (n : ℤ) :
    ‖sourcePsiGapRoot hp hp1 n φ‖ ≤
      ‖canonicalPeriodicLeftDisplacement hp hp1
        (periodOnePotential φ.val) (periodOnePotential_mem φ.val)‖+
      ‖sourcePeriodicGapDisplacement hp hp1 φ.val‖ := by
  let a := sourcePsiGapRoot hp hp1 n φ
  let b := sourcePsiFillDeletedRoot n a (sourceStandardRootMidpoint hp hp1 φ.val n)
  have hnorm : ‖(a : Coeff p)‖ ≤ ‖b‖ := by
    apply lp.norm_mono (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
    intro m
    by_cases hmn : m = n
    · subst m
      simp only [show (a : Coeff p) n = 0 from a.property,norm_zero]
      exact norm_nonneg _
    · rw [show b m = (a : Coeff p) m from sourcePsiFillDeletedRoot_apply_other n m hmn a _]
  exact hnorm.trans (norm_gapRoot_le_gap_displacements hp hp1 φ.val b
    (sourcePsiGapRoot_filled_mem_periodicGapRootSet hp hp1 φ n))

/-- The common complex root radius and gap-product bound control
every analytic branch norm on the same source ball. -/
theorem SourcePsiUniformComplexBranchFamily.norm_branch_le
    {hp : p ≠ ⊤} {hp1 : 1 < p} {φ : realTypeSourceLocus p}
    {D : SourcePsiUniformEquationTube hp hp1 φ}
    (S : SourcePsiUniformComplexBranchFamily D)
    (n : ℤ) (ψ : CoeffPair p) (hψ : ψ ∈ ball φ.val S.sourceRadius) :
    ‖S.branch n ψ‖ ≤ S.rootRadius+
      ‖canonicalPeriodicLeftDisplacement hp hp1
        (periodOnePotential φ.val) (periodOnePotential_mem φ.val)‖+
      ‖sourcePeriodicGapDisplacement hp hp1 φ.val‖ := by
  have hdist : ‖S.branch n ψ-sourcePsiGapRoot hp hp1 n φ‖ < S.rootRadius := by
    have h := mem_ball.mp (S.graph n ψ hψ)
    rw [Prod.dist_eq,max_lt_iff] at h
    simpa only [dist_eq_norm] using h.1
  have hbase := norm_sourcePsiGapRoot_le_gap_displacements hp hp1 φ n
  calc
    ‖S.branch n ψ‖ = ‖(S.branch n ψ-sourcePsiGapRoot hp hp1 n φ)+sourcePsiGapRoot hp hp1 n φ‖ :=
      by rw [sub_add_cancel]
    _ ≤ ‖S.branch n ψ-sourcePsiGapRoot hp hp1 n φ‖+‖sourcePsiGapRoot hp hp1 n φ‖ := norm_add_le _ _
    _ ≤ _ := by linarith

/-- The actual glued analytic root family satisfies (2.32) on one
neighborhood of each real source. Its tail cutoff and chi majorant
norm bound are independent of the deleted index. -/
theorem SourcePsiComplexRootAtlas.exists_local_midpointFilledRegularFactor_tailMajorant
    {hp : p ≠ ⊤} {hp1 : 1 < p} (A : SourcePsiComplexRootAtlas hp hp1)
    (φ : realTypeSourceLocus p) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ.val ∈ V ∧ V ⊆ A.sourceBall φ ∧
      ∃ K : ℕ, ∃ C : ℝ, 0 ≤ C ∧
        ∀ ψ ∈ V, ∀ n : ℤ,
          ∃ E : Coeff p, ‖E‖ ≤ C ∧
            ∀ m : ℤ, K ≤ m.natAbs → m ≠ n →
              ∀ z ∈ closedBall ((Real.pi : ℂ)*m) (Real.pi/8),
                ‖sourcePsiMidpointFilledRegularFactor hp hp1 n m (A.branch n ψ) ψ z-I‖ ≤ ‖E m‖ := by
  let S := A.localBranch φ
  let T := S.rootRadius+
    ‖canonicalPeriodicLeftDisplacement hp hp1
      (periodOnePotential φ.val) (periodOnePotential_mem φ.val)‖+
    ‖sourcePeriodicGapDisplacement hp hp1 φ.val‖
  have hT : 0 ≤ T := by
    have hroot := S.rootRadius_pos
    dsimp only [T]
    positivity
  obtain ⟨V,hV,hφV,K,C,hC,hmajor⟩ :=
    exists_local_sourcePsiMidpointFilledRegularFactor_uniformBoundedBallTailMajorant
      hp hp1 φ.val φ.property T hT
  refine ⟨V ∩ A.sourceBall φ,hV.inter isOpen_ball,
    ⟨hφV,mem_ball_self S.sourceRadius_pos⟩,inter_subset_right,K,C,hC,?_⟩
  intro ψ hψ n
  apply hmajor ψ hψ.1 n (A.branch n ψ)
  rw [A.eq_local n φ hψ.2]
  exact S.norm_branch_le n ψ hψ.2

end NLS.ZakharovShabat
