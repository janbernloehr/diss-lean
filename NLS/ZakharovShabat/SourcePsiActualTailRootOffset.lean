import NLS.ZakharovShabat.SourcePsiUniformMidpointLowerBound
import NLS.ZakharovShabat.SourcePsiBranchFactorMajorant
import NLS.ZakharovShabat.SourcePsiLocalAssignedContourZero
import NLS.ZakharovShabat.SourceNormalizedActionUniformTailCircles

/-!
# Actual psi squared-gap tail offsets with uniform lp majorants

The free-centered eighth-pi circles fit inside the assigned tail
discs. Nested-circle homotopy transfers the actual retained contour
zeros to those circles. Assigned root placement, tiny midpoint and
gap tails, joint quotient analyticity, chi majorants, and the positive
midpoint bound instantiate the quadratic offset estimate with one
lp majorant norm bound independent of the omitted index.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem SourcePsiIsolatingComplexRootAtlas.exists_local_tail_squared_offset_majorant
    {hp : p ≠ ⊤} {hp1 : 1 < p} {U : Set (CoeffPair p)}
    (A : SourcePsiIsolatingComplexRootAtlas hp hp1 U) (φ : realTypeSourceLocus p) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ.val ∈ V ∧
      V ⊆ A.toSourcePsiComplexRootAtlas.sourceBall φ ∧
      ∃ K : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ ψ ∈ V, ∀ n : ℤ,
        ∃ E : Coeff p, ‖E‖ ≤ C ∧ ∀ m : ℤ, K ≤ m.natAbs → m ≠ n →
          ‖displacedRoots (A.toSourcePsiComplexRootAtlas.branch n ψ : Coeff p) m-
            sourceStandardRootMidpoint hp hp1 ψ m‖ ≤
              ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖^2*‖E m‖ := by
  let B := A.toSourcePsiComplexRootAtlas
  obtain ⟨Vm,hVm,hφVm,hVmBall,Km,Cm,hCm,hmajor⟩ :=
    B.exists_local_midpointFilledRegularFactor_tailMajorant φ
  obtain ⟨Vl,hVl,hφVl,_,c₀,hc₀,hlower⟩ :=
    A.exists_local_uniform_midpoint_factor_lowerBound φ
  obtain ⟨Kt,Vt,hVt,hφVt,htiny⟩ :=
    exists_local_sourcePeriodicMidpointGap_tiny_tail hp hp1 φ.val
  obtain ⟨r,hr,_,hzeroAssigned⟩ := A.exists_local_assigned_contour_zero φ
  obtain ⟨W,hW,_,hreal,hQ⟩ := exists_global_source_analytic_singleRootQuotient hp hp1
  let V := Vm ∩ (Vl ∩ (Vt ∩ (ball φ.val r ∩ W)))
  let K := max Km (max Kt (A.cutoff φ+1))
  let D := 192/(Real.pi*c₀)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨V,hVm.inter (hVl.inter (hVt.inter (isOpen_ball.inter hW))),
    ⟨hφVm,hφVl,hφVt,mem_ball_self hr,hreal φ.property⟩,
    (fun ψ hψ => hVmBall hψ.1),K,D*Cm,mul_nonneg hD hCm,?_⟩
  intro ψ hψ n
  have hψBall : ψ ∈ B.sourceBall φ := hVmBall hψ.1
  obtain ⟨E,hE,hEpoint⟩ := hmajor ψ hψ.1 n
  let F : Coeff p := (D : ℂ) • E
  have hFnorm : ‖F‖ ≤ D*Cm := by
    simp only [F,norm_smul,Complex.norm_real,Real.norm_of_nonneg hD]
    exact mul_le_mul_of_nonneg_left hE hD
  have hFcoord m : ‖F m‖ = D*‖E m‖ := by
    simp only [F,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,norm_mul,
      Complex.norm_real,Real.norm_of_nonneg hD]
  refine ⟨F,hFnorm,?_⟩
  intro m hm hmn
  have hmKm : Km ≤ m.natAbs := by dsimp [K] at hm; omega
  have hmKt : Kt ≤ m.natAbs := by dsimp [K] at hm; omega
  have hmN : ¬m.natAbs ≤ A.cutoff φ := by dsimp [K] at hm; omega
  obtain ⟨hmid,hgap⟩ := htiny ψ hψ.2.2.1 m hmKt
  let c : ℂ := (Real.pi : ℂ)*m
  have hgapAll k : sourcePeriodicSegment hp hp1 ψ k ⊆
      sourceIsolatingDisc hp hp1 φ.val (A.cutoff φ) (A.enlargement φ) k :=
    sourcePeriodicSegment_subset_isolatingDisc hp hp1 φ.val ψ (A.cutoff φ) (A.enlargement φ) k
      (A.clusters φ ψ hψBall k)
  have hclosed : closedBall c (Real.pi/8) ⊆
      sourceIsolatingDisc hp hp1 φ.val (A.cutoff φ) (A.enlargement φ) m := by
    simp only [sourceIsolatingDisc,if_neg hmN,refinedResonantDisk]
    exact closedBall_subset_ball (by nlinarith [Real.pi_pos])
  have hdom : closedBall c (Real.pi/8) ⊆ sourceStandardRootOmittedDomain hp hp1 ψ m :=
    hclosed.trans (sourceIsolatingDisc_subset_omittedDomain hp hp1 φ.val ψ
      (A.cutoff φ) (A.enlargement φ) (A.clusters φ ψ hψBall) (A.disjoint φ) m)
  have hseg := sourcePeriodicSegment_subset_free_eighth_ball hp hp1 ψ m hmid hgap
  have hcircle : sphere c (Real.pi/8) ⊆ sourceCanonicalRootDomain hp hp1 ψ := by
    intro z hz k
    by_cases hkm : k = m
    · subst k
      intro hk
      exact (ne_of_lt (mem_ball.mp (hseg hk))) (mem_sphere.mp hz)
    · exact hdom (sphere_subset_closedBall hz) k hkm
  have hτn : sourceStandardRootMidpoint hp hp1 ψ n ∈
      sourceIsolatingDisc hp hp1 φ.val (A.cutoff φ) (A.enlargement φ) n :=
    hgapAll n (sourcePeriodicMidpoint_mem_segment hp hp1 ψ n)
  have havoid z (hz : z ∈ sphere c (Real.pi/8)) : z ≠ sourceStandardRootMidpoint hp hp1 ψ n := by
    intro heq
    have hin := hclosed (sphere_subset_closedBall hz)
    rw [heq] at hin
    exact Set.disjoint_left.mp (A.disjoint φ m n hmn) hin hτn
  have hf := analyticOnNhd_sourcePsiMidpointFilledRegularFactor hp hp1 φ.val
    (A.cutoff φ) (A.enlargement φ) n m (B.branch n ψ) ψ W hψ.2.2.2.2
    (hQ m).2 c (Real.pi/8) hdom hclosed hτn (A.disjoint φ m n hmn)
  have hfamily := sourcePsiAssignedCircleFamily hp hp1 φ.val ψ (A.cutoff φ) (A.enlargement φ)
    (A.enlargement_pos φ) hgapAll (A.disjoint φ)
  have houterSeg : sourcePeriodicSegment hp hp1 ψ m ⊆ ball c (Real.pi/4) := by
    simpa only [sourceIsolatingDisc,if_neg hmN,refinedResonantDisk] using hgapAll m
  have houterDom : closedBall c (Real.pi/4) ⊆ sourceStandardRootOmittedDomain hp hp1 ψ m := by
    simpa only [sourceIsolatingCenter,sourceIsolatingRadius,if_neg hmN] using (hfamily.2 m).2.2.1
  have hzero : sourcePsiContour hp hp1 n (B.branch n ψ : Coeff p) ψ c (Real.pi/8) = 0 := by
    rw [sourcePsiContour_eq_of_nested_enclosingCircles hp hp1 n m (B.branch n ψ : Coeff p) ψ
      c c (Real.pi/8) (Real.pi/4) (by positivity) (by positivity) hseg houterSeg
      (closedBall_subset_closedBall (by nlinarith [Real.pi_pos])) houterDom]
    simpa only [sourceIsolatingCenter,sourceIsolatingRadius,if_neg hmN] using
      hzeroAssigned ψ hψ.2.2.2.1 n m hmn
  have hroot : ‖displacedRoots (B.branch n ψ : Coeff p) m-c‖ ≤ Real.pi/4 := by
    have h := A.global_placement φ n ψ hψBall m hmn
    simp only [sourceIsolatingDisc,if_neg hmN,refinedResonantDisk,mem_ball,dist_eq_norm] at h
    exact h.le
  have h := norm_sourcePsi_midpointFilled_tail_offset_le hp hp1 n m hmn (B.branch n ψ) ψ
    hmid hgap hroot hcircle havoid hf hzero (‖E m‖) c₀ (norm_nonneg _) hc₀
    (hEpoint m hmKm hmn) (hlower ψ hψ.2.1 n m hmn)
  rw [hFcoord]
  convert h using 1
  dsimp only [D]
  ring

end NLS.ZakharovShabat
