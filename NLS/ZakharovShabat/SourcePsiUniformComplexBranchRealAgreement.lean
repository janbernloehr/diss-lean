import NLS.ZakharovShabat.SourcePsiUniformComplexBranches
import NLS.ComplexAnalysis.ConvexRealAnalyticIdentity

/-!
# Real agreement of the uniform complex psi branches

Continuity and local uniqueness first identify each complex branch
with the canonical real roots as a germ. Real analytic continuation
on the convex real source ball extends this agreement throughout the
same source ball, whose radius is independent of the deleted index.
-/

noncomputable section
open Set Filter Topology Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat.SourcePsiUniformComplexBranchFamily
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
  {φ : realTypeSourceLocus p} {D : SourcePsiUniformEquationTube hp hp1 φ}

theorem eventually_eq_sourcePsiGapRoot (S : SourcePsiUniformComplexBranchFamily D) (n : ℤ) :
    (fun χ : realTypeSourceSubmodule p => S.branch n χ.val) =ᶠ[𝓝 (⟨φ.val,φ.property⟩ : realTypeSourceSubmodule p)]
      (fun χ => sourcePsiGapRoot hp hp1 n χ) := by
  let φr : realTypeSourceSubmodule p := ⟨φ.val,φ.property⟩
  have hcont : ContinuousAt (fun χ : realTypeSourceSubmodule p => sourcePsiGapRoot hp hp1 n χ) φr :=
    (analyticAt_sourcePsiGapRoot_real hp hp1 n φr).continuousAt
  have hroot : ∀ᶠ χ : realTypeSourceSubmodule p in 𝓝 φr,
      sourcePsiGapRoot hp hp1 n χ ∈ ball (sourcePsiGapRoot hp hp1 n φ) S.rootRadius :=
    hcont.eventually (ball_mem_nhds _ S.rootRadius_pos)
  have hval : Tendsto (fun χ : realTypeSourceSubmodule p => χ.val) (𝓝 φr) (𝓝 φ.val) :=
    continuous_subtype_val.continuousAt.tendsto
  have hsource : ∀ᶠ χ : realTypeSourceSubmodule p in 𝓝 φr, χ.val ∈ ball φ.val S.sourceRadius :=
    hval.eventually (ball_mem_nhds _ S.sourceRadius_pos)
  filter_upwards [hroot,hsource] with χ hχroot hχsource
  have hq : (sourcePsiGapRoot hp hp1 n χ,χ.val) ∈
      ball (sourcePsiGapRoot hp hp1 n φ,φ.val) S.rootRadius := by
    rw [mem_ball,Prod.dist_eq]
    exact max_lt_iff.mpr ⟨mem_ball.mp hχroot,
      (mem_ball.mp hχsource).trans_le S.sourceRadius_le_rootRadius⟩
  have houter : (sourcePsiGapRoot hp hp1 n χ,χ.val) ∈
      ball (sourcePsiGapRoot hp hp1 n φ,φ.val) (4*D.radius) :=
    (ball_subset_ball (by linarith [S.rootRadius_lt,D.radius_pos])) hq
  obtain ⟨c,R,hfamily,hcoord⟩ := D.contours n (sourcePsiGapRoot hp hp1 n χ,χ.val) houter
  have hzero : D.equation n (sourcePsiGapRoot hp hp1 n χ,χ.val) = 0 :=
    sourcePsiEquationRealization_zero_of_gapSolution hp hp1 n χ.val χ.property
      (sourcePsiGapRoot hp hp1 n χ) _ c R hfamily hcoord (sourcePsiGapRoot_solution hp hp1 n χ)
  exact (S.unique n χ.val hχsource (sourcePsiGapRoot hp hp1 n χ) hχroot hzero).symm

/-- Every real source in the full common source ball has precisely
its canonical gap roots on the complex branch. -/
theorem eq_sourcePsiGapRoot_of_real (S : SourcePsiUniformComplexBranchFamily D) (n : ℤ)
    (χ : realTypeSourceLocus p) (hχ : χ.val ∈ ball φ.val S.sourceRadius) :
    S.branch n χ.val = sourcePsiGapRoot hp hp1 n χ := by
  let φr : realTypeSourceSubmodule p := ⟨φ.val,φ.property⟩
  let χr : realTypeSourceSubmodule p := ⟨χ.val,χ.property⟩
  let U : Set (realTypeSourceSubmodule p) := ball φr S.sourceRadius
  have hsource (ψ : realTypeSourceSubmodule p) (hψ : ψ ∈ U) : ψ.val ∈ ball φ.val S.sourceRadius := hψ
  have hs : AnalyticOnNhd ℝ (fun ψ : realTypeSourceSubmodule p => S.branch n ψ.val) U := by
    intro ψ hψ
    exact ((S.analytic n ψ.val (hsource ψ hψ)).restrictScalars (𝕜 := ℝ)).comp
      ((realTypeSourceSubmodule p).subtypeL.analyticAt ψ)
  have hr : AnalyticOnNhd ℝ (fun ψ : realTypeSourceSubmodule p => sourcePsiGapRoot hp hp1 n ψ) U :=
    fun ψ _ => analyticAt_sourcePsiGapRoot_real hp hp1 n ψ
  have heq := NLS.ComplexAnalysis.AnalyticOnNhd.eqOn_of_convex_of_eventuallyEq
    (fun ψ : realTypeSourceSubmodule p => S.branch n ψ.val)
    (fun ψ => sourcePsiGapRoot hp hp1 n ψ) U isOpen_ball (convex_ball _ _)
    hs hr φr (mem_ball_self S.sourceRadius_pos) (S.eventually_eq_sourcePsiGapRoot n)
  exact heq (x := χr) hχ

end NLS.ZakharovShabat.SourcePsiUniformComplexBranchFamily
