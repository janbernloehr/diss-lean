import NLS.ZakharovShabat.SourceRealActionLocalAgreement

/-!
# Line analyticity and real sign of the local action extension

The fixed-circle extension is complex differentiable on an open
Banach-source neighborhood. Every affine complex line through a point
of that neighborhood therefore sees an analytic one-variable action.
On the real-type locus, the same extension is nonnegative and detects
exactly the collapsed periodic gaps.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The local extension is analytic along every complex affine line
through every point of its source neighborhood. On real-type sources
it equals the indexed action and inherits its sign and zero criterion. -/
theorem exists_local_lineAnalytic_extension_of_sourceRealAction
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ))
    (n : ℤ) :
    ∃ c : ℂ, ∃ R : ℝ, 0 < R ∧
      ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
        (∀ ψ ∈ V, ∀ h : CoeffPair p,
          AnalyticAt ℂ (fun t : ℂ =>
            sourceActionCircle hp hp1 (ψ+t•h) c R) 0) ∧
        (∀ ψ ∈ V, ∀ hψ : IsRealType (CoeffPair.toMax p ψ),
          sourceRealAction hp hp1 ψ hψ n =
            sourceActionCircle hp hp1 ψ c R ∧
          0 ≤ (sourceActionCircle hp hp1 ψ c R).re ∧
          (sourceActionCircle hp hp1 ψ c R).im = 0 ∧
          (sourceActionCircle hp hp1 ψ c R = 0 ↔
            sourcePeriodicGapDisplacement hp hp1 ψ n = 0)) := by
  obtain ⟨c,R,hR,V,hVopen,hφV,_,hdiff,hagree⟩ :=
    exists_local_differentiable_extension_of_sourceRealAction
      hp hp1 φ hreal n
  refine ⟨c,R,hR,V,hVopen,hφV,?_,?_⟩
  · intro ψ hψ h
    let a : ℂ → CoeffPair p := fun t => ψ+t•h
    have ha : Differentiable ℂ a := by
      dsimp [a]
      fun_prop
    let U : Set ℂ := a ⁻¹' V
    have hUopen : IsOpen U := hVopen.preimage ha.continuous
    have h0 : (0:ℂ) ∈ U := by simpa [U,a] using hψ
    have hline : DifferentiableOn ℂ
        (fun t : ℂ => sourceActionCircle hp hp1 (a t) c R) U := by
      intro t ht
      exact (((hdiff (a t) ht).differentiableAt
        (hVopen.mem_nhds ht)).comp t (ha t)).differentiableWithinAt
    exact hline.analyticAt (hUopen.mem_nhds h0)
  · intro ψ hψ hψreal
    have heq := hagree ψ hψ hψreal
    obtain ⟨hnonneg,him,hzero⟩ :=
      sourceRealAction_nonneg_and_eq_zero_iff_gap_zero hp hp1 ψ hψreal n
    rw [heq] at hnonneg him hzero
    exact ⟨heq,hnonneg,him,hzero⟩

end NLS.ZakharovShabat
