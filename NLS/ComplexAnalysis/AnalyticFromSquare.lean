import NLS.ComplexAnalysis.PrescribedAnalyticSquareRoot

/-! # Recovering a nonzero analytic root from its square

A continuous scalar function whose square is analytic is itself analytic
near every nonzero value. The prescribed root fixes its local sign.
-/

noncomputable section
open Set Complex Filter Topology
namespace NLS.ComplexAnalysis
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A continuous nonzero square root of an analytic scalar family is analytic. -/
theorem analyticAt_of_analyticAt_sq_of_continuousAt
    (f : E → ℂ) (x : E) (hf : ContinuousAt f x)
    (hsq : AnalyticAt ℂ (fun y => f y^2) x) (hne : f x ≠ 0) : AnalyticAt ℂ f x := by
  let q : E → ℂ := fun y => f y^2/(f x)^2
  let g := prescribedSquareRoot (fun y => f y^2) (f x)
  have hq : AnalyticAt ℂ q x := hsq.div analyticAt_const (pow_ne_zero 2 hne)
  have hqx : q x = 1 := by simp [q,pow_ne_zero 2 hne]
  have hroot : AnalyticAt ℂ Complex.sqrt (q x) := by
    rw [hqx]
    exact Complex.differentiableOn_sqrt.analyticAt
      (Complex.isOpen_slitPlane.mem_nhds (by simp [Complex.mem_slitPlane_iff]))
  have hg : AnalyticAt ℂ g x := analyticAt_const.mul (hroot.comp (f := q) hq)
  have hbase : g x = f x := prescribedSquareRoot_base _ _ hne x rfl
  have heq : g =ᶠ[𝓝 x] f := eventuallyEq_of_sq_eq_of_continuousAt g f x
    hg.continuousAt hf hbase hne (Filter.Eventually.of_forall fun y =>
      prescribedSquareRoot_sq _ _ hne y)
  exact hg.congr heq

end NLS.ComplexAnalysis
