import NLS.ComplexAnalysis.PrescribedAnalyticSquareRoot

/-! # Local analytic square roots with a prescribed value

An analytic radicand with a nonzero prescribed root admits an analytic
root on an open neighborhood. No continuous labeling of its roots is
needed, and the prescribed value may lie on the principal branch cut.
-/

noncomputable section
open Set Complex Filter Topology
namespace NLS.ComplexAnalysis
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem exists_local_analytic_squareRoot
    (f : E → ℂ) (a : E) (w : ℂ) (hf : AnalyticAt ℂ f a)
    (hw : w ≠ 0) (hbase : f a = w ^ 2) :
    ∃ V : Set E, IsOpen V ∧ a ∈ V ∧ ∃ r : E → ℂ,
      AnalyticOnNhd ℂ r V ∧ r a = w ∧ ∀ b ∈ V, r b ≠ 0 ∧ r b ^ 2 = f b := by
  let q : E → ℂ := fun b => f b / w ^ 2
  let r := prescribedSquareRoot f w
  have hq : AnalyticAt ℂ q a := hf.div_const
  have hqa : q a = 1 := by simp only [q,hbase,div_self (pow_ne_zero 2 hw)]
  have hs : AnalyticAt ℂ Complex.sqrt (q a) := by
    rw [hqa]
    exact Complex.differentiableOn_sqrt.analyticAt
      (Complex.isOpen_slitPlane.mem_nhds (by simp [Complex.mem_slitPlane_iff]))
  have hr : AnalyticAt ℂ r a := analyticAt_const.mul (hs.comp (f := q) hq)
  have hra : r a = w := prescribedSquareRoot_base f w hw a hbase
  have hgood : ∀ᶠ b in 𝓝 a, AnalyticAt ℂ r b ∧ r b ≠ 0 :=
    hr.eventually_analyticAt.and (hr.continuousAt.eventually_ne (hra ▸ hw))
  obtain ⟨V,hVsub,hV,haV⟩ := _root_.mem_nhds_iff.mp hgood
  exact ⟨V,hV,haV,r,(fun b hb => (hVsub hb).1),hra,
    fun b hb => ⟨(hVsub hb).2,prescribedSquareRoot_sq f w hw b⟩⟩

end NLS.ComplexAnalysis
