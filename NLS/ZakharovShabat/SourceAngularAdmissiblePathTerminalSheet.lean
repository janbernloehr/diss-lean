import NLS.ZakharovShabat.SourceAngularAdmissiblePathRoot

/-!
# The local terminal chart of a continued admissible root

A continuous root along a path agrees near a regular terminal with any
analytic root chart having the same terminal value. Only a neighborhood
of the terminal is used; the rest of the path can leave that chart.
-/

noncomputable section
open Set Filter Topology Metric Complex NLS.ComplexAnalysis
open scoped ENNReal unitInterval
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceAngularAdmissiblePathRootData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {n : ℤ} {ψ : CoeffPair p}
  {c : ℂ} {R : ℝ} {Q : ℂ × CoeffPair p → ℂ} {a b : ℂ} {γ : Path a b}

/-- Clamping preserves the square identity outside the unit interval. -/
theorem square_root_extend
    (hQ : SourceAngularAdmissiblePathRootData hp hp1 n ψ c R Q γ) (t : ℝ) :
    Q (γ.extend t,ψ)^2 = sourceAngularRadicand hp (γ.extend t,ψ) := by
  let u : I := projIcc 0 1 zero_le_one t
  have h := hQ.square_root (u : ℝ) u.property
  rw [Path.extend_apply γ u.property] at h
  exact h

/-- The continued root agrees locally with its regular terminal sheet,
without requiring that sheet to contain the entire path. -/
theorem eventuallyEq_terminal_sheet
    (hQ : SourceAngularAdmissiblePathRootData hp hp1 n ψ c R Q γ)
    (w : ℂ) (hw : w ≠ 0)
    (hb : (b,ψ) ∈ sourceAngularRootSheetDomain hp w)
    (heq : Q (b,ψ) = sourceAngularRootSheet hp w (b,ψ)) :
    (fun t : ℝ => Q (γ.extend t,ψ)) =ᶠ[𝓝 (1:ℝ)]
      (fun t : ℝ => sourceAngularRootSheet hp w (γ.extend t,ψ)) := by
  have hsheet : ContinuousAt (fun t : ℝ => sourceAngularRootSheet hp w (γ.extend t,ψ)) 1 := by
    have hgraph : ContinuousAt (fun t : ℝ => (γ.extend t,ψ)) 1 :=
      (γ.continuous_extend.continuousAt (x := (1:ℝ))).prodMk continuousAt_const
    have hroot : ContinuousAt (sourceAngularRootSheet hp w) (γ.extend 1,ψ) := by
      simpa only [Path.extend_one] using
        (analyticOnNhd_sourceAngularRootSheet hp hp1 w (b,ψ) hb).continuousAt
    exact hroot.comp (f := fun t : ℝ => (γ.extend t,ψ)) hgraph
  apply eventuallyEq_of_sq_eq_of_continuousAt _ _ (1:ℝ) hQ.continuous_root.continuousAt hsheet
  · simpa only [Path.extend_one] using heq
  · simpa only [Path.extend_one] using sourceAngularRootSheet_ne_zero hp w hw (b,ψ) hb
  · exact Eventually.of_forall fun t => (hQ.square_root_extend t).trans
      (sourceAngularRootSheet_sq hp w hw (γ.extend t,ψ)).symm

end SourceAngularAdmissiblePathRootData
end NLS.ZakharovShabat
