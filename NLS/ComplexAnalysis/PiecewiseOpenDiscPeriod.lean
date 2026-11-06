import NLS.ComplexAnalysis.PiecewiseContourPeriod
import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas

/-! # Reference-contour periods on an open cut disc

The finite trace of each actual loop is compact. A smaller closed disc
therefore contains the cut and both contours, and the proved closed-disc
period formula applies without analyticity at the original outer boundary.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
namespace NLS.ComplexAnalysis
namespace PiecewiseC1Loop

def trace (Γ : PiecewiseC1Loop) : Set ℂ := ⋃ i : Fin Γ.count, range (Γ.edge i)

theorem isCompact_trace (Γ : PiecewiseC1Loop) : IsCompact Γ.trace :=
  isCompact_iUnion (fun i => isCompact_range (Γ.edge i).continuous)

theorem inside_iff_trace_subset (Γ : PiecewiseC1Loop) (D : Set ℂ) :
    Γ.Inside D ↔ Γ.trace ⊆ D := by
  simp only [Inside,trace,iUnion_subset_iff,range_subset_iff]

theorem integral_eq_reference_mul_winding_of_open_disc_cut
    (Γ Γ₀ : PiecewiseC1Loop) (f : ℂ → ℂ) (d c : ℂ) (R : ℝ)
    (K : Set ℂ) (hKclosed : IsClosed K) (hc : c ∈ K)
    (hKstar : StarConvex ℝ c K) (hK : K ⊆ ball d R)
    (hf : AnalyticOnNhd ℂ f (ball d R \ K))
    (hΓ : Γ.Inside (ball d R \ K)) (hΓ₀ : Γ₀.Inside (ball d R \ K))
    (hw : Γ₀.windingIntegral c = 1) :
    Γ.integral f = Γ₀.integral f*Γ.windingIntegral c := by
  have hR : 0 < R := dist_nonneg.trans_lt (mem_ball.mp (hK hc))
  have hclosed : IsClosed (K ∪ Γ.trace ∪ Γ₀.trace) :=
    (hKclosed.union Γ.isCompact_trace.isClosed).union Γ₀.isCompact_trace.isClosed
  have hsub : K ∪ Γ.trace ∪ Γ₀.trace ⊆ ball d R := by
    intro z hz
    rcases hz with (hz | hz) | hz
    · exact hK hz
    · exact ((Γ.inside_iff_trace_subset _).mp hΓ hz).1
    · exact ((Γ₀.inside_iff_trace_subset _).mp hΓ₀ hz).1
  obtain ⟨T,hT,hall⟩ := exists_pos_lt_subset_ball hR hclosed hsub
  have hKT : K ⊆ ball d T := fun _ hz => hall (Or.inl (Or.inl hz))
  obtain ⟨s,hs,hKs⟩ := exists_pos_lt_subset_ball hT.1 hKclosed hKT
  have hfT : AnalyticOnNhd ℂ f (closedBall d T \ K) :=
    hf.mono (fun _ hz => ⟨closedBall_subset_ball hT.2 hz.1,hz.2⟩)
  have hΓT : Γ.Inside (ball d T \ K) := by
    intro i t
    refine ⟨hall (Or.inl (Or.inr ?_)),(hΓ i t).2⟩
    exact mem_iUnion.mpr ⟨i,mem_range_self t⟩
  have hΓ₀T : Γ₀.Inside (ball d T \ K) := by
    intro i t
    refine ⟨hall (Or.inr ?_),(hΓ₀ i t).2⟩
    exact mem_iUnion.mpr ⟨i,mem_range_self t⟩
  have heΓ := Γ.integral_eq_circleIntegral_mul_winding_of_starConvex_cut f d c s T
    hs.1 hs.2 K hKclosed hc hKstar hKs hfT hΓT
  have heΓ₀ := Γ₀.integral_eq_circleIntegral_mul_winding_of_starConvex_cut f d c s T
    hs.1 hs.2 K hKclosed hc hKstar hKs hfT hΓ₀T
  rw [hw,mul_one] at heΓ₀
  rw [heΓ,heΓ₀]

end PiecewiseC1Loop
end NLS.ComplexAnalysis
