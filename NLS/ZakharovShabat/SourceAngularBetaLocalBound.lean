import NLS.ZakharovShabat.SourceAngularBetaBound
import NLS.ComplexAnalysis.CompactParameterBounds

/-!
# Local gap-weighted estimates for every actual beta chart

Joint analyticity on the annulus and compactness of an enclosing circle
supply the numerator bound in `SourceAngularBetaBound`. The resulting
estimate holds locally at every complex source of the chart, including
at zero gaps and endpoint terminals. Its constant can depend on both
indices; the index-uniform estimate of Theorem 13.1(i) remains separate.
-/

noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceAngularJointAnnulusChartData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {m : ℤ}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}
  {W V : Set (CoeffPair p)} {c : ℤ → ℂ} {T : ℤ → ℝ} {r R : ℝ} {z₀ : ℂ}

/-- Multiplying the actual integrand by its selected root recovers the
jointly analytic gap numerator on the open annulus. -/
theorem analyticOnNhd_gapNumerator_annulus
    (D : SourceAngularJointAnnulusChartData hp hp1 m s W V c T r R z₀) (n : ℤ) :
    AnalyticOnNhd ℂ (fun x : ℂ × CoeffPair p => sourceAngularGapNumerator hp hp1 n m s x.2 x.1)
      ((ball (c m) R \ closedBall (c m) r) ×ˢ V) := by
  let A := (ball (c m) R \ closedBall (c m) r) ×ˢ V
  have hA : IsOpen A := (isOpen_ball.sdiff isClosed_closedBall).prod D.source_open
  have hsub : A ⊆ (closedBall (c m) R \ ball (c m) r) ×ˢ V := by
    intro x hx
    exact ⟨⟨ball_subset_closedBall hx.1.1,fun h => hx.1.2 (ball_subset_closedBall h)⟩,hx.2⟩
  intro x hx
  have hf := ((D.integrand_analytic n x (hsub hx)).mul (D.selected_root_analytic x (hsub hx)))
  apply hf.congr
  filter_upwards [hA.mem_nhds hx] with y hy
  change sourceAngularIntegrand n s (sourceCanonicalRootJointProduct hp hp1) (y.1,y.2) *
    sourceStandardRoot hp hp1 y.2 m y.1 = sourceAngularGapNumerator hp hp1 n m s y.2 y.1
  change sourceAngularIntegrand n s (fun t => sourceCanonicalRoot hp hp1 t.2 t.1) (y.1,y.2) *
    sourceStandardRoot hp hp1 y.2 m y.1 = sourceAngularGapNumerator hp hp1 n m s y.2 y.1
  rw [sourceAngularIntegrand_eq_gapNumerator_div_standardRoot hp hp1 n m s y.2 y.1]
  exact div_mul_cancel₀ _ (sourceStandardRoot_ne_zero_off_segment hp hp1 y.2 m y.1
    (fun h => hy.1.2 (ball_subset_closedBall (D.gap_enclosed y.2 hy.2 h))))

/-- At every source in the chart, an actual numerator has one circle
bound on an open source neighborhood. -/
theorem exists_local_gapNumerator_circle_bound
    (D : SourceAngularJointAnnulusChartData hp hp1 m s W V c T r R z₀)
    (φ : CoeffPair p) (hφ : φ ∈ V) (n : ℤ)
    (ρ : ℝ) (hrρ : r < ρ) (hρR : ρ < R) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ φ ∈ U ∧ U ⊆ V ∧
      ∃ M : ℝ, 0 < M ∧ ∀ ψ ∈ U, ∀ w ∈ sphere (c m) ρ,
        ‖sourceAngularGapNumerator hp hp1 n m s ψ w‖ ≤ M := by
  let A := (ball (c m) R \ closedBall (c m) r) ×ˢ V
  have hA : IsOpen A := (isOpen_ball.sdiff isClosed_closedBall).prod D.source_open
  have hbase (w : ℂ) (hw : w ∈ sphere (c m) ρ) : (w,φ) ∈ A := by
    have hd := mem_sphere.mp hw
    exact ⟨⟨mem_ball.mpr (hd.trans_lt hρR),
      fun h => (not_le_of_gt hrρ) (hd ▸ mem_closedBall.mp h)⟩,hφ⟩
  obtain ⟨U,hU,hφU,B,hB,hbound⟩ := exists_local_uniform_bound_on_compact_of_continuousOn
    (fun x : ℂ × CoeffPair p => sourceAngularGapNumerator hp hp1 n m s x.2 x.1)
    A hA (D.analyticOnNhd_gapNumerator_annulus n).continuousOn
    (sphere (c m) ρ) (isCompact_sphere _ _) φ hbase
  exact ⟨U ∩ V,hU.inter D.source_open,⟨hφU,hφ⟩,inter_subset_right,B+1,by linarith,
    fun ψ hψ w hw => (hbound ψ hψ.1 w hw).2.trans (by linarith)⟩

/-- A genuine local estimate with the vanishing gap weight. The source
neighborhood and constant may depend on the off-diagonal pair. -/
theorem exists_local_norm_beta_le_gap_weight
    (D : SourceAngularJointAnnulusChartData hp hp1 m s W V c T r R z₀)
    (φ : CoeffPair p) (hφ : φ ∈ V) (n : ℤ) (hmn : m ≠ n) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ φ ∈ U ∧ U ⊆ V ∧
      ∃ C : ℝ, 0 < C ∧ ∀ ψ ∈ U,
        ‖sourceAngularBeta hp hp1 n m s ψ‖ ≤ C *
          (‖sourcePeriodicGapDisplacement hp hp1 ψ m‖ +
            ‖canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m-
              sourceStandardRootMidpoint hp hp1 ψ m‖) := by
  let ρ := (r+R)/2
  have hrρ : r < ρ := by dsimp only [ρ]; linarith [D.inner_lt_outer]
  have hρR : ρ < R := by dsimp only [ρ]; linarith [D.inner_lt_outer]
  obtain ⟨U,hU,hφU,hUV,M,hM,hbound⟩ := D.exists_local_gapNumerator_circle_bound φ hφ n ρ hrρ hρR
  let C := Real.pi*ρ^2*M/(ρ-r)^3
  have hC : 0 < C := by
    have hρ := D.inner_pos.trans hrρ
    have hd := sub_pos.mpr hrρ
    dsimp only [C]
    positivity
  refine ⟨U,hU,hφU,hUV,C,hC,?_⟩
  intro ψ hψ
  have h := D.norm_beta_le_of_gapNumerator_bound ψ (hUV hψ) n hmn ρ M hrρ hρR hM.le (hbound ψ hψ)
  have hweight :
      ‖canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m-sourceStandardRootMidpoint hp hp1 ψ m‖ +
        ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖/2 ≤
      ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖ +
        ‖canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m-sourceStandardRootMidpoint hp hp1 ψ m‖ := by
    nlinarith [norm_nonneg (sourcePeriodicGapDisplacement hp hp1 ψ m)]
  exact h.trans (by simpa only [C,mul_comm] using mul_le_mul_of_nonneg_right hweight hC.le)

end SourceAngularJointAnnulusChartData
end NLS.ZakharovShabat
