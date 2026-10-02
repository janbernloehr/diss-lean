import NLS.ZakharovShabat.SourceAngularBetaBound
import NLS.ZakharovShabat.SourceAngularEtaRemainderGlobal

/-! # Quantitative bounds for the actual eta remainder

The diagonal model subtraction gives a zero-period primitive. Its
normalized Cauchy transform is controlled by the diagonal numerator
minus `i`, with constants depending only on enclosing chart radii.
The estimate includes collapsed gaps and endpoint terminals.
-/

noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceAngularJointAnnulusChartData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {m : ℤ}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}
  {W V : Set (CoeffPair p)} {c : ℤ → ℂ} {T : ℤ → ℝ} {r R : ℝ} {z₀ : ℂ}

/-- The normalized primitive estimate reduces the interior quotient to
a bound for the diagonal numerator minus `i` on a single fixed circle. -/
theorem norm_etaQuotientCauchyCandidate_le
    (D : SourceAngularJointAnnulusChartData hp hp1 m s W V c T r R z₀)
    (ψ : CoeffPair p) (hψ : ψ ∈ V)
    (ρ M : ℝ) (hrρ : r < ρ) (hρR : ρ < R) (hM : 0 ≤ M)
    (hg : ∀ w ∈ sphere (c m) ρ, ‖(sourceAngularGapNumerator hp hp1 m m s ψ w-I)‖ ≤ M)
    (z : ℂ) (hz : z ∈ closedBall (c m) r) :
    ‖sourceAngularEtaQuotientCauchyCandidate hp hp1 m s (c m) r R z₀ ρ (z,ψ)‖ ≤
      Real.pi*ρ^2*M/(ρ-r)^3 := by
  let P : ℂ → ℂ := fun w => sourceAngularEtaRemainderJointAnnularPrimitive hp hp1 m s (c m) r R z₀ (w,ψ)
  let Q := sourceStandardRoot hp hp1 ψ m
  let f : ℂ → ℂ := fun w => (sourceAngularGapNumerator hp hp1 m m s ψ w-I)/Q w
  have hρ : 0 < ρ := D.inner_pos.trans hrρ
  have hδ : 0 < ρ-r := sub_pos.mpr hrρ
  have hQ (w : ℂ) (hw : w ∈ sphere (c m) ρ) : ρ-r ≤ ‖Q w‖ :=
    D.norm_selectedRoot_ge_on_circle ψ hψ ρ hrρ w hw
  have hP (w : ℂ) (hw : w ∈ sphere (c m) ρ) : HasDerivAt P (f w) w := by
    rw [show f w = sourceAngularEtaRemainderIntegrand hp hp1 m s ψ w from
      (sourceAngularEtaRemainderIntegrand_eq_gapNumerator hp hp1 m s ψ w).symm]
    apply D.etaRemainderJointAnnularPrimitive_derivative ψ hψ w
    have hd := mem_sphere.mp hw
    exact ⟨mem_ball.mpr (hd.trans_lt hρR),
      fun h => (not_le_of_gt hrρ) (hd ▸ mem_closedBall.mp h)⟩
  have hf (w : ℂ) (hw : w ∈ sphere (c m) ρ) : ‖f w‖ ≤ M/(ρ-r) := by
    rw [show f w = (sourceAngularGapNumerator hp hp1 m m s ψ w-I)/Q w from rfl,norm_div]
    exact div_le_div₀ hM (hg w hw) hδ (hQ w hw)
  have hzρ : z ∈ ball (c m) ρ := mem_ball.mpr ((mem_closedBall.mp hz).trans_lt hrρ)
  rw [D.etaQuotientCauchyCandidate_eq_sub_const ψ hψ ρ hrρ hρR (P (c m+ρ)) z hzρ]
  have h := norm_circleCauchyTransform_primitive_quotient_le P f Q (c m) ρ r (ρ-r) (M/(ρ-r))
    hρ.le hrρ hδ (by positivity) hP hf hQ z hz
  convert h using 1
  field_simp

/-- Quantitative reduction for the global eta remainder, valid throughout the
complex chart, including collapsed gaps and endpoint terminals. -/
theorem norm_etaRemainder_le_of_gapNumerator_bound
    (D : SourceAngularJointAnnulusChartData hp hp1 m s W V c T r R z₀)
    (ψ : CoeffPair p) (hψ : ψ ∈ V)
    (ρ M : ℝ) (hrρ : r < ρ) (hρR : ρ < R) (hM : 0 ≤ M)
    (hg : ∀ w ∈ sphere (c m) ρ, ‖(sourceAngularGapNumerator hp hp1 m m s ψ w-I)‖ ≤ M) :
    ‖sourceAngularEtaRemainder hp hp1 m s ψ‖ ≤
      (‖canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m-
          sourceStandardRootMidpoint hp hp1 ψ m‖ + ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖/2) *
        (Real.pi*ρ^2*M/(ρ-r)^3) := by
  rw [D.etaRemainder_eq_cauchyCandidate ρ hrρ hρR ψ hψ]
  dsimp only [sourceAngularEtaRemainderCauchyCandidate]
  rw [norm_mul]
  apply mul_le_mul
  · exact norm_sourceDirichletRootCoefficient_le hp hp1 ψ m
      (((D.disc_family ψ hψ).contour_family.2 m).2.2.1
        (ball_subset_closedBall ((D.disc_family ψ hψ).dirichlet_mem_ball m)))
  · exact D.norm_etaQuotientCauchyCandidate_le ψ hψ ρ M hrρ hρR hM hg _
      (ball_subset_closedBall (D.terminal_enclosed ψ hψ))
  · exact norm_nonneg _
  · positivity

/-- The chart geometry bounds the terminal displacement and half-gap
by three inner radii, including for complex endpoints. -/
theorem dirichletDisplacement_add_halfGap_le
    (D : SourceAngularJointAnnulusChartData hp hp1 m s W V c T r R z₀)
    (ψ : CoeffPair p) (hψ : ψ ∈ V) :
    ‖canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m-
        sourceStandardRootMidpoint hp hp1 ψ m‖ +
      ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖/2 ≤ 3*r := by
  have hμ := (mem_ball.mp (D.terminal_enclosed ψ hψ)).le
  have hτ := (mem_ball.mp (D.gap_enclosed ψ hψ
    (sourcePeriodicMidpoint_mem_segment hp hp1 ψ m))).le
  have hl := (mem_ball.mp (D.gap_enclosed ψ hψ (left_mem_segment ℝ _ _))).le
  have hr := (mem_ball.mp (D.gap_enclosed ψ hψ (right_mem_segment ℝ _ _))).le
  have hμτ := dist_triangle_right
    (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m)
    (sourceStandardRootMidpoint hp hp1 ψ m) (c m)
  have hgap := dist_triangle_right
    (canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m)
    (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m) (c m)
  rw [dist_eq_norm] at hμτ hgap
  simp only [sourcePeriodicGapDisplacement_apply,canonicalPeriodicGap]
  change _ ≤ _ at hτ
  linarith

/-- The remainder has a scalar bound using only the enclosing chart's
radii and its diagonal numerator bound. -/
theorem norm_etaRemainder_le_of_chart_bound
    (D : SourceAngularJointAnnulusChartData hp hp1 m s W V c T r R z₀)
    (ψ : CoeffPair p) (hψ : ψ ∈ V)
    (ρ M : ℝ) (hrρ : r < ρ) (hρR : ρ < R) (hM : 0 ≤ M)
    (hg : ∀ w ∈ sphere (c m) ρ, ‖sourceAngularGapNumerator hp hp1 m m s ψ w-I‖ ≤ M) :
    ‖sourceAngularEtaRemainder hp hp1 m s ψ‖ ≤
      3*r*(Real.pi*ρ^2*M/(ρ-r)^3) := by
  have hδ : 0 < ρ-r := sub_pos.mpr hrρ
  exact (D.norm_etaRemainder_le_of_gapNumerator_bound ψ hψ ρ M hrρ hρR hM hg).trans
    (mul_le_mul_of_nonneg_right (D.dirichletDisplacement_add_halfGap_le ψ hψ) (by positivity))


end SourceAngularJointAnnulusChartData
end NLS.ZakharovShabat
