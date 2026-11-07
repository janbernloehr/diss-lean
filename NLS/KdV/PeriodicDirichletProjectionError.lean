import NLS.KdV.DirichletFreeProjectionBounds
import NLS.KdV.HillBoundarySineApproximation

/-! Quantitative comparison of ACTUAL periodic and interval projections
for the identical zero-boundary physical representative. -/
noncomputable section
open Set Metric
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue NLS.ZakharovShabat

/-- Correcting the zero trace produces a free sine fixed vector. Hence
the actual interval projection error is controlled by the actual Dirichlet
operator error and six times the literal periodic two-mode uniform error.
The factor six is sufficient for the source overlap bound and does not
change its final constants one half and three halves. -/
theorem exists_periodicDirichlet_projection_error_bound :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ+, N < (n:ℕ) →
      ∀ q : FourierLebesgueSpace (2:ℝ) (-1) 2,
      ∀ F : C(AddCircle (2:ℝ),ℂ), ∀ H : CircleL2,
      F 0 = 0 →
      let v := unitIntervalContinuousToLp 2 (circleUnitContinuousRestriction F)
      ‖singularDirichletL2RieszProjection q (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ) v-v‖ ≤
        ‖singularDirichletL2RieszProjection q (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ)-
          singularDirichletL2RieszProjection 0 (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ)‖*‖v‖+
            6*‖F-hillFreeContinuousModeProjection (n:ℕ) H‖ := by
  obtain ⟨N,hN,hfree⟩ := exists_dirichletFreeProjection_bounds_and_sine_fixed
  refine ⟨N,hN,?_⟩
  intro n hn q F H h0 v
  obtain ⟨_,hP,hfix⟩ := hfree n hn
  obtain ⟨a,ha⟩ := exists_sine_approximation_of_zero_trace n F H h0
  let P := singularDirichletL2RieszProjection 0 (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ)
  let Q := singularDirichletL2RieszProjection q (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ)
  let w := a • unitIntervalContinuousToLp 2 (dirichletFreeSineCurve n)
  let E := ‖F-hillFreeContinuousModeProjection (n:ℕ) H‖
  have hw : P w = w := by
    dsimp only [w]
    rw [map_smul,hfix]
  have hvw : ‖v-w‖ ≤ 2*E := by
    change ‖unitIntervalContinuousToLp 2 (circleUnitContinuousRestriction F)-
      a • unitIntervalContinuousToLp 2 (dirichletFreeSineCurve n)‖ ≤ _
    rw [← map_smul,← map_sub]
    exact (norm_unitIntervalContinuousToLp_le 2 _).trans ha
  have herror : ‖P v-v‖ ≤ 6*E := by
    have he : P v-v = P (v-w)-(v-w) := by rw [map_sub,hw]; abel
    rw [he]
    calc
      _ ≤ ‖P (v-w)‖+‖v-w‖ := norm_sub_le _ _
      _ ≤ 2*‖v-w‖+‖v-w‖ := by
        gcongr
        exact (P.le_opNorm _).trans (mul_le_mul_of_nonneg_right hP (norm_nonneg _))
      _ ≤ 6*E := by linarith
  have he : Q v-v = (Q-P) v+(P v-v) := by rw [sub_apply]; abel
  change ‖Q v-v‖ ≤ ‖Q-P‖*‖v‖+6*E
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add ((Q-P).le_opNorm v) herror)

end NLS.KdV
