import NLS.KdV.HillOnIndexAbelianCauchyCharts
import NLS.ComplexAnalysis.QuadraticCauchyUniqueness

/-! The filled quadratic solutions agree on WHOLE complex chart
overlaps. Uniqueness uses a contained actual endpoint, including a
double endpoint at collapse, rather than any real-source restriction. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV.HillAbelianCauchyChart
variable {P : HillProductEquationPatch} {m : ℕ+}

theorem onIndexRemainderSolution_eq_on_overlap (C D : HillAbelianCauchyChart P m)
    (ρ σ : ℝ) (hrρ : C.inner < ρ) (hρR : ρ < C.outer) (hsσ : D.inner < σ) (hσT : σ < D.outer)
    (q : PeriodOneHminusOne) (hqC : q ∈ C.source) (hqD : q ∈ D.source)
    (z : ℂ) (hzC : z ∈ ball (P.centers ((m:ℕ):ℤ):ℂ) ρ) (hzD : z ∈ ball (P.centers ((m:ℕ):ℤ):ℂ) σ) :
    C.onIndexRemainderSolution ρ (z,q) = D.onIndexRemainderSolution σ (z,q) := by
  let Ω := ball (P.centers ((m:ℕ):ℤ):ℂ) ρ ∩ ball (P.centers ((m:ℕ):ℤ):ℂ) σ
  let l := canonicalPeriodicLeft (by norm_num) (by norm_num) (periodOnePotential (P.sourcePsi q)) (periodOnePotential_mem _) ((m:ℕ):ℤ)
  let r := canonicalPeriodicRight (by norm_num) (by norm_num) (periodOnePotential (P.sourcePsi q)) (periodOnePotential_mem _) ((m:ℕ):ℤ)
  have hC : AnalyticOnNhd ℂ (fun w => C.onIndexRemainderSolution ρ (w,q)) (ball (P.centers ((m:ℕ):ℤ):ℂ) ρ) := by
    intro w hw
    exact (C.analytic_onIndexRemainderSolution ρ hrρ hρR (w,q) ⟨hw,hqC⟩).comp (f := fun t : ℂ => (t,q)) (analyticAt_id.prod analyticAt_const)
  have hD : AnalyticOnNhd ℂ (fun w => D.onIndexRemainderSolution σ (w,q)) (ball (P.centers ((m:ℕ):ℤ):ℂ) σ) := by
    intro w hw
    exact (D.analytic_onIndexRemainderSolution σ hsσ hσT (w,q) ⟨hw,hqD⟩).comp (f := fun t : ℂ => (t,q)) (analyticAt_id.prod analyticAt_const)
  have hH : AnalyticOnNhd ℂ (fun w => C.onIndexRemainderSolution ρ (w,q)-D.onIndexRemainderSolution σ (w,q)) Ω :=
    (hC.mono inter_subset_left).sub (hD.mono inter_subset_right)
  have hl : l ∈ Ω := ⟨ball_subset_ball hrρ.le (C.gap_enclosed q hqC (left_mem_segment ℝ _ _)),
    ball_subset_ball hsσ.le (D.gap_enclosed q hqD (left_mem_segment ℝ _ _))⟩
  apply sub_eq_zero.mp
  apply quadratic_equation_homogeneous_eq_zero l r _ Ω (isOpen_ball.inter isOpen_ball)
    ((convex_ball _ _).inter (convex_ball _ _)).isPreconnected hl hH _ z ⟨hzC,hzD⟩
  intro w hw
  change sourceAngularSelectedPolynomial (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ) w*
      deriv (fun v => C.onIndexRemainderSolution ρ (v,q)-D.onIndexRemainderSolution σ (v,q)) w+
    (w-sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ))*
      (C.onIndexRemainderSolution ρ (w,q)-D.onIndexRemainderSolution σ (w,q)) = 0
  have hd : HasDerivAt (fun v => C.onIndexRemainderSolution ρ (v,q)-D.onIndexRemainderSolution σ (v,q))
      (deriv (fun v => C.onIndexRemainderSolution ρ (v,q)) w-deriv (fun v => D.onIndexRemainderSolution σ (v,q)) w) w :=
    (hC w hw.1).differentiableAt.hasDerivAt.sub (hD w hw.2).differentiableAt.hasDerivAt
  rw [hd.deriv]
  linear_combination C.onIndexRemainderSolution_equation ρ hrρ hρR q hqC w hw.1-
    D.onIndexRemainderSolution_equation σ hsσ hσT q hqD w hw.2

end NLS.KdV.HillAbelianCauchyChart
