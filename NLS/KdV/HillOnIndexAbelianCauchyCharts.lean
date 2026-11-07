import NLS.KdV.HillOnIndexAbelianRemainder

/-! The zero-period remainder of the ACTUAL diagonal Hill differential
has a jointly analytic filled quadratic Cauchy solution. Its right
side is the actual diagonal gap numerator MINUS I. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV.HillAbelianCauchyChart
variable {P : HillProductEquationPatch} {m : ℕ+}

def onIndexRemainderSolution (C : HillAbelianCauchyChart P m) (ρ : ℝ) : ℂ × PeriodOneHminusOne → ℂ :=
  parametricQuadraticCauchySolution (P.onIndexAbelianRemainderDifferential m)
    (fun t => sourceStandardRoot (by norm_num) (by norm_num) (P.sourcePsi t.2) ((m:ℕ):ℤ) t.1)
    (P.centers ((m:ℕ):ℤ):ℂ) C.inner C.outer ρ

theorem analytic_onIndexRemainderSolution (C : HillAbelianCauchyChart P m) (ρ : ℝ)
    (hrρ : C.inner < ρ) (hρR : ρ < C.outer) :
    AnalyticOnNhd ℂ (C.onIndexRemainderSolution ρ) (ball (P.centers ((m:ℕ):ℤ):ℂ) ρ ×ˢ C.source) := by
  apply analyticOnNhd_parametricQuadraticCauchySolution _ _ _ C.inner C.outer ρ C.inner_pos hrρ hρR
    C.source C.source_open ((P.analytic_onIndexAbelianRemainderDifferential m).mono C.closed_annulus_mem_rootDomain) C.analytic_root_annulus
  intro t ht
  exact sourceStandardRoot_ne_zero_off_segment (by norm_num) (by norm_num) (P.sourcePsi t.2) ((m:ℕ):ℤ) t.1
    (fun h => ht.1.2 (ball_subset_closedBall (C.gap_enclosed t.2 ht.2 h)))

theorem onIndexRemainderSolution_equation (C : HillAbelianCauchyChart P m)
    (ρ : ℝ) (hrρ : C.inner < ρ) (hρR : ρ < C.outer) (q : PeriodOneHminusOne) (hq : q ∈ C.source)
    (z : ℂ) (hz : z ∈ ball (P.centers ((m:ℕ):ℤ):ℂ) ρ) :
    sourceAngularSelectedPolynomial (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ) z*
        deriv (fun w => C.onIndexRemainderSolution ρ (w,q)) z+
      (z-sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ))*C.onIndexRemainderSolution ρ (z,q) =
        P.abelianGapNumerator m m (z,q)-I := by
  apply parametricQuadraticCauchySolution_equation _ _ (fun t => P.abelianGapNumerator m m t-I) _ _ _ C.inner C.outer ρ
    C.inner_pos hrρ hρR C.source C.source_open ((P.analytic_onIndexAbelianRemainderDifferential m).mono C.closed_annulus_mem_rootDomain) C.analytic_root_annulus q hq
  · intro w hw
    exact sourceStandardRoot_ne_zero_off_segment (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ) w
      (fun h => hw.2 (ball_subset_closedBall (C.gap_enclosed q hq h)))
  · intro w hw
    change sourceStandardRoot (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ) w^2 =
      sourceAngularSelectedPolynomial (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ) w
    rw [sourceAngularSelectedPolynomial_eq_endpoint_factor]
    exact sourceStandardRoot_sq_of_not_mem_segment (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ) w
      (fun h => hw.2 (ball_subset_closedBall (C.gap_enclosed q hq h)))
  · intro w hw
    exact P.onIndexAbelianRemainderDifferential_eq_gap_quotient m (w,q)
      (C.closed_annulus_mem_rootDomain (w,q) ⟨⟨ball_subset_closedBall hw.1,fun h => hw.2 (ball_subset_closedBall h)⟩,hq⟩).2
  · intro w hw
    exact ((P.analytic_abelianGapNumerator_on_patch m m (w,q)
      ⟨closedBall_subset_closedBall (hρR.trans C.outer_lt_assigned).le hw,C.subset hq⟩).comp
      (f := fun t : ℂ => (t,q)) (analyticAt_id.prod analyticAt_const)).sub analyticAt_const
  · let D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ) := {
      center := P.centers ((m:ℕ):ℤ)
      radius := C.inner
      radius_pos := C.inner_pos
      gap := C.gap_enclosed q hq
      other := by
        intro j hj w hw
        let E := P.isolating.periodCircle (P.sourcePsi q) (P.image q (C.subset hq)).2 ((m:ℕ):ℤ)
          (P.centers ((m:ℕ):ℤ)) (P.radii ((m:ℕ):ℤ)) (P.radii_pos _) (P.discs_eq _)
        rcases E.other j hj w hw with h | h
        · change w.re < P.centers ((m:ℕ):ℤ)-P.radii ((m:ℕ):ℤ) at h
          exact Or.inl (by linarith [C.inner_lt_outer,C.outer_lt_assigned])
        · change P.centers ((m:ℕ):ℤ)+P.radii ((m:ℕ):ℤ) < w.re at h
          exact Or.inr (by linarith [C.inner_lt_outer,C.outer_lt_assigned]) }
    exact P.onIndexAbelianRemainderDifferential_period m q (C.subset hq) D
  · exact hz

end NLS.KdV.HillAbelianCauchyChart
