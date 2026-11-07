import NLS.KdV.HillOnIndexEnergyCoefficients
import NLS.ComplexAnalysis.QuadraticPhaseDerivative

/-! The ACTUAL even/odd diagonal Cartesian coefficients satisfy the
original Hill branch system at every regular point of each assigned
disc, with the full native Hill radicand and normalized numerator. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch

theorem onIndexFrequency_branch_system_of_quadratic_ne_zero
    (P : HillProductEquationPatch) (n : ℕ+) (q : PeriodOneHminusOne) (hq : q ∈ P.source)
    (z : ℂ) (hz : z ∈ ball (P.centers ((n:ℕ):ℤ):ℂ) (P.radii ((n:ℕ):ℤ)))
    (hne : sourceAngularSelectedPolynomial (by norm_num) (by norm_num) (P.sourcePsi q) ((n:ℕ):ℤ) z ≠ 0) :
    deriv (fun w => P.onIndexFrequencyEven n (w,q)) z =
      (I*P.abelianFrequencyNumerator n (z,q))*P.onIndexFrequencyOdd n (z,q) ∧
    hillHminusRadicand q (z^2-(P.parent.parent.miuraBall.actionBall.shift:ℂ))*
        deriv (fun w => P.onIndexFrequencyOdd n (w,q)) z+
      (deriv (fun w => hillHminusRadicand q (w^2-(P.parent.parent.miuraBall.actionBall.shift:ℂ))) z/2)*P.onIndexFrequencyOdd n (z,q) =
      (I*P.abelianFrequencyNumerator n (z,q))*P.onIndexFrequencyEven n (z,q) := by
  let τ := sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi q) ((n:ℕ):ℤ)
  let d := (canonicalPeriodicGap (by norm_num) (by norm_num) (periodOnePotential (P.sourcePsi q)) (periodOnePotential_mem _) ((n:ℕ):ℤ))^2/4
  let Q := quadraticRootPolynomial τ d
  let H : ℂ → ℂ := fun w => P.onIndexAbelianFilledRemainder n (w,q)
  let K : ℂ → ℂ := fun w => P.abelianGapRootMultiplier n (w,q)
  let A : ℂ → ℂ := fun w => P.onIndexFrequencyEven n (w,q)
  let B : ℂ → ℂ := fun w => P.onIndexFrequencyOdd n (w,q)
  let D : ℂ → ℂ := fun w => K w^2*Q w
  let w := Complex.sqrt (Q z)
  have hw : w ≠ 0 := by intro he; apply hne; change Q z = 0; rw [← complex_sqrt_sq (Q z)]; change w^2 = 0; rw [he]; norm_num
  let R := prescribedSquareRoot Q w
  let S : ℂ → ℂ := fun v => K v*R v
  let f := I*P.abelianFrequencyNumerator n (z,q)
  let g := P.abelianGapNumerator n n (z,q)
  have hQ : AnalyticOnNhd ℂ Q univ := by intro v _; unfold Q quadraticRootPolynomial; fun_prop
  have hR : AnalyticAt ℂ R z := analyticOnNhd_prescribedSquareRoot Q w hQ z
    (mem_prescribedSquareRootDomain Q w hw z (complex_sqrt_sq (Q z)).symm)
  have hRne : R z ≠ 0 := by rw [show R z = w from prescribedSquareRoot_base Q w hw z (complex_sqrt_sq (Q z)).symm]; exact hw
  have hRsq (v : ℂ) : R v^2 = Q v := prescribedSquareRoot_sq Q w hw v
  have hRnear : (fun v => R v^2) =ᶠ[𝓝 z] Q := Filter.Eventually.of_forall hRsq
  have hH := (P.analytic_onIndexAbelianFilledRemainder n (z,q) ⟨hz,hq⟩).comp
    (f := fun v : ℂ => (v,q)) (analyticAt_id.prod analyticAt_const)
  have hK := (P.analytic_abelianGapRootMultiplier n (z,q) ⟨hz,hq⟩).comp
    (f := fun v : ℂ => (v,q)) (analyticAt_id.prod analyticAt_const)
  have hKne : K z ≠ 0 := P.abelianGapRootMultiplier_ne_zero n (z,q) ⟨hz,hq⟩
  have hA := (P.analytic_onIndexFrequencyEven n (z,q) ⟨hz,hq⟩).comp
    (f := fun v : ℂ => (v,q)) (analyticAt_id.prod analyticAt_const)
  have hB := (P.analytic_onIndexFrequencyOdd n (z,q) ⟨hz,hq⟩).comp
    (f := fun v : ℂ => (v,q)) (analyticAt_id.prod analyticAt_const)
  have hS : AnalyticAt ℂ S z := hK.mul hR
  have hSne : S z ≠ 0 := mul_ne_zero hKne hRne
  have hD : AnalyticAt ℂ D z := (hK.pow 2).mul (hQ z (mem_univ _))
  have hSD : (fun v => S v^2) =ᶠ[𝓝 z] D := by
    filter_upwards [] with v
    dsimp only [S,D]
    rw [mul_pow,hRsq v]
  have heq : Q z*deriv H z+(z-τ)*H z = g-I := P.onIndexAbelianFilledRemainder_equation n q hq z hz
  have hpRaw := hasDerivAt_quadratic_phase_plus R H τ d (-4*τ) g z hR hRne hRnear hH heq
  have hmRaw := hasDerivAt_quadratic_phase_minus R H τ d (-4*τ) g z hR hRne hRnear hH heq
  have hpEq : (fun v => A v+S v*B v) =ᶠ[𝓝 z] (fun v => (-4*τ)*(v-τ-R v)*Complex.exp (I*R v*H v)) := by
    filter_upwards [isOpen_ball.mem_nhds hz] with v hv
    exact P.onIndexFrequencyEven_add_root_mul_odd n (v,q) ⟨hv,hq⟩ (R v) (hRsq v)
  have hmEq : (fun v => A v-S v*B v) =ᶠ[𝓝 z] (fun v => (-4*τ)*(v-τ+R v)*Complex.exp (-I*R v*H v)) := by
    filter_upwards [isOpen_ball.mem_nhds hz] with v hv
    exact P.onIndexFrequencyEven_sub_root_mul_odd n (v,q) ⟨hv,hq⟩ (R v) (hRsq v)
  have hforce : f/S z = I*g/R z := by
    change (I*P.abelianFrequencyNumerator n (z,q))/(K z*R z) = I*(P.abelianFrequencyNumerator n (z,q)/K z)/R z
    field_simp [hKne,hRne]
  have hforceMinus : -f/S z = -I*g/R z := by simpa only [neg_div,neg_mul] using congrArg Neg.neg hforce
  have hp : HasDerivAt (fun v => A v+S v*B v) ((f/S z)*(A z+S z*B z)) z := by
    rw [hpEq.eq_of_nhds,hforce]
    exact hpRaw.congr_of_eventuallyEq hpEq
  have hm : HasDerivAt (fun v => A v-S v*B v) ((-f/S z)*(A z-S z*B z)) z := by
    rw [hmEq.eq_of_nhds,hforceMinus]
    exact hmRaw.congr_of_eventuallyEq hmEq
  have hs := branch_system_of_two_sheet_derivatives D A B S f z hD.differentiableAt hA.differentiableAt
    hB.differentiableAt hS.differentiableAt hSne hSD hp hm
  have hnative : D =ᶠ[𝓝 z] (fun v => hillHminusRadicand q (v^2-(P.parent.parent.miuraBall.actionBall.shift:ℂ))) := by
    filter_upwards [isOpen_ball.mem_nhds hz] with v hv
    exact P.abelianGapRootMultiplier_sq_mul_polynomial n (v,q) ⟨hv,hq⟩
  rw [hnative.eq_of_nhds,hnative.deriv_eq] at hs
  exact hs

end NLS.KdV.HillProductEquationPatch
