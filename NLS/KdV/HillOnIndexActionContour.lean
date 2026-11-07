import NLS.KdV.HillOnIndexActionVelocity

/-! The actual on-index phase has the same original-energy action
contour variation as every off-index Abelian value. The selected
gap is open by the actual phase chart; its physical sheet may be zero. -/
noncomputable section
open Set Metric Complex NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.KdV.HillPhysicalOnIndexPhaseChart
variable {P : HillProductEquationPatch} {n : ℕ+}

theorem exists_phase_action_bracket_contour (C : HillPhysicalOnIndexPhaseChart P n)
    (k : ℕ+) (q : PeriodOneHminusOne) (hq : q ∈ C.source) (hr : IsRealPeriodOneHminusOne q) :
    ∃ u : Coeff 2, ∃ c : ℂ, periodOneMiura u=q+periodOneL2Inclusion (lp.single 2 0 c) ∧
      ∃ a : ℂ, ∃ R : ℝ, 0 < R ∧
        CircleIntegrable (hillMiuraActionDirichletIntegrand n q u c) a R ∧
        deriv (hillHminusDirichlet q) (hillHminusCanonicalDirichlet n q)*
          NLS.Poisson.hminusGardnerBracket C.phase (hillHminusCanonicalAction k) q =
          -hillHminusCanonicalPsi n (hillHminusCanonicalDirichlet n q,q)*(Real.pi:ℂ)⁻¹*
            (∮ z in C(a,R), hillMiuraActionDirichletIntegrand n q u c z) := by
  obtain ⟨B,hqB⟩ := exists_hillHminusMiuraActionBall q hr
  obtain ⟨a,R,hR,r,hrpos,_,hcircle,_,hphase⟩ := C.exists_local_action_velocity B k q hq hqB hr
  have hqr : q ∈ ball q r := mem_ball_self hrpos
  have hdir := C.source_subset_dirichlet hq
  have hci : CircleIntegrable (hillMiuraActionDirichletIntegrand n q (B.lift q) (B.shift:ℂ)) a R :=
    ((analyticOnNhd_hillMiuraActionDirichletIntegrand n q hdir _ _).continuousOn.mono
      (hcircle q hqr)).circleIntegrable hR.le
  refine ⟨B.lift q,B.shift,B.image q hqB,a,R,hR,hci,?_⟩
  let d := deriv (hillHminusDirichlet q) (hillHminusCanonicalDirichlet n q)
  have hd : d ≠ 0 := deriv_hillHminusCanonicalDirichlet_ne_zero n q hdir
  have hv : d*B.dirichletContourVelocity n a R q = -(Real.pi:ℂ)⁻¹*
      (∮ z in C(a,R), hillMiuraActionDirichletIntegrand n q (B.lift q) (B.shift:ℂ) z) := by
    dsimp only [HillHminusMiuraActionBall.dirichletContourVelocity]
    change d*(-(Real.pi:ℂ)⁻¹*d⁻¹*_) = _
    calc
      _ = (-(Real.pi:ℂ)⁻¹*(∮ z in C(a,R), hillMiuraActionDirichletIntegrand n q
        (B.lift q) (B.shift:ℂ) z))*(d*d⁻¹) := by ring
      _ = _ := by rw [mul_inv_cancel₀ hd,mul_one]
  have hb := hphase q hqr
  linear_combination d*hb+hillHminusCanonicalPsi n (hillHminusCanonicalDirichlet n q,q)*hv

end NLS.KdV.HillPhysicalOnIndexPhaseChart
