import NLS.KdV.HillFreeMiuraCriticalRatio
import NLS.KdV.HillFreeMiuraGapData
import NLS.ComplexAnalysis.CollapsedLinearFactorDerivative

/-! Exact ACTUAL free shifted-Miura trace curvature at each positive
collapsed frequency. It follows from the independently normalized scalar
Dirichlet characteristic and its simple ORIGINAL-energy derivative. -/
noncomputable section
open Set Complex Filter Topology NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV

theorem classicalHillDirichlet_free_energy (μ : ℂ) (hμ : μ ≠ 0) :
    classicalHillDirichlet 0 μ = sin (sqrt μ)/sqrt μ := by
  have hw : sqrt μ ≠ 0 := fun he => hμ (by rw [← complex_sqrt_sq μ,he]; simp)
  have h := classicalHillDirichlet_free_sq (sqrt μ) hw
  simpa only [complex_sqrt_sq] using h

theorem deriv_discriminant_shifted_free_miura_eq_dirichlet (u : PeriodOneRealL2) (c : ℝ)
    (hi : periodOneMiura u.val = periodOneL2Inclusion (lp.single 2 0 (c:ℂ)))
    (z : ℂ) (hne : z^2-(c:ℂ) ≠ 0) :
    deriv (canonicalDiscriminant (by norm_num) (periodOnePotential (hillMiuraDiagonal u.val))) z =
      -2*z*classicalHillDirichlet 0 (z^2-(c:ℂ)) := by
  rw [deriv_discriminant_shifted_free_miura u c hi z hne,classicalHillDirichlet_free_energy _ hne]
  ring

theorem HillHminusMiuraGapBall.hasDerivAt_free_trace_deriv (B : HillHminusMiuraGapBall)
    (h0 : (0 : PeriodOneHminusOne) ∈ B.source) (n : ℕ+) :
    HasDerivAt (deriv (canonicalDiscriminant (by norm_num)
      (periodOnePotential (hillMiuraDiagonal (B.actionBall.lift 0)))))
      (-2*(-1:ℂ)^(n:ℕ)*(B.freeFrequencyMidpoint n)^2/((Real.pi:ℂ)*n)^2)
      (B.freeFrequencyMidpoint n) := by
  let τ := B.freeFrequencyMidpoint n
  let c := B.actionBall.shift
  have hs : (Real.pi:ℂ)*n ≠ 0 :=
    mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) (by exact_mod_cast n.ne_zero)
  have hene : τ^2-(c:ℂ) ≠ 0 := by
    rw [B.freeFrequencyMidpoint_energy h0 n]
    exact pow_ne_zero 2 hs
  have hDir : HasDerivAt (classicalHillDirichlet 0)
      ((-1:ℂ)^(n:ℕ)/(2*((Real.pi:ℂ)*n)^2)) (τ^2-(c:ℂ)) := by
    rw [B.freeFrequencyMidpoint_energy h0 n]
    exact hasDerivAt_classicalHillDirichlet_free_eigenvalue n
  have hcomp := hasDerivAt_comp_quadratic_shift _ τ (c:ℂ) _ hDir
  have hval : classicalHillDirichlet 0 (τ^2-(c:ℂ))=0 := by
    rw [B.freeFrequencyMidpoint_energy h0 n,classicalHillDirichlet_free_sq _ hs,complex_sin_nat_pi,zero_div]
  have hprod := ((hasDerivAt_id τ).const_mul (-2)).mul hcomp
  have hmodel : HasDerivAt (fun z : ℂ => -2*z*classicalHillDirichlet 0 (z^2-(c:ℂ)))
      (-2*(-1:ℂ)^(n:ℕ)*τ^2/((Real.pi:ℂ)*n)^2) τ := by
    convert! hprod using 1
    rw [hval]
    simp only [id_eq]
    field_simp [hs]
    ring
  have hr : IsRealPeriodOneHminusOne (0 : PeriodOneHminusOne) := by intro k; simp
  let u : PeriodOneRealL2 := ⟨B.actionBall.lift 0,B.actionBall.lift_real 0 h0 hr⟩
  have hi : periodOneMiura u.val = periodOneL2Inclusion (lp.single 2 0 (c:ℂ)) := by
    simpa only [zero_add] using B.actionBall.image 0 h0
  have hopen : IsOpen {z : ℂ | z^2-(c:ℂ) ≠ 0} :=
    isOpen_ne_fun (by fun_prop) continuous_const
  have he : deriv (canonicalDiscriminant (by norm_num) (periodOnePotential (hillMiuraDiagonal u.val))) =ᶠ[𝓝 τ]
      fun z => -2*z*classicalHillDirichlet 0 (z^2-(c:ℂ)) := by
    filter_upwards [hopen.mem_nhds hene] with z hz
    exact deriv_discriminant_shifted_free_miura_eq_dirichlet u c hi z hz
  exact hmodel.congr_of_eventuallyEq he

end NLS.KdV
