import NLS.ZakharovShabat.SobolevHamiltonianPhase

/-! # The intrinsic next Hamiltonian phase

All Hamiltonians available on the original Sobolev source define a phase analytic away from the spectral pole.
-/

noncomputable section
open Set Complex NLS.Fourier
open scoped ContDiff
namespace NLS.ZakharovShabat

/-- The next finite phase uses all Hamiltonians available on Hs,
including the (s+1)-st Hamiltonian defined by the top L2 Riccati density. -/
def sobolevNextHamiltonianPhase (s : ℕ) (ab : SobolevSource s) (z : ℂ) : ℂ :=
  -I*z+∑ k : Fin (s+1), I*sobolevNLSHamiltonian s ab (k.val+1) (by omega)/(2*z)^(k.val+1)

/-- The next phase is jointly analytic in the original source and
spectral parameter away from the finite phase's pole. -/
theorem analyticAt_sobolevNextHamiltonianPhase_joint (s : ℕ)
    (q : SobolevSource s × ℂ) (hz : q.2 ≠ 0) :
    AnalyticAt ℂ (fun p : SobolevSource s × ℂ => sobolevNextHamiltonianPhase s p.1 p.2) q := by
  apply (analyticAt_const.mul analyticAt_snd).add
  exact Finset.analyticAt_fun_sum Finset.univ (fun k _ =>
    (analyticAt_const.mul ((analyticAt_sobolevNLSHamiltonian s (k.val+1) (by omega) q.1).comp
      analyticAt_fst)).div ((analyticAt_const.mul analyticAt_snd).pow (k.val+1))
      (pow_ne_zero _ (mul_ne_zero (by norm_num) hz)))

/-- The next source phase agrees with its physical smooth phase. -/
theorem sobolevNextHamiltonianPhase_eq_classical
    (s : ℕ) (ab : SobolevSource s) (a b : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1)
    (hca : ∀ j, ab.1.val j = periodOneCoefficient a j)
    (hcb : ∀ j, ab.2.val j = periodOneCoefficient b j) (z : ℂ) :
    sobolevNextHamiltonianPhase s ab z = nlsHamiltonianPhase a b (s+1) z := by
  simp only [sobolevNextHamiltonianPhase,nlsHamiltonianPhase,Finset.sum_range]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [sobolevNLSHamiltonian_eq_classical s ab a b ha hb hpa hpb hca hcb]

end NLS.ZakharovShabat
