import NLS.ZakharovShabat.SobolevHamiltonianNextPhaseFree
import NLS.ZakharovShabat.SobolevWKBNextTraceDerivativeTail

/-! # Invertibility of the next Hamiltonian phase derivative

The spectral derivative tends uniformly to the free value -i on original Sobolev balls.
-/

noncomputable section
open Set Complex Metric NLS.Fourier
open scoped ContDiff ENNReal
namespace NLS.ZakharovShabat

/-- The derivative of the next phase is uniformly close to the free
value -i at high frequencies, and hence uniformly invertible. -/
theorem exists_uniform_nlsHamiltonian_next_phase_derivative_bounds
    (s N : ℕ) (hs : 1 ≤ s) (hNs : N ≤ s+1) (R : ℝ) (hR : 0 ≤ R) :
    ∃ T : ℝ, 2 ≤ T ∧ ∀ ab : SobolevSource s, ‖ab‖ ≤ R → ∀ a b : ℝ → ℂ,
      ContDiff ℝ ∞ a → ContDiff ℝ ∞ b →
      Function.Periodic a 1 → Function.Periodic b 1 →
      (∀ j, ab.1.val j = periodOneCoefficient a j) →
      (∀ j, ab.2.val j = periodOneCoefficient b j) →
      ∀ z : ℂ, T ≤ ‖z‖ →
        ‖deriv (nlsHamiltonianPhase a b N) z+I‖ ≤ 1/2 ∧
        deriv (nlsHamiltonianPhase a b N) z ≠ 0 ∧
        ‖(deriv (nlsHamiltonianPhase a b N) z)⁻¹‖ ≤ 2 := by
  obtain ⟨C,hC,hfree⟩ := exists_uniform_nlsHamiltonian_next_phase_free_bound s N hs hNs R hR
  refine ⟨4*C+2,by linarith,?_⟩
  intro ab hab a b ha hb hpa hpb hca hcb z hz
  have hzn : 2 ≤ ‖z‖ := by linarith
  let f (w : ℂ) := nlsHamiltonianPhase a b N w+I*w
  have hgeom (w : ℂ) (hw : w ∈ ball z 1) : 1 ≤ ‖w‖ ∧ ‖z‖ ≤ 2*‖w‖ := by
    have hd : ‖w-z‖ < 1 := by simpa only [mem_ball,dist_eq_norm] using hw
    have ht := norm_le_norm_add_norm_sub w z
    constructor <;> linarith
  have hf : DifferentiableOn ℂ f (ball z 1) := by
    intro w hw
    have hw0 : w ≠ 0 := norm_ne_zero_iff.mp (by linarith [(hgeom w hw).1])
    exact ((analyticAt_nlsHamiltonianPhase_spectral a b N w hw0).add
      (analyticAt_const.mul analyticAt_id)).differentiableAt.differentiableWithinAt
  have hbnd (w : ℂ) (hw : w ∈ ball z 1) : ‖f w‖ ≤ C/‖z‖ := by
    obtain ⟨hw1,hwz⟩ := hgeom w hw
    apply (hfree ab hab a b ha hb hpa hpb hca hcb w hw1).trans
    simp only [norm_inv,norm_mul,norm_ofNat,norm_I,mul_one,← div_eq_mul_inv]
    exact div_le_div_of_nonneg_left hC (by linarith) hwz
  have hmaps : MapsTo f (ball z 1) (closedBall (f z) (2*(C/‖z‖))) := by
    intro w hw
    rw [mem_closedBall,dist_eq_norm]
    exact (norm_sub_le _ _).trans (by linarith [hbnd w hw,hbnd z (mem_ball_self (by norm_num))])
  have hd : ‖deriv f z‖ ≤ 2*(C/‖z‖) := by
    rw [norm_deriv_eq_norm_fderiv]
    simpa only [div_one] using Complex.norm_fderiv_le_div_of_mapsTo_ball hf hmaps (by norm_num : (0:ℝ) < 1)
  have hphase := (analyticAt_nlsHamiltonianPhase_spectral a b N z
    (norm_ne_zero_iff.mp (by linarith))).differentiableAt.hasDerivAt
  have he : deriv f z = deriv (nlsHamiltonianPhase a b N) z+I := by
    simpa only [f,mul_one] using! (hphase.add ((hasDerivAt_id z).const_mul I)).deriv
  rw [he] at hd
  have hsmall : ‖deriv (nlsHamiltonianPhase a b N) z+I‖ ≤ 1/2 := by
    apply hd.trans
    apply (le_div_iff₀ (by norm_num : (0:ℝ) < 2)).mpr
    have hh : C/‖z‖ ≤ 1/4 := (div_le_iff₀ (by linarith : 0 < ‖z‖)).mpr (by linarith)
    linarith
  have hlower : (1/2:ℝ) ≤ ‖deriv (nlsHamiltonianPhase a b N) z‖ := by
    have ht := norm_sub_le (deriv (nlsHamiltonianPhase a b N) z+I) (deriv (nlsHamiltonianPhase a b N) z)
    simp only [add_sub_cancel_left,norm_I] at ht
    linarith
  refine ⟨hsmall,norm_ne_zero_iff.mp (by linarith),?_⟩
  rw [norm_inv,inv_eq_one_div]
  apply (div_le_iff₀ (by linarith : 0 < ‖deriv (nlsHamiltonianPhase a b N) z‖)).mpr
  linarith

end NLS.ZakharovShabat
