import NLS.ZakharovShabat.ClassicalSwapDiscriminant
import NLS.ZakharovShabat.NLSHamiltonianPhasePolynomial
import NLS.ComplexAnalysis.LocalSinhComparison

/-! # Sampled cancellation of reflected Hamiltonian phases

Actual discriminant asymptotics give arbitrary-order cancellation of the two phase corrections at free cosine zeros.
-/

noncomputable section
open Set Complex Filter Topology NLS.ComplexAnalysis NLS.LinearVolterra
open scoped ContDiff
namespace NLS.ZakharovShabat

/-- Reflection symmetry of the actual discriminant forces the two finite
phase corrections to cancel to arbitrary sampled inverse-frequency order. -/
theorem exists_nlsHamiltonian_reflected_phase_sampled_bound
    (a b : ℝ → ℂ) (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1)
    (r : ℕ → ℝ) (hr : Tendsto r atTop atTop) (hcos : ∀ j, Real.cos (r j) = 0)
    (N : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ᶠ j in atTop,
      ‖nlsHamiltonianCorrection a b N (r j:ℂ)⁻¹+
        nlsHamiltonianCorrection (-b) (-a) N (-(r j:ℂ)⁻¹)‖ ≤ C*‖(r j:ℂ)⁻¹‖^N := by
  have hpb' : Function.Periodic (-b) 1 := by
    intro x; change -b (x+1) = -b x; rw [hpb x]
  have hpa' : Function.Periodic (-a) 1 := by
    intro x; change -a (x+1) = -a x; rw [hpa x]
  obtain ⟨ε,hε,hlocal⟩ := exists_norm_phase_sub_le_discriminant_error
  have hw : Tendsto (fun j => (r j:ℂ)⁻¹) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Pi.inv_apply,ofReal_inv,ofReal_zero] using!
      (continuous_ofReal.tendsto 0).comp hr.inv_tendsto_atTop
  have hw' : Tendsto (fun j => -(r j:ℂ)⁻¹) atTop (𝓝 0) := by simpa using hw.neg
  have htP : Tendsto (fun j => nlsHamiltonianCorrection a b N (r j:ℂ)⁻¹) atTop (𝓝 0) := by
    simpa only [Function.comp_def,nlsHamiltonianCorrection_zero] using!
      (analyticAt_nlsHamiltonianCorrection a b N 0).continuousAt.tendsto.comp hw
  have htQ : Tendsto (fun j => -nlsHamiltonianCorrection (-b) (-a) N (-(r j:ℂ)⁻¹)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,nlsHamiltonianCorrection_zero,neg_zero] using!
      ((analyticAt_nlsHamiltonianCorrection (-b) (-a) N 0).continuousAt.tendsto.comp hw').neg
  obtain ⟨C,hC,hbound⟩ := exists_classicalDiscriminant_hamiltonian_error_bound a b ha hb hpa hpb N
  obtain ⟨D,hD,hbound'⟩ := exists_classicalDiscriminant_hamiltonian_error_bound (-b) (-a)
    hb.neg ha.neg hpb' hpa' N
  refine ⟨(C+D)/2^N,by positivity,?_⟩
  filter_upwards [hr.eventually (eventually_ge_atTop 1),
    htP.eventually (Metric.ball_mem_nhds (0:ℂ) hε),
    htQ.eventually (Metric.ball_mem_nhds (0:ℂ) hε)] with j hrj hPj hQj
  have hloc := hlocal (r j) (nlsHamiltonianCorrection a b N (r j:ℂ)⁻¹)
    (-nlsHamiltonianCorrection (-b) (-a) N (-(r j:ℂ)⁻¹)) (hcos j) (by simpa using hPj) (by simpa using hQj)
  have heq : 2*cos (I*nlsHamiltonianPhase a b N (r j)) =
      2*cosh (-I*(r j:ℂ)+nlsHamiltonianCorrection a b N (r j:ℂ)⁻¹) := by
    rw [mul_comm I,cos_mul_I,nlsHamiltonianPhase_eq_correction]
  have heq' : 2*cos (I*nlsHamiltonianPhase (-b) (-a) N (-(r j:ℂ))) =
      2*cosh (-I*(r j:ℂ)-nlsHamiltonianCorrection (-b) (-a) N (-(r j:ℂ)⁻¹)) := by
    rw [mul_comm I,cos_mul_I,nlsHamiltonianPhase_eq_correction,inv_neg]
    have hh : -I * -(r j:ℂ)+nlsHamiltonianCorrection (-b) (-a) N (-(r j:ℂ)⁻¹) =
        -(-I*(r j:ℂ)-nlsHamiltonianCorrection (-b) (-a) N (-(r j:ℂ)⁻¹)) := by ring
    rw [hh,cosh_neg]
  have h := hbound (r j) (by rw [abs_of_nonneg (by linarith)]; exact hrj)
  have h' := hbound' (-(r j)) (by rw [abs_neg,abs_of_nonneg (by linarith)]; exact hrj)
  rw [heq] at h
  rw [ofReal_neg,heq',abs_neg] at h'
  rw [← classicalSwapPotential_ofFunctions a b ha.continuous hb.continuous,
    classicalDiscriminant_swap] at h'
  simp only [sub_neg_eq_add] at hloc
  apply hloc.trans
  have ht := norm_sub_le_norm_sub_add_norm_sub
    (2*cosh (-I*(r j:ℂ)+nlsHamiltonianCorrection a b N (r j:ℂ)⁻¹))
    (classicalDiscriminant (classicalPotentialOfFunctions a b ha.continuous hb.continuous) (r j))
    (2*cosh (-I*(r j:ℂ)-nlsHamiltonianCorrection (-b) (-a) N (-(r j:ℂ)⁻¹)))
  rw [norm_sub_rev (2*cosh _) (classicalDiscriminant _ _)] at ht
  apply (ht.trans (add_le_add h h')).trans_eq
  rw [norm_inv,Complex.norm_real,Real.norm_eq_abs,mul_pow,inv_pow]
  ring

end NLS.ZakharovShabat
