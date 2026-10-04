import NLS.ZakharovShabat.NLSHamiltonianPhasePolynomial
import NLS.ComplexAnalysis.LocalSinhComparison
import NLS.ComplexAnalysis.SampledAnalyticOrder

/-! # Hamiltonian coefficients recovered from the actual discriminant

For smooth periodic physical potentials, any normalized analytic exterior
phase with the correct discriminant has the physical Hamiltonian Taylor
coefficients. A sequence of free cosine zeros removes the oscillation.
-/
noncomputable section
open Set Complex Filter Topology NLS.ComplexAnalysis
open scoped ContDiff
namespace NLS.ZakharovShabat

/-- Discriminant asymptotics give the same-order phase error on any sequence
of real free cosine zeros escaping to positive infinity. -/
theorem exists_nlsHamiltonian_sampled_phase_error (a b : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1)
    (A : ℂ → ℂ) (hA : ContinuousAt A 0) (hA0 : A 0 = 0)
    (r : ℕ → ℝ) (hr : Tendsto r atTop atTop) (hcos : ∀ j, Real.cos (r j) = 0)
    (he : ∀ᶠ j in atTop,
      2*cosh (-I*(r j : ℂ)+A (r j : ℂ)⁻¹) =
        classicalDiscriminant (classicalPotentialOfFunctions a b ha.continuous hb.continuous) (r j))
    (N : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ᶠ j in atTop,
      ‖A (r j : ℂ)⁻¹-nlsHamiltonianCorrection a b N (r j : ℂ)⁻¹‖ ≤
        C*‖(r j : ℂ)⁻¹‖^N := by
  obtain ⟨ε,hε,hlocal⟩ := exists_norm_phase_sub_le_discriminant_error
  have hw : Tendsto (fun j => (r j : ℂ)⁻¹) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Pi.inv_apply,ofReal_inv,ofReal_zero] using! (continuous_ofReal.tendsto 0).comp hr.inv_tendsto_atTop
  have htA : Tendsto (fun j => A (r j : ℂ)⁻¹) atTop (𝓝 0) := by
    simpa [hA0,Function.comp_def] using! hA.tendsto.comp hw
  have htP : Tendsto (fun j => nlsHamiltonianCorrection a b N (r j : ℂ)⁻¹) atTop (𝓝 0) := by
    simpa [Function.comp_def] using! (analyticAt_nlsHamiltonianCorrection a b N 0).continuousAt.tendsto.comp hw
  obtain ⟨C,hC,hbound⟩ := exists_classicalDiscriminant_hamiltonian_error_bound a b ha hb hpa hpb N
  refine ⟨C/2^N,by positivity,?_⟩
  filter_upwards [he,hr.eventually (eventually_ge_atTop 1),
    htA.eventually (Metric.ball_mem_nhds (0 : ℂ) hε),
    htP.eventually (Metric.ball_mem_nhds (0 : ℂ) hε)] with j hej hrj hAj hPj
  have hloc := hlocal (r j) _ _ (hcos j) (by simpa using hAj) (by simpa using hPj)
  rw [hej] at hloc
  have heq : 2*cos (I*nlsHamiltonianPhase a b N (r j)) =
      2*cosh (-I*(r j : ℂ)+nlsHamiltonianCorrection a b N (r j : ℂ)⁻¹) := by
    rw [mul_comm I,cos_mul_I,nlsHamiltonianPhase_eq_correction]
  have hboundj := hbound (r j) (by rw [abs_of_nonneg (by linarith)]; exact hrj)
  rw [heq] at hboundj
  apply (hloc.trans hboundj).trans_eq
  rw [norm_inv,Complex.norm_real,Real.norm_eq_abs,mul_pow,inv_pow]
  ring

/-- All Taylor coefficients of a normalized analytic phase are the physical
NLS Hamiltonians, provided its hyperbolic cosine is the actual discriminant. -/
theorem iteratedDeriv_nlsHamiltonian_of_discriminant (a b : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1)
    (A : ℂ → ℂ) (hA : AnalyticAt ℂ A 0) (hA0 : A 0 = 0)
    (he : ∀ᶠ r : ℝ in atTop,
      2*cosh (-I*(r : ℂ)+A (r : ℂ)⁻¹) =
        classicalDiscriminant (classicalPotentialOfFunctions a b ha.continuous hb.continuous) r)
    (k : ℕ) :
    iteratedDeriv (k+1) A 0 =
      ((k+1).factorial : ℂ)*(I*classicalNLSHamiltonian a b (k+1)/2^(k+1)) := by
  let r : ℕ → ℝ := fun j => Real.pi*((j : ℝ)+1/2)
  have hr : Tendsto r atTop atTop :=
    (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds).const_mul_atTop Real.pi_pos
  have hcos (j : ℕ) : Real.cos (r j) = 0 := by
    have h : r j = (j : ℝ)*Real.pi+Real.pi/2 := by dsimp [r]; ring
    rw [h,Real.cos_add_pi_div_two,Real.sin_nat_mul_pi,neg_zero]
  have hw : Tendsto (fun j => (r j : ℂ)⁻¹) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Pi.inv_apply,ofReal_inv,ofReal_zero] using! (continuous_ofReal.tendsto 0).comp hr.inv_tendsto_atTop
  have hw0 : ∀ᶠ j in atTop, (r j : ℂ)⁻¹ ≠ 0 := by
    filter_upwards [hr.eventually (eventually_gt_atTop 0)] with j hj
    exact inv_ne_zero (ofReal_ne_zero.mpr hj.ne')
  obtain ⟨C,_,hbound⟩ := exists_nlsHamiltonian_sampled_phase_error a b ha hb hpa hpb A
    hA.continuousAt hA0 r hr hcos (hr.eventually he) (k+2)
  have hzero := iteratedDeriv_eq_zero_of_sampled_bound
    (fun w => A w-nlsHamiltonianCorrection a b (k+2) w)
    (hA.sub (analyticAt_nlsHamiltonianCorrection a b (k+2) 0))
    (fun j => (r j : ℂ)⁻¹) hw hw0 (k+2) C hbound (k+1) (by omega)
  rw [iteratedDeriv_fun_sub hA.contDiffAt
    (analyticAt_nlsHamiltonianCorrection a b (k+2) 0).contDiffAt] at hzero
  exact (sub_eq_zero.mp hzero).trans (iteratedDeriv_nlsHamiltonianCorrection a b (k+2) k (by omega))

/-- The identified Hamiltonian coefficients form a convergent series, not
only a formal asymptotic expansion. -/
theorem exists_nlsHamiltonian_series_of_discriminant (a b : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1)
    (A : ℂ → ℂ) (hA : AnalyticAt ℂ A 0) (hA0 : A 0 = 0)
    (he : ∀ᶠ r : ℝ in atTop,
      2*cosh (-I*(r : ℂ)+A (r : ℂ)⁻¹) =
        classicalDiscriminant (classicalPotentialOfFunctions a b ha.continuous hb.continuous) r) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ w : ℂ, ‖w‖ < ε →
      HasSum (fun k : ℕ => (I*classicalNLSHamiltonian a b (k+1)/2^(k+1))*w^(k+1)) (A w) := by
  have hs := hasFPowerSeriesAt_iff.mp hA.hasFPowerSeriesAt
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp hs
  refine ⟨ε,hε,?_⟩
  intro w hw
  have hsum := hball (show w ∈ Metric.ball (0 : ℂ) ε by simpa using hw)
  simp only [FormalMultilinearSeries.coeff_ofScalars,smul_eq_mul,zero_add] at hsum
  have htail := (hasSum_nat_add_iff' 1).mpr hsum
  have hcoeff (k : ℕ) : iteratedDeriv (k+1) A 0 / ((k+1).factorial : ℂ) =
      I*classicalNLSHamiltonian a b (k+1)/2^(k+1) := by
    rw [iteratedDeriv_nlsHamiltonian_of_discriminant a b ha hb hpa hpb A hA hA0 he k]
    field_simp [show ((k+1).factorial : ℂ) ≠ 0 by exact_mod_cast Nat.factorial_ne_zero (k+1)]
  simpa only [hcoeff,Finset.sum_range_one,iteratedDeriv_zero,hA0,zero_div,mul_zero,zero_mul,sub_zero,mul_comm] using htail

/-- The physical Hamiltonian series converges throughout an exterior complex
neighborhood whenever a normalized analytic inversion phase exists. -/
theorem exists_nlsHamiltonian_laurent_of_discriminant (a b : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1)
    (A : ℂ → ℂ) (hA : AnalyticAt ℂ A 0) (hA0 : A 0 = 0)
    (he : ∀ᶠ r : ℝ in atTop,
      2*cosh (-I*(r : ℂ)+A (r : ℂ)⁻¹) =
        classicalDiscriminant (classicalPotentialOfFunctions a b ha.continuous hb.continuous) r) :
    ∃ R : ℝ, 0 < R ∧ ∀ z : ℂ, R < ‖z‖ →
      HasSum (fun k : ℕ => I*classicalNLSHamiltonian a b (k+1)/(2*z)^(k+1)) (A z⁻¹) := by
  obtain ⟨ε,hε,hs⟩ := exists_nlsHamiltonian_series_of_discriminant a b ha hb hpa hpb A hA hA0 he
  refine ⟨ε⁻¹,inv_pos.mpr hε,?_⟩
  intro z hz
  have hw : ‖z⁻¹‖ < ε := by
    rw [norm_inv]
    exact (inv_lt_comm₀ ((inv_pos.mpr hε).trans hz) hε).mpr hz
  convert hs z⁻¹ hw using 1
  ext k
  rw [mul_pow,div_mul_eq_div_div,div_eq_mul_inv,inv_pow]

end NLS.ZakharovShabat
