import NLS.ZakharovShabat.NLSWKBNextTraceIdentity
import NLS.ZakharovShabat.SobolevHamiltonianTraceTaylor
import NLS.ZakharovShabat.SobolevWKBInitialDecay

/-! # The scalar correction to the next trace

The scalar correction has uniform order N+2 on original Hs balls through the top available density.
-/

noncomputable section
open Set Complex NLS.Fourier
open scoped ContDiff ENNReal
namespace NLS.ZakharovShabat

/-- The remaining scalar correction in the exact next-phase trace has
uniform order N+2 on the original Hs ball, including the top order N=s. -/
theorem exists_uniform_nlsWKB_next_trace_correction_error_bound
    (s N : ℕ) (hs : 1 ≤ s) (hNs : N ≤ s) (R : ℝ) (hR : 0 ≤ R) (H : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ab : SobolevSource s, ‖ab‖ ≤ R → ∀ a b : ℝ → ℂ,
      ContDiff ℝ ∞ a → ContDiff ℝ ∞ b →
      Function.Periodic a 1 → Function.Periodic b 1 →
      (∀ j, ab.1.val j = periodOneCoefficient a j) →
      (∀ j, ab.2.val j = periodOneCoefficient b j) →
      ∀ z : ℂ, 1 ≤ ‖z‖ → |z.im| ≤ H →
        ‖nlsWKBNextTraceCorrectionError a b N z‖ ≤ C*‖(2*I*z)⁻¹‖^(N+2) := by
  obtain ⟨B,hB,hinit⟩ := exists_uniform_nlsWKB_initial_coordinate_decay s N hNs R hR
  obtain ⟨L,hL,hinc⟩ := exists_uniform_nlsHamiltonianPhase_increment_bound s N hs hNs R hR
  obtain ⟨T,hT,htaylor⟩ := exists_uniform_nlsHamiltonian_trace_increment_error_bound s N hs hNs R hR H
  refine ⟨(1+B^2)*T+2*B^2*Real.exp H*L,by positivity,?_⟩
  intro ab hab a b ha hb hpa hpb hca hcb z hz hzH
  let w := (2*I*z)⁻¹
  let p := nlsWKBInitialLower a b N z
  let q := nlsWKBInitialUpper a b N z
  let P := nlsWKBDiagonalPhasePrimitive a b N z 1+nlsWKBDiagonalPhasePrimitive (-b) (-a) N (-z) 1
  let E := nlsHamiltonianTraceIncrementError a b N z
  have hw : ‖w‖ ≤ 1 := by
    simp only [w,norm_inv,norm_mul,norm_ofNat,norm_I,mul_one]
    apply inv_le_one_of_one_le₀
    linarith
  have hi := hinit ab hab a b ha hb hpa hpb hca hcb z hz
  have hpq : ‖p*q‖ ≤ B^2*‖w‖^2 := by
    rw [norm_mul]
    exact (mul_le_mul hi.1 hi.2 (norm_nonneg _) (by positivity)).trans_eq (by ring)
  have hpqB : ‖p*q‖ ≤ B^2 := hpq.trans
    (mul_le_of_le_one_right (sq_nonneg _) (pow_le_one₀ (norm_nonneg _) hw))
  have hd : ‖1-p*q‖ ≤ 1+B^2 := by
    apply (norm_sub_le _ _).trans
    simpa only [norm_one] using add_le_add le_rfl hpqB
  have hminus : ‖exp (-I*z)‖ ≤ Real.exp H := by
    simpa using norm_exp_neg_I_mul_strip_le z H hzH 1 ⟨by norm_num,le_rfl⟩
  have hplus : ‖exp (I*z)‖ ≤ Real.exp H := by
    simpa only [mul_neg,neg_mul,neg_neg,Complex.ofReal_one,mul_one] using
      norm_exp_neg_I_mul_strip_le (-z) H (by simpa using hzH) 1 ⟨by norm_num,le_rfl⟩
  have hP : ‖P‖ ≤ (2*Real.exp H*L)*‖w‖^(N+1) := by
    dsimp only [P]
    rw [nlsWKBDiagonalPhasePrimitive_sum_eq_phase_increment a b ha hb hpa hpb,norm_mul,norm_neg]
    have he : ‖exp (-I*z)-exp (I*z)‖ ≤ 2*Real.exp H :=
      (norm_sub_le _ _).trans ((add_le_add hminus hplus).trans_eq (by ring))
    exact (mul_le_mul he (hinc ab hab a b ha hb hpa hpb hca hcb z)
      (norm_nonneg _) (by positivity)).trans_eq (by ring)
  have hE : ‖E‖ ≤ T*‖w‖^(N+2) := htaylor ab hab a b ha hb hpa hpb hca hcb z hz hzH
  change ‖-(1-p*q)*E-p*q*P‖ ≤ _
  calc
    _ ≤ ‖-(1-p*q)*E‖+‖p*q*P‖ := norm_sub_le _ _
    _ = ‖1-p*q‖*‖E‖+‖p*q‖*‖P‖ := by simp only [norm_mul,norm_neg]
    _ ≤ (1+B^2)*(T*‖w‖^(N+2))+(B^2*‖w‖^2)*((2*Real.exp H*L)*‖w‖^(N+1)) :=
      add_le_add (mul_le_mul hd hE (norm_nonneg _) (by positivity))
        (mul_le_mul hpq hP (norm_nonneg _) (by positivity))
    _ = ((1+B^2)*T)*‖w‖^(N+2)+(2*B^2*Real.exp H*L)*‖w‖^(N+3) := by
      simp only [pow_add,pow_one]
      ring
    _ ≤ ((1+B^2)*T)*‖w‖^(N+2)+(2*B^2*Real.exp H*L)*‖w‖^(N+2) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (pow_le_pow_of_le_one (norm_nonneg _) hw (by omega)) (by positivity))
    _ = _ := by ring

end NLS.ZakharovShabat
