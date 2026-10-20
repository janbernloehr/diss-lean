import NLS.ZakharovShabat.NLSWKBNextSeparatedIdentity
import NLS.ZakharovShabat.SobolevHamiltonianSinhTaylor
import NLS.ZakharovShabat.SobolevWKBInitialDecay
import NLS.ZakharovShabat.WKBBoundedFrequencyCutoff
import NLS.SequenceSpaces.SobolevInversePowerBound

/-! # The scalar correction to the separated next phase

Uniform inverse-power decay gives a sharper Sobolev tail for both boundary conditions and every larger cutoff.
-/

noncomputable section
open Set Complex NLS.Fourier
open scoped ContDiff ENNReal
namespace NLS.ZakharovShabat
open BoundaryCondition

/-- The remaining scalar correction in the separated next-phase identity
has uniform order N+2 on original Hs balls, including the top order N=s. -/
theorem exists_uniform_nlsWKB_next_separated_correction_error_bound
    (s N : ℕ) (hs : 1 ≤ s) (hNs : N ≤ s) (R : ℝ) (hR : 0 ≤ R) (H : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ab : SobolevSource s, ‖ab‖ ≤ R → ∀ a b : ℝ → ℂ,
      ContDiff ℝ ∞ a → ContDiff ℝ ∞ b →
      Function.Periodic a 1 → Function.Periodic b 1 →
      (∀ j, ab.1.val j = periodOneCoefficient a j) →
      (∀ j, ab.2.val j = periodOneCoefficient b j) →
      ∀ z : ℂ, 1 ≤ ‖z‖ → |z.im| ≤ H → ∀ θ : BoundaryCondition,
        ‖nlsWKBNextSeparatedCorrectionError θ a b N z‖ ≤ C*‖(2*I*z)⁻¹‖^(N+2) := by
  obtain ⟨B,hB,hinit⟩ := exists_uniform_nlsWKB_initial_coordinate_decay s N hNs R hR
  obtain ⟨L,hL,hinc⟩ := exists_uniform_nlsHamiltonianPhase_increment_bound s N hs hNs R hR
  obtain ⟨T,hT,htaylor⟩ := exists_uniform_nlsHamiltonian_sinh_increment_error_bound s N hs hNs R hR H
  refine ⟨(1+B)^2*T+2*B*(1+B)*Real.exp H*L,by positivity,?_⟩
  intro ab hab a b ha hb hpa hpb hca hcb z hz hzH θ
  let w := (2*I*z)⁻¹
  let p := nlsWKBInitialLower a b N z
  let q := nlsWKBInitialUpper a b N z
  let η := extensionSign θ
  let P := nlsWKBDiagonalPhasePrimitive a b N z 1
  let Q := nlsWKBDiagonalPhasePrimitive (-b) (-a) N (-z) 1
  let E := nlsHamiltonianSinhIncrementError a b N z
  have hη : ‖η‖ = 1 := by cases θ <;> norm_num [η,extensionSign]
  have hw : ‖w‖ ≤ 1 := by
    simp only [w,norm_inv,norm_mul,norm_ofNat,norm_I,mul_one]
    apply inv_le_one_of_one_le₀
    linarith
  have hi := hinit ab hab a b ha hb hpa hpb hca hcb z hz
  have hpw : ‖p‖ ≤ B*‖w‖ := hi.1
  have hqw : ‖q‖ ≤ B*‖w‖ := hi.2
  have hp : ‖p‖ ≤ B := hi.1.trans (mul_le_of_le_one_right hB hw)
  have hq : ‖q‖ ≤ B := hi.2.trans (mul_le_of_le_one_right hB hw)
  have hA : ‖1+p*q-η*(p+q)‖ ≤ (1+B)^2 := by
    have hpq : ‖p*q‖ ≤ B^2 := by rw [norm_mul]; nlinarith [norm_nonneg p,norm_nonneg q]
    have hsum : ‖η*(p+q)‖ ≤ 2*B := by rw [norm_mul,hη,one_mul]; linarith [norm_add_le p q]
    have h := norm_sub_le (1+p*q) (η*(p+q))
    have h' := norm_add_le (1:ℂ) (p*q)
    rw [norm_one] at h'
    nlinarith
  have hηq : ‖η-q‖ ≤ 1+B := (norm_sub_le _ _).trans (by rw [hη]; linarith)
  have hpη : ‖p-η‖ ≤ 1+B := (norm_sub_le _ _).trans (by rw [hη]; linarith)
  have hminus : ‖exp (-I*z)‖ ≤ Real.exp H := by
    simpa using norm_exp_neg_I_mul_strip_le z H hzH 1 ⟨by norm_num,le_rfl⟩
  have hplus : ‖exp (I*z)‖ ≤ Real.exp H := by
    simpa only [mul_neg,neg_mul,neg_neg,Complex.ofReal_one,mul_one] using
      norm_exp_neg_I_mul_strip_le (-z) H (by simpa using hzH) 1 ⟨by norm_num,le_rfl⟩
  have hinc' := hinc ab hab a b ha hb hpa hpb hca hcb z
  have hP : ‖P‖ ≤ (Real.exp H*L)*‖w‖^(N+1) := by
    dsimp only [P]
    rw [nlsWKBDiagonalPhasePrimitive_one_eq_phase_increment,norm_mul,norm_neg]
    exact (mul_le_mul hminus hinc' (norm_nonneg _) (by positivity)).trans_eq (by ring)
  have hQeq : Q = exp (I*z)*(nlsHamiltonianPhase a b (N+1) z-nlsHamiltonianPhase a b N z) := by
    dsimp only [Q]
    rw [nlsWKBDiagonalPhasePrimitive_one_eq_phase_increment,
      nlsHamiltonianPhase_signedSwap a b ha hb hpa hpb,
      nlsHamiltonianPhase_signedSwap a b ha hb hpa hpb]
    simp only [mul_neg]
    ring
  have hQ : ‖Q‖ ≤ (Real.exp H*L)*‖w‖^(N+1) := by
    rw [hQeq,norm_mul]
    exact (mul_le_mul hplus hinc' (norm_nonneg _) (by positivity)).trans_eq (by ring)
  have hE : ‖E‖ ≤ T*‖w‖^(N+2) := htaylor ab hab a b ha hb hpa hpb hca hcb z hz hzH
  change ‖(1+p*q-η*(p+q))*E+p*(η-q)*P+q*(p-η)*Q‖ ≤ _
  calc
    _ ≤ ‖(1+p*q-η*(p+q))*E‖+‖p*(η-q)*P‖+‖q*(p-η)*Q‖ := by
      linarith [norm_add_le ((1+p*q-η*(p+q))*E) (p*(η-q)*P),
        norm_add_le ((1+p*q-η*(p+q))*E+p*(η-q)*P) (q*(p-η)*Q)]
    _ = ‖1+p*q-η*(p+q)‖*‖E‖+‖p‖*‖η-q‖*‖P‖+‖q‖*‖p-η‖*‖Q‖ := by simp only [norm_mul]
    _ ≤ (1+B)^2*(T*‖w‖^(N+2))+
        (B*‖w‖)*(1+B)*((Real.exp H*L)*‖w‖^(N+1))+
        (B*‖w‖)*(1+B)*((Real.exp H*L)*‖w‖^(N+1)) := by
      gcongr
    _ = _ := by simp only [pow_add,pow_one]; ring

/-- The scalar correction to the separated next Hamiltonian phase has an H^(N+1)
tail, uniformly on original Hs balls and at every larger cutoff. -/
theorem exists_uniform_nlsWKB_next_separated_correction_fourier_tail_bound_of_bounded_displacement
    (s N : ℕ) (hs : 1 ≤ s) (hNs : N ≤ s) (R D : ℝ) (hR : 0 ≤ R) (hD : 0 ≤ D) :
    ∃ K : ℕ, 0 < K ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ K' : ℕ, K ≤ K' → ∀ ab : SobolevSource s, ‖ab‖ ≤ R → ∀ a b : ℝ → ℂ,
      ContDiff ℝ ∞ a → ContDiff ℝ ∞ b →
      Function.Periodic a 1 → Function.Periodic b 1 →
      (∀ j, ab.1.val j = periodOneCoefficient a j) →
      (∀ j, ab.2.val j = periodOneCoefficient b j) →
      ∀ δ : NLS.Coeff ⊤, ‖δ‖ ≤ D → ∀ θ : BoundaryCondition,
      ∃ f : ScalarSobolev (N+1),
        (∀ n, f.val n = if K' ≤ n.natAbs then
          nlsWKBNextSeparatedCorrectionError θ a b N ((Real.pi:ℂ)*n+δ n) else 0) ∧ ‖f‖ ≤ C := by
  classical
  obtain ⟨K,hK,hcut⟩ := exists_wkb_bounded_frequency_cutoff D hD
  obtain ⟨C,hC,herr⟩ := exists_uniform_nlsWKB_next_separated_correction_error_bound s N hs hNs R hR D
  refine ⟨K,hK,2*C,by positivity,?_⟩
  intro K' hK' ab hab a b ha hb hpa hpb hca hcb δ hδD θ
  let ν (n : ℤ) := (Real.pi:ℂ)*n+δ n
  let F (n : ℤ) := if K' ≤ n.natAbs then nlsWKBNextSeparatedCorrectionError θ a b N (ν n) else 0
  have hδ (n : ℤ) : ‖δ n‖ ≤ D := (lp.norm_apply_le_norm (by simp) δ n).trans hδD
  have hF (n : ℤ) : (1+|(n:ℝ)|)^((N+1)+1)*‖F n‖ ≤ C := by
    by_cases hn : K' ≤ n.natAbs
    · have hgeom := (hcut δ hδ n (hK'.trans hn)).2
      change 1+|(n:ℝ)| ≤ ‖ν n‖ at hgeom
      have hz : 1 ≤ ‖ν n‖ := by linarith [abs_nonneg (n:ℝ)]
      have hzD : |(ν n).im| ≤ D := by
        have he : (ν n).im = (δ n).im := by simp [ν,Complex.mul_im]
        rw [he]
        exact (Complex.abs_im_le_norm _).trans (hδ n)
      have hbnd := herr ab hab a b ha hb hpa hpb hca hcb (ν n) hz hzD θ
      have hw : (1+|(n:ℝ)|)*‖(2*I*ν n)⁻¹‖ ≤ 1 := by
        simp only [norm_inv,norm_mul,norm_ofNat,norm_I,mul_one]
        rw [← div_eq_mul_inv]
        apply (div_le_one (by linarith : 0 < 2*‖ν n‖)).mpr
        linarith
      have hp := pow_le_pow_left₀ (by positivity) hw (N+2)
      rw [mul_pow,one_pow] at hp
      simp only [F,if_pos hn]
      calc
        _ ≤ (1+|(n:ℝ)|)^(N+2)*(C*‖(2*I*ν n)⁻¹‖^(N+2)) :=
          mul_le_mul_of_nonneg_left hbnd (by positivity)
        _ = C*((1+|(n:ℝ)|)^(N+2)*‖(2*I*ν n)⁻¹‖^(N+2)) := by ring
        _ ≤ C*1 := mul_le_mul_of_nonneg_left hp hC
        _ = C := mul_one C
    · simpa only [F,if_neg hn,norm_zero,mul_zero] using hC
  exact WeightedCoeff.exists_sobolev_coeff_of_inverse_power_bound (N+1) F C hC hF

end NLS.ZakharovShabat
