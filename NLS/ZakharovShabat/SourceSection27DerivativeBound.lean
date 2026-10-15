import NLS.ZakharovShabat.SourceSection27Actions

/-! # The coefficient-one derivative estimate in Section 27

A freely enlarged frequency cutoff gives a Hamiltonian bound with coefficient
3/2 on the highest action moment. Absorbing a quarter of the scalar derivative
energy then retains coefficient one in the printed pair derivative estimate.
The unweighted mass remainder has one constant before all real sources.
-/
noncomputable section
namespace NLS.ZakharovShabat

/-- An adjustable cutoff preserves a chosen top-moment coefficient in the remainder budget. -/
theorem section27_central_remainder_budget (e : ℕ) (he : 2 ≤ e)
    (P M S T K L : ℝ) (hM : 0 ≤ M) (hMS : M ≤ S) (hT : 0 ≤ T)
    (hK : 0 ≤ K) (hL : 1 ≤ L) (hKL : 2*(6^e*K) ≤ L^e)
    (hP : P^2 ≤ 3*(S+M^2))
    (hinter : L^e*(1+S)^e*S ≤ T+L^(e+2)*(1+S)^(e+2)*M) :
    K*(1+P^2)^e*(S+2*M^2) ≤
      T/2+(L^(e+2)/2+3*(6^e*K))*(1+S)^(2*e+1)*M := by
  let K₀ := (6:ℝ)^e*K
  have hK₀ : 0 ≤ K₀ := by positivity
  let B := 1+S
  have hS : 0 ≤ S := hM.trans hMS
  have hB : 1 ≤ B := by dsimp [B]; linarith
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hM2 : M^2 ≤ B*M := by dsimp [B]; nlinarith
  have hp1 : B^(e+1) ≤ B^(2*e+1) := pow_le_pow_right₀ hB (by omega)
  have hp2 : B^(e+2) ≤ B^(2*e+1) := pow_le_pow_right₀ hB (by omega)
  have hLp : 0 ≤ L^(e+2) := pow_nonneg (zero_le_one.trans hL) _
  change L^e*B^e*S ≤ T+L^(e+2)*B^(e+2)*M at hinter
  change _ ≤ T/2+(L^(e+2)/2+3*K₀)*B^(2*e+1)*M
  by_cases hsmall : M ≤ 1
  · have hbase : 1+P^2 ≤ 6*B := by
      have hsq : M^2 ≤ M := by nlinarith
      dsimp [B]
      nlinarith
    have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ 1+P^2) hbase e
    have hfirst : 2*K₀*(B^e*S) ≤ T+L^(e+2)*(B^(2*e+1)*M) := by
      have hscale := mul_le_mul_of_nonneg_right hKL (by positivity : 0 ≤ B^e*S)
      change 2*K₀*(B^e*S) ≤ L^e*(B^e*S) at hscale
      have hmass := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hp2 hM) hLp
      nlinarith
    have hsecond : B^e*M^2 ≤ B^(2*e+1)*M := by
      have hx := mul_le_mul_of_nonneg_left hM2 (pow_nonneg hB0 e)
      have hm := mul_le_mul_of_nonneg_right hp1 hM
      rw [pow_succ] at hm
      nlinarith
    have hsmallbound : K₀*(B^e*(S+2*M^2)) ≤ T/2+(L^(e+2)/2+3*K₀)*(B^(2*e+1)*M) := by
      have hx := mul_le_mul_of_nonneg_left hsecond hK₀
      have hr : 0 ≤ K₀*(B^(2*e+1)*M) := by positivity
      nlinarith
    calc
      _ ≤ K*(6*B)^e*(S+2*M^2) := by gcongr
      _ = K₀*(B^e*(S+2*M^2)) := by dsimp [K₀]; rw [mul_pow]; ring
      _ ≤ T/2+(L^(e+2)/2+3*K₀)*(B^(2*e+1)*M) := hsmallbound
      _ = _ := by ring
  · have hlarge : 1 ≤ M := le_of_not_ge hsmall
    have hbase : 1+P^2 ≤ 6*B^2 := by dsimp [B]; nlinarith [sq_nonneg (S-M)]
    have henergy : S+2*M^2 ≤ 3*B*M := by
      have hSM := mul_le_mul_of_nonneg_left hlarge hS
      dsimp [B] at *
      nlinarith
    have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 1+P^2) hbase e
    calc
      _ ≤ K*((6*B^2)^e*(3*B*M)) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (mul_le_mul hp henergy (by positivity) (by positivity)) hK
      _ = (3*K₀)*(B^(2*e+1)*M) := by dsimp [K₀]; rw [mul_pow,← pow_mul,pow_succ]; ring
      _ ≤ _ := by
        have hr : 0 ≤ (L^(e+2)/2)*(B^(2*e+1)*M) := by positivity
        nlinarith

/-- The mass remainder can be enlarged while retaining a coefficient 3/2 on the top action sum. -/
theorem exists_sobolevOddHamiltonian_three_halves_action_bound (m : ℕ) (hm : 2 ≤ m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : realTypeHigherSobolevSourceLocus m,
      (sobolevOddHamiltonian m (by omega) a.val).re ≤
        (3/2:ℝ)*(∑' n : ℤ, sourceWeightedActionTerm ⟨higherSobolevSourceInclusion m a.val,a.property⟩ m n)+
        C*(1+∑' n : ℤ, sourceWeightedActionTerm ⟨higherSobolevSourceInclusion m a.val,a.property⟩ 1 n)^(4*m-3)*
          (∑' n : ℤ, sourceWeightedActionTerm ⟨higherSobolevSourceInclusion m a.val,a.property⟩ 0 n) := by
  let e := 2*(m-1)
  let K : ℝ := (16*Real.pi)^e
  let L : ℝ := 1+2*(6^e*K)
  have he : 2 ≤ e := by dsimp [e]; omega
  have hK : 0 ≤ K := by positivity
  have hL : 1 ≤ L := by dsimp [L]; linarith [show 0 ≤ 2*((6:ℝ)^e*K) by positivity]
  have hKL : 2*((6:ℝ)^e*K) ≤ L^e :=
    (by dsimp [L]; linarith : 2*((6:ℝ)^e*K) ≤ L).trans (le_self_pow₀ hL (by omega))
  refine ⟨L^(e+2)/2+3*(6^e*K),by positivity,?_⟩
  intro a
  have hm1 : 1 ≤ m := by omega
  let ψ : realTypeSourceSubmodule 2 := ⟨higherSobolevSourceInclusion m a.val,a.property⟩
  let M := ∑' n : ℤ, sourceWeightedActionTerm ψ 0 n
  let S := ∑' n : ℤ, sourceWeightedActionTerm ψ 1 n
  let T := ∑' n : ℤ, sourceWeightedActionTerm ψ m n
  let P := ‖sourcePiSobolevCoordinates m 1 hm1 a.val‖
  have hnon (k : ℕ) : 0 ≤ ∑' n : ℤ, sourceWeightedActionTerm ψ k n := by
    apply tsum_nonneg
    intro n
    unfold sourceWeightedActionTerm
    positivity
  have hM : 0 ≤ M := hnon 0
  have hT : 0 ≤ T := hnon m
  have hS : 0 ≤ S := hnon 1
  have hMS : M ≤ S := by
    simpa only [sourceH1RealSource_realHigherSobolevToH1] using
      sourceH1_action_mass_le_weighted (realHigherSobolevToH1 m hm1 a)
  have hP : P^2 ≤ 3*(S+M^2) := by
    have h := sourceH1_third_norm_sq_le_actions (realHigherSobolevToH1 m hm1 a)
    rw [sourceH1RealSource_realHigherSobolevToH1] at h
    change (1/3:ℝ)*‖sourcePhysicalH1Coordinates (higherSobolevToH1 m hm1 a.val)‖^2 ≤ _ at h
    rw [sourcePhysicalH1Coordinates_higherSobolevToH1] at h
    change (1/3:ℝ)*P^2 ≤ S+M^2 at h
    linarith
  have hinter : L^e*(1+S)^e*S ≤ T+L^(e+2)*(1+S)^(e+2)*M := by
    simpa only [mul_pow,show e+2 = 2*m by dsimp [e]; omega] using
      sourceWeightedAction_threshold_comparison m hm1 a (L*(1+S)) (by positivity)
  have hb := section27_central_remainder_budget e he P M S T K L hM hMS hT hK hL hKL hP hinter
  have hham := sobolevOddHamiltonian_le_actions_add_H1_action_remainder m hm1 a
  change (sobolevOddHamiltonian m hm1 a.val).re ≤ T+K*(1+P^2)^e*(S+2*M^2) at hham
  change _ ≤ (3/2:ℝ)*T+(L^(e+2)/2+3*(6^e*K))*(1+S)^(4*m-3)*M
  rw [show 2*e+1 = 4*m-3 by dsimp [e]; omega] at hb
  linarith

/-- The printed coefficient one on the top action sum in the derivative estimate. -/
theorem exists_sobolev_highestJet_action_bound (m : ℕ) (hm : 2 ≤ m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : realTypeHigherSobolevSourceLocus m,
      (1/2:ℝ)*‖hierarchySobolevJetL2 m m le_rfl a.val.1‖^2 ≤
        (∑' n : ℤ, sourceWeightedActionTerm ⟨higherSobolevSourceInclusion m a.val,a.property⟩ m n)+
        C*(1+∑' n : ℤ, sourceWeightedActionTerm ⟨higherSobolevSourceInclusion m a.val,a.property⟩ 1 n)^(4*m-3)*
          (∑' n : ℤ, sourceWeightedActionTerm ⟨higherSobolevSourceInclusion m a.val,a.property⟩ 0 n) := by
  have hm1 : 1 ≤ m := by omega
  obtain ⟨H,hH,hham⟩ := exists_sobolevOddHamiltonian_three_halves_action_bound m hm
  obtain ⟨E,hE,hrem⟩ := exists_sobolevOddHamiltonian_energy_estimates m hm1 (1/4) (by norm_num)
  refine ⟨(2/3:ℝ)*(H+2*E),by positivity,?_⟩
  intro a
  let ψ : realTypeSourceSubmodule 2 := ⟨higherSobolevSourceInclusion m a.val,a.property⟩
  let M := ∑' n : ℤ, sourceWeightedActionTerm ψ 0 n
  let S := ∑' n : ℤ, sourceWeightedActionTerm ψ 1 n
  let R := (1+S)^(4*m-3)*M
  let A := ‖WeightedCoeff.sobolevToL2 (Nat.cast_nonneg m) a.val.1‖
  have hM : 0 ≤ M := by
    apply tsum_nonneg
    intro n
    unfold sourceWeightedActionTerm
    positivity
  have hMS : M ≤ S := by
    simpa only [sourceH1RealSource_realHigherSobolevToH1] using
      sourceH1_action_mass_le_weighted (realHigherSobolevToH1 m hm1 a)
  have hS : 0 ≤ S := hM.trans hMS
  have hmass : M = A^2 := sourceHigher_sum_actions_eq_scalar_mass m hm1 a
  have hone : 1 ≤ (1+S)^(4*m-3) := one_le_pow₀ (by linarith)
  have hpow : M^(2*m) ≤ (1+S)^(4*m-3) :=
    (pow_le_pow_left₀ hM (by linarith : M ≤ 1+S) (2*m)).trans
      (pow_le_pow_right₀ (by linarith : 1 ≤ 1+S) (by omega))
  have hApow : A^(4*m) = M^(2*m) := by
    rw [hmass,← pow_mul]
    congr 1
    omega
  have herr : (1+A^(4*m))*A^2 ≤ 2*R := by
    rw [hApow,← hmass]
    have hb := mul_le_mul_of_nonneg_right (show 1+M^(2*m) ≤ 2*(1+S)^(4*m-3) by linarith) hM
    dsimp [R]
    nlinarith
  have hr := (abs_le.mp (hrem a).1).1
  have hh := hham a
  have he := mul_le_mul_of_nonneg_left herr hE
  change -(1/4*‖hierarchySobolevJetL2 m m le_rfl a.val.1‖^2+E*(1+A^(4*m))*A^2) ≤
    (sobolevOddHamiltonian m hm1 a.val).re-‖hierarchySobolevJetL2 m m le_rfl a.val.1‖^2 at hr
  dsimp [R,S,M,ψ] at he
  dsimp [A] at hr he
  nlinarith

/-- The last displayed estimate in the proof of Theorem 23.2(ii), with its literal factor 1/4. -/
theorem exists_sourceSection27_derivative_bound (m : ℕ) (hm : 2 ≤ m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : realTypeHigherSobolevSourceLocus m,
      (1/4:ℝ)*(‖hierarchySobolevJetL2 m m le_rfl a.val.1‖^2+
        ‖hierarchySobolevJetL2 m m le_rfl a.val.2‖^2) ≤
        (∑' n : ℤ, sourceIndexedWeightedActionTerm ⟨higherSobolevSourceInclusion m a.val,a.property⟩ m n)+
        C*(1+∑' n : ℤ, sourceIndexedWeightedActionTerm ⟨higherSobolevSourceInclusion m a.val,a.property⟩ 1 n)^(4*m-3)*
          (∑' n : ℤ, sourceIndexedWeightedActionTerm ⟨higherSobolevSourceInclusion m a.val,a.property⟩ 0 n) := by
  obtain ⟨C,hC,hbound⟩ := exists_sobolev_highestJet_action_bound m hm
  refine ⟨C,hC,?_⟩
  intro a
  simp only [sourceIndexedWeightedActionTerm_eq]
  have hj := sourceSection27_pair_jet_norm m a
  have hb := hbound a
  linarith

end NLS.ZakharovShabat
