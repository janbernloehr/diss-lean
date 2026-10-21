import NLS.ZakharovShabat.SobolevBoundarySinhFourierTail
import NLS.ZakharovShabat.SobolevNextPhaseOffsetBounds
import NLS.SequenceSpaces.SobolevSinhFourierRemainder
import NLS.ComplexAnalysis.IntegerSinhShift

/-! # The next boundary phase and original Fourier coefficients

The actual next-phase offset at either separated-root sequence has the signed Fourier half-sum with an H^(s+1) tail error.
-/

noncomputable section
open Set Complex NLS.Fourier NLS.ComplexAnalysis
open scoped ContDiff ENNReal
namespace NLS.ZakharovShabat
open BoundaryCondition

/-- The actual next Hamiltonian phase offset at separated roots has the
signed half-sum of the original Fourier coefficients with an H^(s+1) error.
The estimate is uniform on original Hs balls and every larger cutoff. -/
theorem exists_uniform_boundary_phase_fourier_tail_bound
    (s : ℕ) (hs : 1 ≤ s) (R D M : ℝ) (hR : 0 ≤ R) (hD : 0 ≤ D) (hM : 0 ≤ M) :
    ∃ K : ℕ, 0 < K ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ K' : ℕ, K ≤ K' → ∀ ab : SobolevSource s, ‖ab‖ ≤ R → ∀ a b : ℝ → ℂ,
      ∀ ha : ContDiff ℝ ∞ a, ∀ hb : ContDiff ℝ ∞ b,
      Function.Periodic a 1 → Function.Periodic b 1 →
      (∀ j, ab.1.val j = periodOneCoefficient a j) →
      (∀ j, ab.2.val j = periodOneCoefficient b j) →
      ∀ δ : NLS.Coeff ⊤, ‖δ‖ ≤ D →
      (∀ n : ℤ, (1+|(n:ℝ)|)*‖δ n‖ ≤ M) → ∀ θ : BoundaryCondition,
      (∀ n : ℤ, K' ≤ n.natAbs → classicalSeparatedCharacteristic θ
        (classicalPotentialOfFunctions a b ha.continuous hb.continuous) ((Real.pi:ℂ)*n+δ n) = 0) →
      ∃ f : ScalarSobolev (s+1),
        (∀ n, f.val n = if K' ≤ n.natAbs then
          nlsHamiltonianPhase a b (s+1) ((Real.pi:ℂ)*n+δ n)+I*(Real.pi:ℂ)*n+
            (extensionSign θ*I/2)*(ab.1.val (-n)+ab.2.val n)
          else 0) ∧ ‖f‖ ≤ C := by
  classical
  obtain ⟨ε,hε,hlocal⟩ := exists_norm_sinh_inverse_remainder_bound
  obtain ⟨K₀,hK₀,C₀,hC₀,hsine⟩ := exists_uniform_boundary_sinh_fourier_tail_bound s hs R D M hR hD hM
  obtain ⟨K₁,_,A,hA,hoffset⟩ := exists_uniform_nlsHamiltonian_next_phase_offset_bounds s hs R D M hR hD hM
    (min ε 1) (lt_min hε zero_lt_one)
  refine ⟨max K₀ K₁,hK₀.trans_le (le_max_left _ _),(2*A)*(C₀+2*R)+C₀,by positivity,?_⟩
  intro K' hKK' ab hab a b ha hb hpa hpb hca hcb δ hδD hδM θ hroot
  have hK₀ : K₀ ≤ K' := (le_max_left _ _).trans hKK'
  have hK₁ : K₁ ≤ K' := (le_max_right _ _).trans hKK'
  obtain ⟨e,he,hen⟩ := hsine K' hK₀ ab hab a b ha hb hpa hpb hca hcb δ hδD hδM θ hroot
  let σ (n : ℤ) := nlsHamiltonianPhase a b (s+1) ((Real.pi:ℂ)*n+δ n)
  let u (n : ℤ) := if K' ≤ n.natAbs then σ n+I*(Real.pi:ℂ)*n else 0
  let η := extensionSign θ
  let sign (n : ℤ) := exp (I*((Real.pi:ℂ)*n))
  have hsign (n : ℤ) : ‖sign n‖ = 1 := by simp [sign,norm_exp,Complex.mul_re,Complex.mul_im]
  let v := WeightedCoeff.sobolevInclusion (by norm_num : (s:ℝ)+1 ≤ ((s+1:ℕ):ℝ)) e
  have hv (n : ℤ) : v.val n = e.val n := WeightedCoeff.sobolevInclusion_apply _ e n
  obtain ⟨E,hE,hEn⟩ := WeightedCoeff.exists_of_norm_le _ v (fun n => sign n*v.val n) 1 zero_le_one
    (by intro n; simp only [norm_mul,hsign,le_refl])
  have hEbound : ‖E‖ ≤ C₀ := hEn.trans (by
    simpa only [one_mul] using (WeightedCoeff.norm_sobolevInclusion_le _ e).trans hen)
  let b₀ := WeightedCoeff.reflection (s:ℝ) ab.1+ab.2
  let lead (n : ℤ) := if K' ≤ n.natAbs then -(η*I/2)*(ab.1.val (-n)+ab.2.val n) else 0
  have hη : ‖-(η*I/2)‖ ≤ 1 := by cases θ <;> norm_num [η,extensionSign,norm_div]
  obtain ⟨a₀,ha₀,ha₀n⟩ := WeightedCoeff.exists_of_norm_le _ b₀ lead 1 zero_le_one (by
    intro n
    by_cases hn : K' ≤ n.natAbs
    · simp only [lead,if_pos hn,norm_mul,one_mul,b₀,WeightedCoeff.add_val,WeightedCoeff.reflection_apply]
      exact (mul_le_mul_of_nonneg_right hη (norm_nonneg _)).trans_eq (one_mul _)
    · simp only [lead,if_neg hn,norm_zero]
      positivity)
  have ha₀bound : ‖a₀‖ ≤ 2*R := by
    have hb₀ := norm_add_le (WeightedCoeff.reflection (s:ℝ) ab.1) ab.2
    simp only [LinearIsometryEquiv.norm_map] at hb₀
    have hb₀n : ‖b₀‖ ≤ 2*R := hb₀.trans (by linarith [(norm_fst_le ab).trans hab,(norm_snd_le ab).trans hab])
    exact ha₀n.trans (by simpa only [one_mul] using hb₀n)
  have hformula (n : ℤ) : E.val n = sinh (u n)-a₀.val n := by
    rw [hE n,hv n,he n,ha₀ n]
    by_cases hn : K' ≤ n.natAbs
    · simp only [if_pos hn,u,lead,σ,sign,η]
      rw [show I*(Real.pi:ℂ)*n = I*((Real.pi:ℂ)*n) by ring,
        sinh_add_int_pi_I_eq_exp,exp_neg_int_pi_I_eq]
      linear_combination (extensionSign θ*I/2)*(ab.1.val (-n)+ab.2.val n)*exp_int_pi_I_sq n
    · simp [u,lead,hn]
  have hu (n : ℤ) : ‖u n‖ ≤ 1 := by
    by_cases hn : K' ≤ n.natAbs
    · have h := hoffset ab hab a b ha hb hpa hpb hca hcb δ hδD hδM n (hK₁.trans hn)
      exact (show ‖u n‖ < min ε 1 by simpa only [u,if_pos hn,σ] using h.2.2).le.trans (min_le_right _ _)
    · simp [u,hn]
  have hsmall (n : ℤ) : ‖u n‖ ≤ 2*‖sinh (u n)‖ := by
    by_cases hn : K' ≤ n.natAbs
    · have h := hoffset ab hab a b ha hb hpa hpb hca hcb δ hδD hδM n (hK₁.trans hn)
      apply (hlocal (u n) ?_).1
      exact (show ‖u n‖ < min ε 1 by simpa only [u,if_pos hn,σ] using h.2.2).trans_le (min_le_left _ _)
    · simp [u,hn]
  have hdecay (n : ℤ) : (1+|(n:ℝ)|)*‖u n‖ ≤ A := by
    by_cases hn : K' ≤ n.natAbs
    · simpa only [u,if_pos hn,σ] using (hoffset ab hab a b ha hb hpa hpb hca hcb δ hδD hδM n (hK₁.trans hn)).2.1
    · simpa only [u,if_neg hn,norm_zero,mul_zero] using hA
  obtain ⟨f,hf,hfn⟩ := WeightedCoeff.exists_sobolev_sinh_fourier_remainder (s:ℝ) u a₀ E A hA hformula hu hsmall hdecay
  let F : ScalarSobolev (s+1) := WeightedCoeff.sobolevInclusion
    (by norm_num : ((s+1:ℕ):ℝ) ≤ (s:ℝ)+1) f
  refine ⟨F,?_,(WeightedCoeff.norm_sobolevInclusion_le _ f).trans (hfn.trans ?_)⟩
  · intro n
    rw [WeightedCoeff.sobolevInclusion_apply,hf n,ha₀ n]
    by_cases hn : K' ≤ n.natAbs <;> simp [u,lead,σ,η,hn]
  · exact add_le_add (mul_le_mul_of_nonneg_left (add_le_add hEbound ha₀bound) (by positivity)) hEbound

end NLS.ZakharovShabat
