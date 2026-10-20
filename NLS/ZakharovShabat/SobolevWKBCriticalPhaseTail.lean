import NLS.SequenceSpaces.WeightedDomination
import NLS.ZakharovShabat.SobolevHamiltonianNextPhaseDerivative
import NLS.ComplexAnalysis.CriticalPhaseLocalComparison
import NLS.ZakharovShabat.WKBLeadingFrequencyCutoff

/-! # The critical-point next-phase Sobolev tail

The actual critical equation and the trace derivative bound give a full one-derivative gain for the phase offset.
-/

noncomputable section
open Set Complex NLS.Fourier NLS.ComplexAnalysis
open scoped ContDiff ENNReal
namespace NLS.ZakharovShabat

/-- At actual critical frequencies, the next Hamiltonian phase offset
has a uniformly bounded H^(s+1) tail on the original Hs ball. Only
matching smooth representatives and the two displacement budgets are used. -/
theorem exists_uniform_nlsWKB_critical_phase_fourier_tail_bound
    (s : ℕ) (hs : 1 ≤ s) (R D M : ℝ) (hR : 0 ≤ R) (hD : 0 ≤ D) :
    ∃ K : ℕ, 0 < K ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ K' : ℕ, K ≤ K' → ∀ ab : SobolevSource s, ‖ab‖ ≤ R → ∀ a b : ℝ → ℂ,
      ∀ ha : ContDiff ℝ ∞ a, ∀ hb : ContDiff ℝ ∞ b,
      Function.Periodic a 1 → Function.Periodic b 1 →
      (∀ j, ab.1.val j = periodOneCoefficient a j) →
      (∀ j, ab.2.val j = periodOneCoefficient b j) →
      ∀ δ : NLS.Coeff ⊤, ‖δ‖ ≤ D →
      (∀ n : ℤ, (1+|(n:ℝ)|)*‖δ n‖ ≤ M) →
      (∀ n : ℤ, K' ≤ n.natAbs →
        deriv (classicalDiscriminant (classicalPotentialOfFunctions a b ha.continuous hb.continuous))
          ((Real.pi:ℂ)*n+δ n) = 0) →
      ∃ f : ScalarSobolev (s+1),
        (∀ n, f.val n = if K' ≤ n.natAbs then
          nlsHamiltonianPhase a b (s+1) ((Real.pi:ℂ)*n+δ n)+I*(Real.pi:ℂ)*n
          else 0) ∧ ‖f‖ ≤ C := by
  classical
  obtain ⟨K₀,hK₀,C,hC,htrace⟩ := exists_uniform_nlsWKB_next_trace_derivative_fourier_tail_bound s hs R D hR hD
  obtain ⟨K₁,_,hgeom⟩ := exists_wkb_leading_frequency_cutoff D M hD
  obtain ⟨A,hA,hfree⟩ := exists_uniform_nlsHamiltonian_next_phase_free_bound s (s+1) hs le_rfl R hR
  obtain ⟨T,_,hphase⟩ := exists_uniform_nlsHamiltonian_next_phase_derivative_bounds s (s+1) hs le_rfl R hR
  obtain ⟨ε,hε,hlocal⟩ := exists_norm_phase_offset_le_trace_derivative
  obtain ⟨L,hL⟩ := exists_nat_gt ((A+M)/ε)
  obtain ⟨J,hJ⟩ := exists_nat_ge T
  let K := max K₀ (max K₁ (max L J))
  refine ⟨K,hK₀.trans_le (le_max_left _ _),2*C,by positivity,?_⟩
  intro K' hKK' ab hab a b ha hb hpa hpb hca hcb δ hδD hδM hcrit
  have hKs : K₀ ≤ K' ∧ K₁ ≤ K' ∧ L ≤ K' ∧ J ≤ K' := by dsimp only [K] at hKK'; omega
  obtain ⟨q,hq,hqn⟩ := htrace K' hKs.1 ab hab a b ha hb hpa hpb hca hcb δ hδD
  let ν (n : ℤ) := (Real.pi:ℂ)*n+δ n
  let σ (z : ℂ) := nlsHamiltonianPhase a b (s+1) z
  let Φ := classicalPotentialOfFunctions a b ha.continuous hb.continuous
  let u (n : ℤ) := σ (ν n)+I*(Real.pi:ℂ)*n
  let f (n : ℤ) := if K' ≤ n.natAbs then u n else 0
  have hdom (n : ℤ) : ‖f n‖ ≤ 2*‖q.val n‖ := by
    by_cases hn : K' ≤ n.natAbs
    · have hδ (j : ℤ) : ‖δ j‖ ≤ D := (lp.norm_apply_le_norm (by simp) δ j).trans hδD
      have hzgeom := (hgeom δ hδ hδM n (hKs.2.1.trans hn)).2
      change 1+|(n:ℝ)| ≤ ‖ν n‖ at hzgeom
      have hz : 1 ≤ ‖ν n‖ := by linarith [abs_nonneg (n:ℝ)]
      have hz0 : ν n ≠ 0 := norm_ne_zero_iff.mp (by linarith)
      have hw : (1+|(n:ℝ)|)*‖(2*I*ν n)⁻¹‖ ≤ 1 := by
        simp only [norm_inv,norm_mul,norm_ofNat,norm_I,mul_one]
        rw [← div_eq_mul_inv]
        apply (div_le_one (by linarith : 0 < 2*‖ν n‖)).mpr
        linarith
      have hu : ‖u n‖ ≤ A*‖(2*I*ν n)⁻¹‖+‖δ n‖ := by
        have he : u n = (σ (ν n)+I*ν n)-I*δ n := by dsimp [u,ν]; ring
        rw [he]
        exact (norm_sub_le _ _).trans (by
          simpa only [norm_mul,norm_I,one_mul] using
            add_le_add (hfree ab hab a b ha hb hpa hpb hca hcb (ν n) hz) le_rfl)
      have hweighted : (1+|(n:ℝ)|)*‖u n‖ ≤ A+M := by
        calc
          _ ≤ (1+|(n:ℝ)|)*(A*‖(2*I*ν n)⁻¹‖+‖δ n‖) := mul_le_mul_of_nonneg_left hu (by positivity)
          _ = A*((1+|(n:ℝ)|)*‖(2*I*ν n)⁻¹‖)+(1+|(n:ℝ)|)*‖δ n‖ := by ring
          _ ≤ A*1+M := add_le_add (mul_le_mul_of_nonneg_left hw hA) (hδM n)
          _ = A+M := by ring
      have hnL : (L:ℝ) ≤ |(n:ℝ)| := by
        have hh : (L:ℝ) ≤ (n.natAbs:ℝ) := by exact_mod_cast hKs.2.2.1.trans hn
        simpa using hh
      have hsmall : ‖u n‖ < ε := by
        have he := (div_lt_iff₀ hε).mp hL
        nlinarith [abs_nonneg (n:ℝ)]
      have hnJ : (J:ℝ) ≤ |(n:ℝ)| := by
        have hh : (J:ℝ) ≤ (n.natAbs:ℝ) := by exact_mod_cast hKs.2.2.2.trans hn
        simpa using hh
      have hT : T ≤ ‖ν n‖ := by linarith
      have hder := hphase ab hab a b ha hb hpa hpb hca hcb (ν n) hT
      have hlower : (1/2:ℝ) ≤ ‖deriv σ (ν n)‖ := by
        have ht := norm_sub_le (deriv σ (ν n)+I) (deriv σ (ν n))
        simp only [add_sub_cancel_left,norm_I] at ht
        linarith [hder.1]
      have hpoint := hlocal (σ (ν n)) (deriv σ (ν n)) n hsmall hlower
      have hΔ : HasDerivAt (classicalDiscriminant Φ) 0 (ν n) := by
        have hd : AnalyticAt ℂ (classicalDiscriminant Φ) (ν n) :=
          (analyticOnNhd_classicalDiscriminant_joint (ν n,Φ) (mem_univ _)).comp
            (f := fun z : ℂ => (z,Φ)) (analyticAt_id.prod analyticAt_const)
        have h := hd.differentiableAt.hasDerivAt
        simpa only [Φ,ν,hcrit n hn] using h
      have hσ := (analyticAt_nlsHamiltonianPhase_spectral a b (s+1) (ν n) hz0).differentiableAt.hasDerivAt
      have hm : HasDerivAt (fun z => 2*cosh (σ z))
          (2*sinh (σ (ν n))*deriv σ (ν n)) (ν n) := by
        simpa only [σ,mul_assoc,Function.comp_def] using!
          ((hasDerivAt_cosh (σ (ν n))).comp (ν n) hσ).const_mul 2
      have he : deriv (fun z => classicalDiscriminant Φ z-2*cos (I*σ z)) (ν n) =
          -(2*sinh (σ (ν n))*deriv σ (ν n)) := by
        have heq : (fun z => classicalDiscriminant Φ z-2*cos (I*σ z)) =
            (fun z => classicalDiscriminant Φ z-2*cosh (σ z)) := by
          funext z
          rw [mul_comm I,cos_mul_I]
        rw [heq]
        simpa only [zero_sub] using! (hΔ.sub hm).deriv
      have hq' : q.val n = -(2*sinh (σ (ν n))*deriv σ (ν n)) := by
        rw [hq n,if_pos hn]
        exact he
      simp only [f,if_pos hn,hq',norm_neg]
      exact hpoint
    · simp only [f,if_neg hn,norm_zero]
      positivity
  obtain ⟨g,hg,hgn⟩ := WeightedCoeff.exists_of_norm_le (Weight.sobolev ((s+1:ℕ):ℝ)) q f 2 (by norm_num) hdom
  exact ⟨g,hg,hgn.trans (mul_le_mul_of_nonneg_left hqn (by norm_num))⟩

end NLS.ZakharovShabat
