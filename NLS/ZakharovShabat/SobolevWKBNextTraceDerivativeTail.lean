import NLS.SequenceSpaces.WeightedCauchyDerivative
import NLS.ZakharovShabat.SobolevWKBNextTraceTail
import NLS.ZakharovShabat.ClassicalMonodromyAnalytic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! # Spectral derivatives of the next-phase trace error

Fixed-radius Cauchy estimates preserve the sharp Sobolev trace tail under spectral differentiation.
-/

noncomputable section
open Set Complex Metric NLS.Fourier
open scoped ContDiff ENNReal
namespace NLS.ZakharovShabat

/-- The finite classical Hamiltonian phase is analytic off zero. -/
theorem analyticAt_nlsHamiltonianPhase_spectral
    (a b : ℝ → ℂ) (N : ℕ) (z : ℂ) (hz : z ≠ 0) :
    AnalyticAt ℂ (nlsHamiltonianPhase a b N) z := by
  apply (analyticAt_const.mul analyticAt_id).add
  exact Finset.analyticAt_fun_sum (Finset.range N) (fun k _ =>
    analyticAt_const.div ((analyticAt_const.mul analyticAt_id).pow (k+1))
      (pow_ne_zero _ (mul_ne_zero (by norm_num) hz)))

/-- The actual classical discriminant error is analytic off the phase pole. -/
theorem analyticAt_classicalHamiltonianTrace_error
    (a b : ℝ → ℂ) (ha : Continuous a) (hb : Continuous b) (N : ℕ) (z : ℂ) (hz : z ≠ 0) :
    AnalyticAt ℂ (fun w => classicalDiscriminant (classicalPotentialOfFunctions a b ha hb) w-
      2*cos (I*nlsHamiltonianPhase a b N w)) z := by
  have hd : AnalyticAt ℂ (classicalDiscriminant (classicalPotentialOfFunctions a b ha hb)) z :=
    (analyticOnNhd_classicalDiscriminant_joint
      (z,classicalPotentialOfFunctions a b ha hb) (mem_univ _)).comp
      (f := fun w : ℂ => (w,classicalPotentialOfFunctions a b ha hb))
      (analyticAt_id.prod analyticAt_const)
  exact hd.sub (analyticAt_const.mul (Complex.analyticAt_cos.comp
    (analyticAt_const.mul (analyticAt_nlsHamiltonianPhase_spectral a b N z hz))))

/-- Fixed-radius Cauchy estimates preserve the full H^(s+1) trace tail
under spectral differentiation, uniformly for bounded displacements. -/
theorem exists_uniform_nlsWKB_next_trace_derivative_fourier_tail_bound
    (s : ℕ) (hs : 1 ≤ s) (R D : ℝ) (hR : 0 ≤ R) (hD : 0 ≤ D) :
    ∃ K : ℕ, 0 < K ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ K' : ℕ, K ≤ K' → ∀ ab : SobolevSource s, ‖ab‖ ≤ R → ∀ a b : ℝ → ℂ,
      ∀ ha : ContDiff ℝ ∞ a, ∀ hb : ContDiff ℝ ∞ b,
      Function.Periodic a 1 → Function.Periodic b 1 →
      (∀ j, ab.1.val j = periodOneCoefficient a j) →
      (∀ j, ab.2.val j = periodOneCoefficient b j) →
      ∀ δ : NLS.Coeff ⊤, ‖δ‖ ≤ D →
      ∃ f : ScalarSobolev (s+1),
        (∀ n, f.val n = if K' ≤ n.natAbs then
          deriv (fun z => classicalDiscriminant (classicalPotentialOfFunctions a b ha.continuous hb.continuous) z-
            2*cos (I*nlsHamiltonianPhase a b (s+1) z)) ((Real.pi:ℂ)*n+δ n)
          else 0) ∧ ‖f‖ ≤ C := by
  classical
  obtain ⟨K₀,hK₀,C,hC,htrace⟩ := exists_uniform_nlsWKB_next_trace_fourier_tail_bound_of_bounded_displacement
    s hs R (D+1) hR (by positivity)
  obtain ⟨K₁,_,hcut⟩ := exists_wkb_bounded_frequency_cutoff (D+1) (by positivity)
  refine ⟨max K₀ K₁,hK₀.trans_le (le_max_left _ _),2*C,by positivity,?_⟩
  intro K' hKK' ab hab a b ha hb hpa hpb hca hcb δ hδD
  have hK₀ : K₀ ≤ K' := (le_max_left _ _).trans hKK'
  have hK₁ : K₁ ≤ K' := (le_max_right _ _).trans hKK'
  let ν (n : ℤ) := (Real.pi:ℂ)*n+δ n
  let F (z : ℂ) := classicalDiscriminant (classicalPotentialOfFunctions a b ha.continuous hb.continuous) z-
    2*cos (I*nlsHamiltonianPhase a b (s+1) z)
  let f (ζ : ℂ) (n : ℤ) := if K' ≤ n.natAbs then F (ν n+ζ) else 0
  let shift (ζ : ℂ) : NLS.Coeff ⊤ := ⟨fun n => δ n+ζ,memℓp_infty ⟨‖δ‖+‖ζ‖,by
    rintro _ ⟨n,rfl⟩
    exact (norm_add_le _ _).trans (add_le_add (lp.norm_apply_le_norm (by simp) δ n) le_rfl)⟩⟩
  have hshift (ζ : ℂ) (hζ : ζ ∈ ball (0:ℂ) 1) : ‖shift ζ‖ ≤ D+1 := by
    apply lp.norm_le_of_forall_le (by positivity)
    intro n
    change ‖δ n+ζ‖ ≤ D+1
    have hζn : ‖ζ‖ < 1 := by simpa only [mem_ball,dist_zero_right] using hζ
    exact (norm_add_le _ _).trans (add_le_add
      ((lp.norm_apply_le_norm (by simp) δ n).trans hδD) hζn.le)
  have hnzero (ζ : ℂ) (hζ : ζ ∈ ball (0:ℂ) 1) (n : ℤ) (hn : K' ≤ n.natAbs) : ν n+ζ ≠ 0 := by
    have hh := (hcut (shift ζ) (fun j => (lp.norm_apply_le_norm (by simp) (shift ζ) j).trans (hshift ζ hζ))
      n (hK₁.trans hn)).1
    have hh' : 1 ≤ ‖ν n+ζ‖ := by simpa only [shift,ν,add_assoc] using hh
    exact norm_ne_zero_iff.mp (by linarith)
  have hanalytic (n : ℤ) : AnalyticOnNhd ℂ (fun ζ => f ζ n) (ball 0 1) := by
    intro ζ hζ
    by_cases hn : K' ≤ n.natAbs
    · have hF := analyticAt_classicalHamiltonianTrace_error a b ha.continuous hb.continuous (s+1)
        (ν n+ζ) (hnzero ζ hζ n hn)
      simpa only [f,if_pos hn,F,Function.comp_def] using! hF.comp
        (f := fun w : ℂ => ν n+w) (analyticAt_const.add analyticAt_id)
    · simpa only [f,if_neg hn] using (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (0:ℂ)) ζ)
  have hbound (ζ : ℂ) (hζ : ζ ∈ ball (0:ℂ) 1) :
      ∃ q : ScalarSobolev (s+1), (∀ n, q.val n = f ζ n) ∧ ‖q‖ ≤ C := by
    obtain ⟨q,hq,hqn⟩ := htrace K' hK₀ ab hab a b ha hb hpa hpb hca hcb (shift ζ) (hshift ζ hζ)
    refine ⟨q,?_,hqn⟩
    intro n
    simpa only [f,F,ν,shift,add_assoc] using hq n
  obtain ⟨g,hg,hgn⟩ := WeightedCoeff.exists_deriv_coeff_of_analytic_ball_bound
    (Weight.sobolev ((s+1:ℕ):ℝ)) f 1 C (by norm_num) hanalytic hbound
  refine ⟨g,?_,by simpa only [div_one] using hgn⟩
  intro n
  rw [hg n]
  by_cases hn : K' ≤ n.natAbs
  · simp only [f,if_pos hn]
    have hF := (analyticAt_classicalHamiltonianTrace_error a b ha.continuous hb.continuous (s+1)
      (ν n) (by simpa only [add_zero] using hnzero 0 (mem_ball_self (by norm_num)) n hn)).differentiableAt
    have hd0 : HasDerivAt F (deriv F (ν n)) (ν n+0) := by
      simpa only [add_zero,F] using! hF.hasDerivAt
    have hd := hd0.comp (0:ℂ) ((hasDerivAt_id (0:ℂ)).const_add (ν n))
    simpa only [add_zero,mul_one,F,ν,Function.comp_def] using! hd.deriv
  · simp [f,hn]

end NLS.ZakharovShabat
