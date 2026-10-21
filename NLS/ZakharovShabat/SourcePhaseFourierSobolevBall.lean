import NLS.ZakharovShabat.SourceSpectralDisplacementSobolevBall
import NLS.ZakharovShabat.SourceBoundaryPhaseSmoothTail
import NLS.ZakharovShabat.SourceCriticalPhaseSmoothTail

/-! # Uniform phase Fourier tails on real Sobolev balls

Canonical boundary and critical phase tails have a common stronger-target bound and cutoff on each entire real positive-integer Sobolev ball.
-/

noncomputable section
open Set Complex NLS.Fourier
open scoped ContDiff ENNReal
namespace NLS.ZakharovShabat
open BoundaryCondition

/-- Boundary phase Fourier tails have one bound and one cutoff on each
entire real original Hs ball, for both boundary conditions. -/
theorem exists_uniform_real_source_boundary_phase_fourier_tail_bound
    (s : ℕ) (hs : 1 ≤ s) (R : ℝ) (hR : 0 ≤ R) :
    ∃ K : ℕ, 0 < K ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ K' : ℕ, K ≤ K' →
      ∀ ab : realTypeHigherSobolevSourceLocus s, ‖ab.val‖ ≤ R → ∀ θ : BoundaryCondition,
      ∀ a b : ℝ → ℂ, ContDiff ℝ ∞ a → ContDiff ℝ ∞ b →
      Function.Periodic a 1 → Function.Periodic b 1 →
      (∀ j, ab.val.1.val j = periodOneCoefficient a j) →
      (∀ j, ab.val.2.val j = periodOneCoefficient b j) →
      ∃ f : ScalarSobolev (s+1),
        (∀ n, f.val n = if K' ≤ n.natAbs then
          sourceBoundaryNextPhaseOffset s θ ab.val n+
            (extensionSign θ*I/2)*(ab.val.1.val (-n)+ab.val.2.val n) else 0) ∧ ‖f‖ ≤ C := by
  obtain ⟨D,M,hD,hM,hdisp⟩ := exists_uniform_real_higherSobolev_displacement_envelopes s hs R hR
  obtain ⟨K,hK,C,hC,h⟩ := exists_uniform_boundary_phase_fourier_tail_bound s hs R D M hR hD hM
  refine ⟨K,hK,C,hC,?_⟩
  intro K' hKK' ab hab θ a b ha hb hpa hpb hca hcb
  obtain ⟨habD,habM⟩ := (hdisp ab hab).1 θ
  let δ₂ := sourceBoundaryDisplacement (by norm_num) (by norm_num) θ (higherSobolevSourceInclusion s ab.val)
  let δ : NLS.Coeff ⊤ := Coeff.exponentInclusion (by simp : (2:ℝ≥0∞) ≤ ⊤) δ₂
  have hδD : ‖δ‖ ≤ D := (Coeff.norm_exponentInclusion_le _ δ₂).trans habD
  have hδM (n : ℤ) : (1+|(n:ℝ)|)*‖δ n‖ ≤ M := by
    simpa only [δ,Coeff.exponentInclusion_apply] using habM n
  have hν (n : ℤ) : (Real.pi:ℂ)*n+δ n =
      canonicalPeriodOneBoundaryRoots (by norm_num) (by norm_num) θ (higherSobolevSourceInclusion s ab.val) n := by
    simp only [δ,Coeff.exponentInclusion_apply,δ₂,sourceBoundaryDisplacement_apply]
    ring
  have hroot (n : ℤ) (_ : K' ≤ n.natAbs) : classicalSeparatedCharacteristic θ
      (classicalPotentialOfFunctions a b ha.continuous hb.continuous) ((Real.pi:ℂ)*n+δ n) = 0 := by
    rw [hν n]
    exact classicalSeparatedCharacteristic_higherSobolev_canonicalRoot_eq_zero s hs ab.val a b
      ha.continuous hb.continuous hpa hpb hca hcb θ n
  obtain ⟨f,hf,hfn⟩ := h K' hKK' ab.val hab a b ha hb hpa hpb hca hcb δ hδD hδM θ hroot
  refine ⟨f,?_,hfn⟩
  intro n
  rw [hf n]
  split_ifs with hn
  · rw [hν n]
    simp only [sourceBoundaryNextPhaseOffset,
      sobolevNextHamiltonianPhase_eq_classical s ab.val a b ha hb hpa hpb hca hcb]
  · rfl

/-- Critical phase tails have a common bound on each entire real original
Hs ball, with every larger cutoff allowed. -/
theorem exists_uniform_real_source_critical_phase_fourier_tail_bound
    (s : ℕ) (hs : 1 ≤ s) (R : ℝ) (hR : 0 ≤ R) :
    ∃ K : ℕ, 0 < K ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ K' : ℕ, K ≤ K' →
      ∀ ab : realTypeHigherSobolevSourceLocus s, ‖ab.val‖ ≤ R →
      ∀ a b : ℝ → ℂ, ContDiff ℝ ∞ a → ContDiff ℝ ∞ b →
      Function.Periodic a 1 → Function.Periodic b 1 →
      (∀ j, ab.val.1.val j = periodOneCoefficient a j) →
      (∀ j, ab.val.2.val j = periodOneCoefficient b j) →
      ∃ f : ScalarSobolev (s+1),
        (∀ n, f.val n = if K' ≤ n.natAbs then sourceCriticalNextPhaseOffset s ab.val n else 0) ∧ ‖f‖ ≤ C := by
  obtain ⟨D,M,hD,_,hdisp⟩ := exists_uniform_real_higherSobolev_displacement_envelopes s hs R hR
  obtain ⟨K,hK,C,hC,h⟩ := exists_uniform_nlsWKB_critical_phase_fourier_tail_bound s hs R D M hR hD
  refine ⟨K,hK,C,hC,?_⟩
  intro K' hKK' ab hab a b ha hb hpa hpb hca hcb
  obtain ⟨habD,habM⟩ := (hdisp ab hab).2
  let δ₂ := sourceCriticalDisplacement (by norm_num) (by norm_num) (higherSobolevSourceInclusion s ab.val)
  let δ : NLS.Coeff ⊤ := Coeff.exponentInclusion (by simp : (2:ℝ≥0∞) ≤ ⊤) δ₂
  have hδD : ‖δ‖ ≤ D := (Coeff.norm_exponentInclusion_le _ δ₂).trans habD
  have hδM (n : ℤ) : (1+|(n:ℝ)|)*‖δ n‖ ≤ M := by
    simpa only [δ,Coeff.exponentInclusion_apply] using habM n
  have hν (n : ℤ) : (Real.pi:ℂ)*n+δ n =
      canonicalCriticalPoints (by norm_num) (by norm_num)
        (periodOnePotential (higherSobolevSourceInclusion s ab.val)) (periodOnePotential_mem _) n := by
    simp only [δ,Coeff.exponentInclusion_apply,δ₂,sourceCriticalDisplacement,canonicalCriticalDisplacement_apply]
    ring
  have hdisc : classicalDiscriminant (classicalPotentialOfFunctions a b ha.continuous hb.continuous) =
      canonicalDiscriminant (by norm_num) (periodOnePotential (higherSobolevSourceInclusion s ab.val)) := by
    funext z
    exact (higherSobolev_spectral_functions_eq_classical s hs ab.val a b
      ha.continuous hb.continuous hpa hpb hca hcb z).1.symm
  have hcrit (n : ℤ) (_ : K' ≤ n.natAbs) :
      deriv (classicalDiscriminant (classicalPotentialOfFunctions a b ha.continuous hb.continuous))
        ((Real.pi:ℂ)*n+δ n) = 0 := by
    rw [hdisc,hν n]
    exact canonicalCriticalPoints_is_critical (by norm_num) (by norm_num) _ _ n
  obtain ⟨f,hf,hfn⟩ := h K' hKK' ab.val hab a b ha hb hpa hpb hca hcb δ hδD hδM hcrit
  refine ⟨f,?_,hfn⟩
  intro n
  rw [hf n]
  split_ifs with hn
  · rw [hν n]
    simp only [sourceCriticalNextPhaseOffset,
      sobolevNextHamiltonianPhase_eq_classical s ab.val a b ha hb hpa hpb hca hcb]
  · rfl

end NLS.ZakharovShabat
