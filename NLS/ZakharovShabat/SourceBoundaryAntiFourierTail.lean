import NLS.ZakharovShabat.SobolevBoundaryAntiFourierTail
import NLS.ZakharovShabat.SourceBoundaryWeightedDisplacement
import NLS.ZakharovShabat.SourceSobolevClassicalCompatibility

/-! # Canonical source boundary roots and the Fourier tail

Exact source compatibility transfers the physical boundary estimate to the canonical roots on an original Hs neighborhood.
-/

noncomputable section
open Set Complex NLS.Fourier
open scoped ContDiff ENNReal
namespace NLS.ZakharovShabat

/-- The actual source anti-discriminant at either canonical boundary
sequence has its original signed Fourier coefficients with a locally
uniform H^(s+1) tail near every real Sobolev source. -/
theorem exists_local_source_boundary_anti_fourier_tail_bound
    (s : ℕ) (hs : 1 ≤ s) (a₀ : realTypeHigherSobolevSourceLocus s) (θ : BoundaryCondition) :
    ∃ U : Set (SobolevSource s), IsOpen U ∧ a₀.val ∈ U ∧
      ∃ K : ℕ, 0 < K ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ ab ∈ U, ∀ a b : ℝ → ℂ, ContDiff ℝ ∞ a → ContDiff ℝ ∞ b →
      Function.Periodic a 1 → Function.Periodic b 1 →
      (∀ j, ab.1.val j = periodOneCoefficient a j) →
      (∀ j, ab.2.val j = periodOneCoefficient b j) →
      ∃ f : ScalarSobolev (s+1),
        (∀ n, f.val n = if K ≤ n.natAbs then
          sourceAntiDiscriminantCandidate (by norm_num) (by norm_num)
            (higherSobolevSourceInclusion s ab)
            (canonicalPeriodOneBoundaryRoots (by norm_num) (by norm_num) θ
              (higherSobolevSourceInclusion s ab) n)+
            I*exp (I*((Real.pi:ℂ)*n))*ab.2.val n-I*exp (-I*((Real.pi:ℂ)*n))*ab.1.val (-n)
          else 0) ∧ ‖f‖ ≤ C := by
  obtain ⟨U,hU,haU,R,D,M,hR,hD,hM,hdata⟩ :=
    exists_local_higherSobolev_boundary_weighted_displacement_bounds s hs a₀ θ
  obtain ⟨K,hK,C,hC,h⟩ := exists_uniform_boundary_anti_fourier_tail_bound s hs R D M hR hD hM
  refine ⟨U,hU,haU,K,hK,C,hC,?_⟩
  intro ab hab a b ha hb hpa hpb hca hcb
  obtain ⟨habR,habD,habM⟩ := hdata ab hab
  let δ₂ := sourceBoundaryDisplacement (by norm_num) (by norm_num) θ (higherSobolevSourceInclusion s ab)
  let δ : NLS.Coeff ⊤ := Coeff.exponentInclusion (by simp : (2:ℝ≥0∞) ≤ ⊤) δ₂
  have hδD : ‖δ‖ ≤ D := (Coeff.norm_exponentInclusion_le _ δ₂).trans habD
  have hδM (n : ℤ) : (1+|(n:ℝ)|)*‖δ n‖ ≤ M := by
    simpa only [δ,Coeff.exponentInclusion_apply] using habM n
  have hν (n : ℤ) : (Real.pi:ℂ)*n+δ n =
      canonicalPeriodOneBoundaryRoots (by norm_num) (by norm_num) θ (higherSobolevSourceInclusion s ab) n := by
    simp only [δ,Coeff.exponentInclusion_apply,δ₂,sourceBoundaryDisplacement_apply]
    ring
  have hroot (n : ℤ) (_ : K ≤ n.natAbs) : classicalSeparatedCharacteristic θ
      (classicalPotentialOfFunctions a b ha.continuous hb.continuous) ((Real.pi:ℂ)*n+δ n) = 0 := by
    rw [hν n]
    exact classicalSeparatedCharacteristic_higherSobolev_canonicalRoot_eq_zero s hs ab a b
      ha.continuous hb.continuous hpa hpb hca hcb θ n
  obtain ⟨f,hf,hfn⟩ := h K le_rfl ab habR a b ha hb hpa hpb hca hcb δ hδD hδM θ hroot
  refine ⟨f,?_,hfn⟩
  intro n
  rw [hf n]
  split_ifs with hn
  · rw [hν n,← (higherSobolev_spectral_functions_eq_classical s hs ab a b ha.continuous hb.continuous hpa hpb hca hcb _).2.1]
  · rfl

end NLS.ZakharovShabat
