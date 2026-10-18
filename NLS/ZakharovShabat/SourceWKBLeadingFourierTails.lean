import NLS.ZakharovShabat.SobolevWKBLeadingFourierTail
import NLS.ZakharovShabat.SourceCriticalWeightedDisplacement

/-! # Leading WKB Fourier tails at canonical spectral points

The sharp estimate for the explicit leading integral applies to actual boundary and critical sequences near real original Hs sources. It does not estimate the full WKB solution remainder.
-/

noncomputable section
open Set Complex NLS.Fourier
open scoped ContDiff ENNReal
namespace NLS.ZakharovShabat

/-- The actual leading WKB integral at either canonical boundary sequence
has its original second Fourier coefficient as leading term, with a locally
uniform H^(s+1) tail error on complex neighborhoods near real Hs sources. -/
theorem exists_local_nlsWKBLeadingTerm_boundary_fourier_tail_error_bound
    (s : ℕ) (hs : 1 ≤ s) (a₀ : realTypeHigherSobolevSourceLocus s) (θ : BoundaryCondition) :
    ∃ U : Set (SobolevSource s), IsOpen U ∧ a₀.val ∈ U ∧
      ∃ K : ℕ, 0 < K ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ ab ∈ U, ∀ a b : ℝ → ℂ, ContDiff ℝ ∞ a → ContDiff ℝ ∞ b →
      Function.Periodic a 1 → Function.Periodic b 1 →
      (∀ j, ab.1.val j = periodOneCoefficient a j) →
      (∀ j, ab.2.val j = periodOneCoefficient b j) →
      ∃ f : ScalarSobolev (s+1),
        (∀ n, f.val n = if K ≤ n.natAbs then
          nlsWKBLeadingTerm a b s
            (canonicalPeriodOneBoundaryRoots (by norm_num) (by norm_num) θ
              (higherSobolevSourceInclusion s ab) n) 1-
            I*exp (I*((Real.pi:ℂ)*n))*ab.2.val n else 0) ∧ ‖f‖ ≤ C := by
  obtain ⟨U,hU,haU,R,D,M,hR,hD,hM,hdata⟩ :=
    exists_local_higherSobolev_boundary_weighted_displacement_bounds s hs a₀ θ
  obtain ⟨K,hK,C,hC,h⟩ := exists_uniform_nlsWKBLeadingTerm_fourier_tail_error_bound s R D M hR hD hM
  refine ⟨U,hU,haU,K,hK,C,hC,?_⟩
  intro ab hab a b ha hb hpa hpb hca hcb
  obtain ⟨habR,habD,habM⟩ := hdata ab hab
  let δ₂ := sourceBoundaryDisplacement (by norm_num) (by norm_num) θ (higherSobolevSourceInclusion s ab)
  let δ : NLS.Coeff ⊤ := Coeff.exponentInclusion (by simp : (2:ℝ≥0∞) ≤ ⊤) δ₂
  have hδD : ‖δ‖ ≤ D := (Coeff.norm_exponentInclusion_le _ δ₂).trans habD
  have hδM (n : ℤ) : (1+|(n:ℝ)|)*‖δ n‖ ≤ M := by
    simpa only [δ,Coeff.exponentInclusion_apply] using habM n
  obtain ⟨f,hf,hfn⟩ := h ab habR a b ha hb hpa hpb hca hcb δ hδD hδM
  refine ⟨f,?_,hfn⟩
  intro n
  have hcancel (z : ℂ) : (Real.pi:ℂ)*n+(z-(Real.pi:ℂ)*n) = z := by ring
  simpa only [δ,Coeff.exponentInclusion_apply,δ₂,sourceBoundaryDisplacement_apply,hcancel] using hf n

/-- The same sharp leading-term Fourier error holds at the actual canonical
critical points, with the original signed indices and no extra derivative. -/
theorem exists_local_nlsWKBLeadingTerm_critical_fourier_tail_error_bound
    (s : ℕ) (hs : 1 ≤ s) (a₀ : realTypeHigherSobolevSourceLocus s) :
    ∃ U : Set (SobolevSource s), IsOpen U ∧ a₀.val ∈ U ∧
      ∃ K : ℕ, 0 < K ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ ab ∈ U, ∀ a b : ℝ → ℂ, ContDiff ℝ ∞ a → ContDiff ℝ ∞ b →
      Function.Periodic a 1 → Function.Periodic b 1 →
      (∀ j, ab.1.val j = periodOneCoefficient a j) →
      (∀ j, ab.2.val j = periodOneCoefficient b j) →
      ∃ f : ScalarSobolev (s+1),
        (∀ n, f.val n = if K ≤ n.natAbs then
          nlsWKBLeadingTerm a b s
            (canonicalCriticalPoints (by norm_num) (by norm_num)
              (periodOnePotential (higherSobolevSourceInclusion s ab))
              (periodOnePotential_mem _) n) 1-
            I*exp (I*((Real.pi:ℂ)*n))*ab.2.val n else 0) ∧ ‖f‖ ≤ C := by
  obtain ⟨U,hU,haU,R,D,M,hR,hD,hM,hdata⟩ :=
    exists_local_higherSobolev_critical_weighted_displacement_bounds s hs a₀
  obtain ⟨K,hK,C,hC,h⟩ := exists_uniform_nlsWKBLeadingTerm_fourier_tail_error_bound s R D M hR hD hM
  refine ⟨U,hU,haU,K,hK,C,hC,?_⟩
  intro ab hab a b ha hb hpa hpb hca hcb
  obtain ⟨habR,habD,habM⟩ := hdata ab hab
  let δ₂ := sourceCriticalDisplacement (by norm_num) (by norm_num) (higherSobolevSourceInclusion s ab)
  let δ : NLS.Coeff ⊤ := Coeff.exponentInclusion (by simp : (2:ℝ≥0∞) ≤ ⊤) δ₂
  have hδD : ‖δ‖ ≤ D := (Coeff.norm_exponentInclusion_le _ δ₂).trans habD
  have hδM (n : ℤ) : (1+|(n:ℝ)|)*‖δ n‖ ≤ M := by
    simpa only [δ,Coeff.exponentInclusion_apply] using habM n
  obtain ⟨f,hf,hfn⟩ := h ab habR a b ha hb hpa hpb hca hcb δ hδD hδM
  refine ⟨f,?_,hfn⟩
  intro n
  have hcancel (z : ℂ) : (Real.pi:ℂ)*n+(z-(Real.pi:ℂ)*n) = z := by ring
  simpa only [δ,Coeff.exponentInclusion_apply,δ₂,sourceCriticalDisplacement,
    canonicalCriticalDisplacement_apply,hcancel] using hf n

end NLS.ZakharovShabat
