import NLS.ZakharovShabat.SobolevWKBBothLeadingFourierTails
import NLS.ZakharovShabat.SourceCriticalWeightedDisplacement

/-! # Both leading Fourier tails at actual canonical roots

The two-column estimate applies to actual boundary and critical sequences near real Sobolev sources, without assuming covariance of canonical labels.
-/

noncomputable section
open Set Complex NLS.Fourier
open scoped ContDiff ENNReal
namespace NLS.ZakharovShabat

/-- Both actual leading WKB integrals at either canonical boundary sequence
have the original Fourier coefficients at their exact signed indices,
with a common locally uniform H^(s+1) tail bound. -/
theorem exists_local_nlsWKB_both_leading_boundary_fourier_tail_error_bound
    (s : ℕ) (hs : 1 ≤ s) (a₀ : realTypeHigherSobolevSourceLocus s) (θ : BoundaryCondition) :
    ∃ U : Set (SobolevSource s), IsOpen U ∧ a₀.val ∈ U ∧
      ∃ K : ℕ, 0 < K ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ ab ∈ U, ∀ a b : ℝ → ℂ, ContDiff ℝ ∞ a → ContDiff ℝ ∞ b →
      Function.Periodic a 1 → Function.Periodic b 1 →
      (∀ j, ab.1.val j = periodOneCoefficient a j) →
      (∀ j, ab.2.val j = periodOneCoefficient b j) →
      ∃ f g : ScalarSobolev (s+1),
        (∀ n, f.val n = if K ≤ n.natAbs then
          nlsWKBLeadingTerm a b s
            (canonicalPeriodOneBoundaryRoots (by norm_num) (by norm_num) θ
              (higherSobolevSourceInclusion s ab) n) 1-
            I*exp (I*((Real.pi:ℂ)*n))*ab.2.val n else 0) ∧
        (∀ n, g.val n = if K ≤ n.natAbs then
          nlsWKBLeadingTerm (-b) (-a) s
            (-(canonicalPeriodOneBoundaryRoots (by norm_num) (by norm_num) θ
              (higherSobolevSourceInclusion s ab) n)) 1+
            I*exp (-I*((Real.pi:ℂ)*n))*ab.1.val (-n) else 0) ∧
        ‖f‖ ≤ C ∧ ‖g‖ ≤ C := by
  obtain ⟨U,hU,haU,R,D,M,hR,hD,hM,hdata⟩ :=
    exists_local_higherSobolev_boundary_weighted_displacement_bounds s hs a₀ θ
  obtain ⟨K,hK,C,hC,h⟩ := exists_uniform_nlsWKB_both_leading_fourier_tail_error_bound s R D M hR hD hM
  refine ⟨U,hU,haU,K,hK,C,hC,?_⟩
  intro ab hab a b ha hb hpa hpb hca hcb
  obtain ⟨habR,habD,habM⟩ := hdata ab hab
  let δ₂ := sourceBoundaryDisplacement (by norm_num) (by norm_num) θ (higherSobolevSourceInclusion s ab)
  let δ : NLS.Coeff ⊤ := Coeff.exponentInclusion (by simp : (2:ℝ≥0∞) ≤ ⊤) δ₂
  have hδD : ‖δ‖ ≤ D := (Coeff.norm_exponentInclusion_le _ δ₂).trans habD
  have hδM (n : ℤ) : (1+|(n:ℝ)|)*‖δ n‖ ≤ M := by
    simpa only [δ,Coeff.exponentInclusion_apply] using habM n
  obtain ⟨f,g,hf,hg,hfn,hgn⟩ := h ab habR a b ha hb hpa hpb hca hcb δ hδD hδM
  have hcancel (n : ℤ) (z : ℂ) : (Real.pi:ℂ)*n+(z-(Real.pi:ℂ)*n) = z := by ring
  refine ⟨f,g,?_,?_,hfn,hgn⟩
  · intro n
    simpa only [δ,Coeff.exponentInclusion_apply,δ₂,sourceBoundaryDisplacement_apply,hcancel] using hf n
  · intro n
    simpa only [δ,Coeff.exponentInclusion_apply,δ₂,sourceBoundaryDisplacement_apply,hcancel] using hg n

/-- Both leading-integral Fourier errors have a common H^(s+1) tail bound
at the actual canonical critical points, with no extra source derivative. -/
theorem exists_local_nlsWKB_both_leading_critical_fourier_tail_error_bound
    (s : ℕ) (hs : 1 ≤ s) (a₀ : realTypeHigherSobolevSourceLocus s) :
    ∃ U : Set (SobolevSource s), IsOpen U ∧ a₀.val ∈ U ∧
      ∃ K : ℕ, 0 < K ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ ab ∈ U, ∀ a b : ℝ → ℂ, ContDiff ℝ ∞ a → ContDiff ℝ ∞ b →
      Function.Periodic a 1 → Function.Periodic b 1 →
      (∀ j, ab.1.val j = periodOneCoefficient a j) →
      (∀ j, ab.2.val j = periodOneCoefficient b j) →
      ∃ f g : ScalarSobolev (s+1),
        (∀ n, f.val n = if K ≤ n.natAbs then
          nlsWKBLeadingTerm a b s
            (canonicalCriticalPoints (by norm_num) (by norm_num)
              (periodOnePotential (higherSobolevSourceInclusion s ab))
              (periodOnePotential_mem _) n) 1-
            I*exp (I*((Real.pi:ℂ)*n))*ab.2.val n else 0) ∧
        (∀ n, g.val n = if K ≤ n.natAbs then
          nlsWKBLeadingTerm (-b) (-a) s
            (-(canonicalCriticalPoints (by norm_num) (by norm_num)
              (periodOnePotential (higherSobolevSourceInclusion s ab))
              (periodOnePotential_mem _) n)) 1+
            I*exp (-I*((Real.pi:ℂ)*n))*ab.1.val (-n) else 0) ∧
        ‖f‖ ≤ C ∧ ‖g‖ ≤ C := by
  obtain ⟨U,hU,haU,R,D,M,hR,hD,hM,hdata⟩ :=
    exists_local_higherSobolev_critical_weighted_displacement_bounds s hs a₀
  obtain ⟨K,hK,C,hC,h⟩ := exists_uniform_nlsWKB_both_leading_fourier_tail_error_bound s R D M hR hD hM
  refine ⟨U,hU,haU,K,hK,C,hC,?_⟩
  intro ab hab a b ha hb hpa hpb hca hcb
  obtain ⟨habR,habD,habM⟩ := hdata ab hab
  let δ₂ := sourceCriticalDisplacement (by norm_num) (by norm_num) (higherSobolevSourceInclusion s ab)
  let δ : NLS.Coeff ⊤ := Coeff.exponentInclusion (by simp : (2:ℝ≥0∞) ≤ ⊤) δ₂
  have hδD : ‖δ‖ ≤ D := (Coeff.norm_exponentInclusion_le _ δ₂).trans habD
  have hδM (n : ℤ) : (1+|(n:ℝ)|)*‖δ n‖ ≤ M := by
    simpa only [δ,Coeff.exponentInclusion_apply] using habM n
  obtain ⟨f,g,hf,hg,hfn,hgn⟩ := h ab habR a b ha hb hpa hpb hca hcb δ hδD hδM
  have hcancel (n : ℤ) (z : ℂ) : (Real.pi:ℂ)*n+(z-(Real.pi:ℂ)*n) = z := by ring
  refine ⟨f,g,?_,?_,hfn,hgn⟩
  · intro n
    simpa only [δ,Coeff.exponentInclusion_apply,δ₂,sourceCriticalDisplacement,
    canonicalCriticalDisplacement_apply,hcancel] using hf n
  · intro n
    simpa only [δ,Coeff.exponentInclusion_apply,δ₂,sourceCriticalDisplacement,
    canonicalCriticalDisplacement_apply,hcancel] using hg n

end NLS.ZakharovShabat
