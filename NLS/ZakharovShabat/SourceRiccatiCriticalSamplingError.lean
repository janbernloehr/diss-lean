import NLS.ZakharovShabat.SourceCriticalWeightedDisplacement
import NLS.ZakharovShabat.SobolevRiccatiWeightedSampling

/-! # One weighted derivative for critical sampling errors

The actual critical-sampled Riccati density minus its original Fourier coefficients gains one weighted L2 derivative locally near real Hs sources, including N=s.
-/

noncomputable section
open Set Complex MeasureTheory NLS.Fourier
open scoped ContDiff ENNReal
namespace NLS.ZakharovShabat

/-- At the actual canonical critical sequence, the literal sampled
Riccati density minus its original Fourier coefficient has one weighted
L2 derivative, locally uniformly near every real original Hs source.
The top order N=s is included without an additional source derivative. -/
theorem exists_local_sobolevRiccati_critical_sampling_error_bound
    (s N : ℕ) (hs : 1 ≤ s) (hNs : N ≤ s)
    (a₀ : realTypeHigherSobolevSourceLocus s) :
    ∃ U : Set (SobolevSource s), IsOpen U ∧ a₀.val ∈ U ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ ab ∈ U, ∀ a b : ℝ → ℂ,
      ContDiff ℝ ∞ a → ContDiff ℝ ∞ b →
      Function.Periodic a 1 → Function.Periodic b 1 →
      (∀ j, ab.1.val j = periodOneCoefficient a j) →
      (∀ j, ab.2.val j = periodOneCoefficient b j) →
      ∃ e : WeightedCoeff (Weight.sobolev 1) 2,
        (∀ n, e.val n = (∫ x in (0:ℝ)..1, nlsRiccatiDensity a b N x*
          exp (-2*I*canonicalCriticalPoints (by norm_num) (by norm_num)
            (periodOnePotential (higherSobolevSourceInclusion s ab))
            (periodOnePotential_mem _) n*x))-
          (sobolevRiccatiDensity s ab N hNs).val n) ∧ ‖e‖ ≤ C := by
  obtain ⟨U,hU,haU,R,D,M,hR,hD,hM,hdata⟩ :=
    exists_local_higherSobolev_critical_weighted_displacement_bounds s hs a₀
  obtain ⟨C,hC,h⟩ := exists_uniform_sobolevRiccati_weighted_sampling_error_bound
    s N hNs R hR D M hM (Weight.sobolev 1)
  refine ⟨U,hU,haU,C,hC,?_⟩
  intro ab hab a b ha hb hpa hpb hca hcb
  obtain ⟨habR,habD,habM⟩ := hdata ab hab
  let δ₂ := sourceCriticalDisplacement (by norm_num) (by norm_num) (higherSobolevSourceInclusion s ab)
  let δ : NLS.Coeff ⊤ := Coeff.exponentInclusion (by simp : (2:ℝ≥0∞) ≤ ⊤) δ₂
  have hδD : ‖δ‖ ≤ D := (Coeff.norm_exponentInclusion_le _ δ₂).trans habD
  have hδM (n : ℤ) : Weight.sobolev 1 n*‖δ n‖ ≤ M := by
    simpa only [Weight.sobolev_apply,Real.rpow_one,δ,Coeff.exponentInclusion_apply] using habM n
  obtain ⟨e,he,hn⟩ := h ab habR a b ha hb hpa hpb hca hcb δ hδD hδM
  refine ⟨e,?_,hn⟩
  intro n
  have hcancel (z : ℂ) : (Real.pi:ℂ)*n+(z-(Real.pi:ℂ)*n) = z := by ring
  simpa only [δ,Coeff.exponentInclusion_apply,δ₂,sourceCriticalDisplacement,canonicalCriticalDisplacement_apply,hcancel] using he n

end NLS.ZakharovShabat
