import NLS.ZakharovShabat.SourceCriticalMidpointSobolevBall
import NLS.ZakharovShabat.SourceDirichletCriticalFourierSobolevBall
import NLS.ZakharovShabat.SourceBirkhoffFourierErrorReduction

/-! # Uniform midpoint Fourier tails for smooth real sources

The literal midpoint Fourier error has a common H^(s+1) tail bound on every real original Hs ball, with matching smooth representatives.
-/

noncomputable section
open Set Complex NLS.Fourier
open scoped ContDiff ENNReal
namespace NLS.ZakharovShabat

/-- The literal midpoint Fourier error has a common H^(s+1) tail bound
on each entire real original Hs ball, for smooth periodic representatives. -/
theorem exists_uniform_real_source_eta_midpoint_smooth_fourier_tail_bound
    (s : ℕ) (hs : 1 ≤ s) (R : ℝ) (hR : 0 ≤ R) :
    ∃ K : ℕ, 0 < K ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ ab : realTypeHigherSobolevSourceLocus s, ‖ab.val‖ ≤ R →
      ∀ a b : ℝ → ℂ, ContDiff ℝ ∞ a → ContDiff ℝ ∞ b →
      Function.Periodic a 1 → Function.Periodic b 1 →
      (∀ j, ab.val.1.val j = periodOneCoefficient a j) →
      (∀ j, ab.val.2.val j = periodOneCoefficient b j) →
      ∃ f : ScalarSobolev (s+1),
        (∀ n, f.val n = if K ≤ n.natAbs then
          sourceEtaMidpointFourierError (by simp) (by norm_num) (higherSobolevSourceInclusion s ab.val) n
          else 0) ∧ ‖f‖ ≤ C := by
  obtain ⟨K,hK,C,hC,hu⟩ :=
    exists_uniform_real_source_dirichlet_critical_smooth_fourier_tail_bound s hs R hR
  obtain ⟨D,hD,hv⟩ := exists_uniform_real_higherSobolev_critical_midpoint_bound s hs R
  refine ⟨K,hK,C+D,by positivity,?_⟩
  intro ab hab a b ha hb hpa hpb hca hcb
  obtain ⟨e,he,hen⟩ := hu ab hab a b ha hb hpa hpb hca hcb
  obtain ⟨k₂,hk₂,hkn₂⟩ := hv ab hab
  have horder : ((s+1:ℕ):ℝ) ≤ ((2*s:ℕ):ℝ) := by exact_mod_cast (show s+1 ≤ 2*s by omega)
  let k₁ : ScalarSobolev (s+1) := WeightedCoeff.sobolevInclusion horder k₂
  obtain ⟨k,hk,hkn⟩ := WeightedCoeff.exists_tail_restriction _ k₁ K
  have hkn' : ‖k‖ ≤ D := hkn.trans ((WeightedCoeff.norm_sobolevInclusion_le horder k₂).trans hkn₂)
  refine ⟨e+k,?_,(norm_add_le e k).trans (add_le_add hen hkn')⟩
  intro n
  rw [WeightedCoeff.add_val,he n,hk n]
  simp only [k₁,WeightedCoeff.sobolevInclusion_apply,hk₂]
  by_cases hn : K ≤ n.natAbs
  · simp only [if_pos hn,sourceBoundaryCriticalRootDifference,sourceEtaMidpointFourierError,
      sourceDirichletMidpointDisplacement_apply,sourceStandardRootMidpoint,
      higherSobolevSourceInclusion_fst,higherSobolevSourceInclusion_snd]
    ring
  · simp only [if_neg hn,add_zero]

end NLS.ZakharovShabat
