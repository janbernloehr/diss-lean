import NLS.ZakharovShabat.SourceDirichletCriticalFourierSmoothTail
import NLS.ZakharovShabat.SourceCriticalMidpointSobolevAnalytic
import NLS.ZakharovShabat.SourceBirkhoffFourierErrorReduction

/-! # The literal midpoint Fourier tail for smooth sources

Adding the critical-midpoint correction gives the original literal midpoint error on a common tail.
-/

noncomputable section
open Set Complex NLS.Fourier
open scoped ContDiff ENNReal
namespace NLS.ZakharovShabat

/-- The literal midpoint Fourier error has a locally bounded H^(s+1) tail
for matching smooth periodic representatives of the original Hs source. -/
theorem exists_local_source_eta_midpoint_smooth_fourier_tail_bound
    (s : ℕ) (hs : 1 ≤ s) (a₀ : realTypeHigherSobolevSourceLocus s) :
    ∃ U : Set (SobolevSource s), IsOpen U ∧ a₀.val ∈ U ∧
      ∃ K : ℕ, 0 < K ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ ab ∈ U,
      ∀ a b : ℝ → ℂ, ContDiff ℝ ∞ a → ContDiff ℝ ∞ b →
      Function.Periodic a 1 → Function.Periodic b 1 →
      (∀ j, ab.1.val j = periodOneCoefficient a j) →
      (∀ j, ab.2.val j = periodOneCoefficient b j) →
      ∃ f : ScalarSobolev (s+1),
        (∀ n, f.val n = if K ≤ n.natAbs then
          sourceEtaMidpointFourierError (by simp) (by norm_num) (higherSobolevSourceInclusion s ab) n
          else 0) ∧ ‖f‖ ≤ C := by
  obtain ⟨U,hU,haU,K,hK,C,hC,hu⟩ :=
    exists_local_source_dirichlet_critical_smooth_fourier_tail_bound s hs a₀
  obtain ⟨V,hV,haV,D,hD,_,hv⟩ := exists_local_sourceCriticalMidpoint_one_smoothing s hs a₀
  refine ⟨U ∩ V,hU.inter hV,⟨haU,haV⟩,K,hK,C+D,by positivity,?_⟩
  intro ab hab a b ha hb hpa hpb hca hcb
  obtain ⟨e,he,hen⟩ := hu ab hab.1 a b ha hb hpa hpb hca hcb
  obtain ⟨k,hk,hkn⟩ := WeightedCoeff.exists_tail_restriction _
    (sourceCriticalMidpointSobolevRemainder s (s+1) ab) K
  refine ⟨e+k,?_,(norm_add_le e k).trans (add_le_add hen (hkn.trans (hv ab hab.2).1))⟩
  intro n
  rw [WeightedCoeff.add_val,he n,hk n,(hv ab hab.2).2 n]
  by_cases hn : K ≤ n.natAbs
  · simp only [if_pos hn,sourceBoundaryCriticalRootDifference,sourceEtaMidpointFourierError,
      sourceDirichletMidpointDisplacement_apply,sourceStandardRootMidpoint,
      higherSobolevSourceInclusion_fst,higherSobolevSourceInclusion_snd]
    ring
  · simp only [if_neg hn,add_zero]

end NLS.ZakharovShabat
