import NLS.KdV.HillCommonMiuraRatioIdentity
import NLS.KdV.HillL2MiuraActionRatioTail
import NLS.KdV.HillNormalizedAmplitudeSymbols

/-! The GLOBAL canonical normalized action ratio minus one has a
uniform one-order bound BEFORE ALL positive indices on ONE complex
L2 neighborhood of every real source. Both the actual Miura tail
and the finite head are included; global collapsed conventions remain. -/
noncomputable section
open Set Complex NLS.ComplexAnalysis
namespace NLS.KdV

private theorem ratio_bound_of_sqrt_bound (q : PeriodOneHminusOne) (n : ℕ+) (R : ℝ)
    (hb : ‖hillHminusActionRatioSqrt n q‖ ≤ R) :
    ‖hillHminusCanonicalActionRatio n q-1‖ ≤ R^2+1 := by
  have hr : ‖hillHminusCanonicalActionRatio n q‖ ≤ R^2 := by
    rw [← hillHminusActionRatioSqrt_sq,norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hb 2
  exact (norm_sub_le _ _).trans (by rw [norm_one]; linarith)

theorem exists_local_hillL2CanonicalActionRatio_weighted_bound (q : Coeff 2)
    (hr : IsRealPeriodOneHminusOne (periodOneL2Inclusion q)) :
    ∃ U : Set (Coeff 2), IsOpen U ∧ q ∈ U ∧
      (∀ r ∈ U, periodOneL2Inclusion r ∈ hillHminusActionAmplitudeDomain) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ U, ∀ n : ℕ+,
        (1+(n:ℝ))*‖hillHminusCanonicalActionRatio n (periodOneL2Inclusion r)-1‖ ≤ C := by
  obtain ⟨B,hqB⟩ := exists_hillHminusMiuraGapBall (periodOneL2Inclusion q) hr
  obtain ⟨Ni,Vi,hVi,hqVi,_,hi⟩ := B.exists_local_canonicalRatio_Miura_alternative _ hqB hr
  obtain ⟨Ut,hUt,hqUt,_,Nt,T,hT,ht⟩ := B.exists_local_l2Miura_normalizedRatio_tail_bound q hqB hr
  obtain ⟨Va,hVa,hqVa,hVaD,R,_,hb⟩ := exists_local_uniform_hillHminusActionRatioSqrt_inverse_bounds
    (periodOneL2Inclusion q) (real_mem_hillHminusActionAmplitudeDomain _ hr)
  let U := Ut ∩ periodOneL2Inclusion ⁻¹' (Vi ∩ Va)
  let N := max Ni Nt
  let C := T+(1+(N:ℝ))*(R^2+1)
  refine ⟨U,hUt.inter ((hVi.inter hVa).preimage periodOneL2Inclusion.continuous),
    ⟨hqUt,hqVi,hqVa⟩,(fun r hrU => hVaD hrU.2.2),C,by dsimp [C]; positivity,?_⟩
  intro r hrU n
  by_cases hn : N ≤ (n:ℕ)
  · have hNi : Ni ≤ (n:ℕ) := (le_max_left _ _).trans hn
    have hNt : Nt ≤ (n:ℕ) := (le_max_right _ _).trans hn
    have htail : (1+(n:ℝ))*‖hillHminusCanonicalActionRatio n (periodOneL2Inclusion r)-1‖ ≤ T := by
      rcases hi _ hrU.2.1 n hNi with he | he
      · rw [he,sub_self,norm_zero,mul_zero]
        exact hT
      · rw [he]
        exact ht r hrU.1 n hNt
    exact htail.trans (le_add_of_nonneg_right (by positivity))
  · have hnR : (n:ℝ) ≤ (N:ℝ) := by exact_mod_cast (le_of_lt (lt_of_not_ge hn))
    have hhead := ratio_bound_of_sqrt_bound (periodOneL2Inclusion r) n R (hb _ hrU.2.2 n).1
    calc
      _ ≤ (1+(N:ℝ))*(R^2+1) :=
        mul_le_mul (by linarith) hhead (norm_nonneg _) (by positivity)
      _ ≤ C := le_add_of_nonneg_left hT

end NLS.KdV
