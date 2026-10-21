import NLS.ZakharovShabat.SourceOmittedBoundarySobolevBall
import NLS.ZakharovShabat.SourceBoundaryAntiFourierSobolevBall
import NLS.ZakharovShabat.SourceEtaSineFourierAnalytic

/-! # Complete terminal-sine Fourier bounds on Sobolev balls

The actual terminal-sine Fourier remainder has a uniform one-order stronger bound on every real positive-integer Sobolev ball.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The complete literal terminal-sine Fourier remainder is uniformly
bounded in h^(s+1) over each entire real original Hs ball. -/
theorem exists_uniform_real_sourceEtaSineFourierRemainder_bound
    (s : ℕ) (hs : 1 ≤ s) (R : ℝ) (hR : 0 ≤ R) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ ab : realTypeHigherSobolevSourceLocus s, ‖ab.val‖ ≤ R →
      ‖sourceEtaSineFourierRemainder s ab.val‖ ≤ B ∧
      ∀ n, (sourceEtaSineFourierRemainder s ab.val).val n =
        sourceEtaSineFourierError (by norm_num) (by norm_num) (higherSobolevSourceInclusion s ab.val) n := by
  obtain ⟨A,hA,hAc⟩ := exists_uniform_real_sourceBoundaryAntiFourierRemainder_bound s hs R hR .dirichlet
  obtain ⟨Q,hQ,hQc⟩ := exists_uniform_real_sourceBoundaryOmittedInverseRemainder_bound s hs R hR .dirichlet
  let J := higherSobolevSourceInclusion s
  let B := ((Q+1)*A+Q*(2*R))/2
  refine ⟨B,by dsimp [B]; positivity,?_⟩
  intro ab hab
  let a := WeightedCoeff.reflection (s:ℝ) ab.val.1-ab.val.2
  have hweights (n : ℤ) : Weight.sobolev ((s:ℝ)+1) n ≤ Weight.sobolev ((s+1:ℕ):ℝ) n := by
    simp only [Nat.cast_add,Nat.cast_one,le_refl]
  let e := WeightedCoeff.inclusionCLM (Weight.sobolev ((s+1:ℕ):ℝ))
    (Weight.sobolev ((s:ℝ)+1)) hweights (sourceBoundaryAntiFourierRemainder s .dirichlet ab.val)
  have heval (n : ℤ) : e.val n = sourceBoundaryAntiFourierError s .dirichlet n ab.val := by
    simp only [e,WeightedCoeff.inclusionCLM_apply]
    exact (hAc ab hab).2 n
  let q := sourceBoundaryOmittedInverseRemainder s .dirichlet ab.val
  let P (n : ℤ) := sourceStandardRootOmittedProduct (by norm_num) (by norm_num) n (J ab.val)
    (canonicalPeriodOneBoundaryRoots (by norm_num) (by norm_num) .dirichlet (J ab.val) n)
  let sign (n : ℤ) := (-1:ℂ)^n.natAbs
  have hsign (n : ℤ) : (sign n)^2 = 1 := by
    dsimp only [sign]
    rw [← pow_mul,mul_comm n.natAbs 2,pow_mul]
    norm_num
  obtain ⟨b,hb,hbn⟩ := WeightedCoeff.exists_sobolev_signed_quotient_remainder
    (s:ℝ) a e P sign hsign (by intro n; simp [sign]) q
    (fun n => (hQc ab hab).2 n)
  have ha : ‖a‖ ≤ 2*R := by
    have habR : ‖ab.val‖ ≤ R := hab
    have ht := norm_sub_le (WeightedCoeff.reflection (s:ℝ) ab.val.1) ab.val.2
    simp only [LinearIsometryEquiv.norm_map] at ht
    exact ht.trans (by linarith [(norm_fst_le ab.val).trans habR,(norm_snd_le ab.val).trans habR])
  have he : ‖e‖ ≤ A := (WeightedCoeff.norm_inclusionCLM_le _ _ hweights
    (sourceBoundaryAntiFourierRemainder s .dirichlet ab.val)).trans (hAc ab hab).1
  have hq : ‖q‖ ≤ Q := (hQc ab hab).1
  have hval (n : ℤ) : b.val n = sourceEtaSineFourierError (by norm_num) (by norm_num) (J ab.val) n := by
    rw [hb n,heval n]
    simpa only [a,WeightedCoeff.sub_val,WeightedCoeff.reflection_apply,
      P,sign,J] using
      (sourceEtaSineFourierError_eq_signed_quotient s ab.val n).symm
  have heq : sourceEtaSineFourierRemainder s ab.val = b := by
    apply WeightedCoeff.ofFunctionOrZero_eq_of_coordinates
    exact hval
  rw [heq]
  refine ⟨hbn.trans ?_,hval⟩
  dsimp only [B]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  exact add_le_add
    (mul_le_mul (add_le_add hq le_rfl) he (norm_nonneg _) (by positivity))
    (mul_le_mul hq ha (norm_nonneg _) hQ)

end NLS.ZakharovShabat
