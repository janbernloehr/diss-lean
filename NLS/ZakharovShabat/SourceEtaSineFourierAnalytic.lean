import NLS.ZakharovShabat.SourceOmittedBoundaryInverseAnalytic
import NLS.ZakharovShabat.SourceBoundaryAntiFourierAnalytic
import NLS.ZakharovShabat.SourceBirkhoffFourierErrorReduction
import NLS.SequenceSpaces.SobolevSignedQuotientRemainder

/-! # The actual terminal sine Fourier remainder

The omitted-product normalization and anti-discriminant Fourier remainder give an analytic one-derivative gain at every signed index.
-/

noncomputable section
open Set Complex Metric Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The free exponential carrier is the absolute-index parity on both tails. -/
theorem exp_freeCenter_eq_natAbs_sign (n : ℤ) :
    exp (I*((Real.pi:ℂ)*n)) = (-1:ℂ)^n.natAbs := by
  rw [mul_comm I,exp_mul_I,cos_freeCenter_eq_natAbs_sign]
  rw [mul_comm (Real.pi:ℂ),sin_int_mul_pi,zero_mul,add_zero]

/-- The literal terminal sine Fourier error is the signed quotient of
the anti-discriminant remainder and its original Fourier leading term. -/
theorem sourceEtaSineFourierError_eq_signed_quotient
    (s : ℕ) (ab : SobolevSource s) (n : ℤ) :
    sourceEtaSineFourierError (by norm_num) (by norm_num) (higherSobolevSourceInclusion s ab) n =
      (sourceBoundaryAntiFourierError s .dirichlet n ab+
        I*(-1:ℂ)^n.natAbs*(ab.1.val (-n)-ab.2.val n))/
        (2*sourceStandardRootOmittedProduct (by norm_num) (by norm_num) n
          (higherSobolevSourceInclusion s ab)
          (canonicalPeriodOneBoundaryRoots (by norm_num) (by norm_num) .dirichlet
            (higherSobolevSourceInclusion s ab) n))-
        (I/2)*(ab.1.val (-n)-ab.2.val n) := by
  have he : exp (-I*((Real.pi:ℂ)*n)) = (-1:ℂ)^n.natAbs := by
    rw [neg_mul,exp_neg,exp_freeCenter_eq_natAbs_sign,← inv_pow,inv_neg,inv_one]
  simp only [sourceEtaSineFourierError,sourceDirichletEtaSineNumerator,
    sourceBoundaryAntiFourierError,higherSobolevSourceInclusion_fst,
    higherSobolevSourceInclusion_snd,exp_freeCenter_eq_natAbs_sign,he]
  ring

/-- The complete actual terminal sine Fourier error in its sharper Sobolev target. -/
def sourceEtaSineFourierRemainder (s : ℕ) (ab : SobolevSource s) :
    WeightedCoeff (Weight.sobolev ((s:ℝ)+1)) 2 :=
  WeightedCoeff.ofFunctionOrZero (Weight.sobolev ((s:ℝ)+1)) 2
    (fun n => sourceEtaSineFourierError (by norm_num) (by norm_num)
      (higherSobolevSourceInclusion s ab) n)

/-- The literal terminal sine Fourier error gains one derivative
analytically near every real original Hs source, including all central
indices and collapsed gaps, without smooth representatives. -/
theorem exists_local_sourceEtaSineFourierRemainder_analytic
    (s : ℕ) (hs : 1 ≤ s) (a₀ : realTypeHigherSobolevSourceLocus s) :
    ∃ V : Set (SobolevSource s), IsOpen V ∧ a₀.val ∈ V ∧
      ∃ B : ℝ, 0 ≤ B ∧ AnalyticOnNhd ℂ (sourceEtaSineFourierRemainder s) V ∧
        ∀ ab ∈ V, ‖sourceEtaSineFourierRemainder s ab‖ ≤ B ∧
          ∀ n, (sourceEtaSineFourierRemainder s ab).val n =
            sourceEtaSineFourierError (by norm_num) (by norm_num)
              (higherSobolevSourceInclusion s ab) n := by
  obtain ⟨Va,hVa,haVa,A,hA,hAa,hAc⟩ :=
    exists_local_sourceBoundaryAntiFourierRemainder_analytic s hs a₀ .dirichlet
  obtain ⟨Vq,hVq,haVq,Q,hQ,hQa,hQc⟩ :=
    exists_local_sourceBoundaryOmittedInverseRemainder_analytic s hs a₀ .dirichlet
  let J := higherSobolevSourceInclusion s
  obtain ⟨Vp,hVp,haVp,hP⟩ := exists_local_source_omitted_boundary_analytic
    (by norm_num) (by norm_num) (J a₀.val) a₀.property
  let R := ‖a₀.val‖+1
  let U := (Va ∩ Vq) ∩ (J ⁻¹' Vp ∩ ball 0 R)
  have hU : IsOpen U := (hVa.inter hVq).inter ((hVp.preimage J.continuous).inter isOpen_ball)
  have haU : a₀.val ∈ U := ⟨⟨haVa,haVq⟩,haVp,by simp only [mem_ball,dist_zero_right,R]; linarith⟩
  let f (ab : SobolevSource s) (n : ℤ) :=
    sourceEtaSineFourierError (by norm_num) (by norm_num) (J ab) n
  have hf (n : ℤ) : AnalyticOnNhd ℂ (fun ab => f ab n) U := by
    intro ab hab
    have hE : AnalyticAt ℂ (fun x : SobolevSource s => sourceBoundaryAntiFourierError s .dirichlet n x) ab := by
      have he := ((WeightedCoeff.evalCLM _ 2 n).analyticAt _).comp (hAa ab hab.1.1)
      apply he.congr
      filter_upwards [hVa.mem_nhds hab.1.1] with x hx
      exact (hAc x hx).2 n
    have hcoeff : AnalyticAt ℂ (fun x : SobolevSource s => x.1.val (-n)-x.2.val n) ab :=
      (((WeightedCoeff.evalCLM _ 2 (-n)).analyticAt _).comp analyticAt_fst).sub
        (((WeightedCoeff.evalCLM _ 2 n).analyticAt _).comp analyticAt_snd)
    have hp := (hP (J ab) hab.2.1 .dirichlet n).2
    have hformula : AnalyticAt ℂ (fun x : SobolevSource s =>
        (sourceBoundaryAntiFourierError s .dirichlet n x+
          I*(-1:ℂ)^n.natAbs*(x.1.val (-n)-x.2.val n))/
          (2*sourceStandardRootOmittedProduct (by norm_num) (by norm_num) n (J x)
            (canonicalPeriodOneBoundaryRoots (by norm_num) (by norm_num) .dirichlet (J x) n))-
          (I/2)*(x.1.val (-n)-x.2.val n)) ab :=
      ((hE.add (analyticAt_const.mul hcoeff)).div
      (analyticAt_const.mul (hp.1.comp (J.analyticAt ab)))
      (mul_ne_zero (by norm_num) hp.2)).sub (analyticAt_const.mul hcoeff)
    simpa only [f,J,sourceEtaSineFourierError_eq_signed_quotient] using! hformula
  let B := ((Q+1)*A+Q*(2*R))/2
  have hB : 0 ≤ B := by dsimp [B,R]; positivity
  have hfull (ab : SobolevSource s) (hab : ab ∈ U) :
      ∃ b : WeightedCoeff (Weight.sobolev ((s:ℝ)+1)) 2,
        (∀ n, b.val n = f ab n) ∧ ‖b‖ ≤ B := by
    let a := WeightedCoeff.reflection (s:ℝ) ab.1-ab.2
    have hweights (n : ℤ) : Weight.sobolev ((s:ℝ)+1) n ≤ Weight.sobolev ((s+1:ℕ):ℝ) n := by
      simp only [Nat.cast_add,Nat.cast_one,le_refl]
    let e := WeightedCoeff.inclusionCLM (Weight.sobolev ((s+1:ℕ):ℝ))
      (Weight.sobolev ((s:ℝ)+1)) hweights (sourceBoundaryAntiFourierRemainder s .dirichlet ab)
    have heval (n : ℤ) : e.val n = sourceBoundaryAntiFourierError s .dirichlet n ab := by
      simp only [e,WeightedCoeff.inclusionCLM_apply]
      exact (hAc ab hab.1.1).2 n
    let q := sourceBoundaryOmittedInverseRemainder s .dirichlet ab
    let P (n : ℤ) := sourceStandardRootOmittedProduct (by norm_num) (by norm_num) n (J ab)
      (canonicalPeriodOneBoundaryRoots (by norm_num) (by norm_num) .dirichlet (J ab) n)
    let sign (n : ℤ) := (-1:ℂ)^n.natAbs
    have hsign (n : ℤ) : (sign n)^2 = 1 := by
      dsimp only [sign]
      rw [← pow_mul,mul_comm n.natAbs 2,pow_mul]
      norm_num
    obtain ⟨b,hb,hbn⟩ := WeightedCoeff.exists_sobolev_signed_quotient_remainder
      (s:ℝ) a e P sign hsign (by intro n; simp [sign]) q
      (fun n => (hQc ab hab.1.2).2 n)
    have ha : ‖a‖ ≤ 2*R := by
      have habR : ‖ab‖ ≤ R := (show ‖ab‖ < R by simpa only [mem_ball,dist_zero_right] using hab.2.2).le
      have ht := norm_sub_le (WeightedCoeff.reflection (s:ℝ) ab.1) ab.2
      simp only [LinearIsometryEquiv.norm_map] at ht
      exact ht.trans (by linarith [(norm_fst_le ab).trans habR,(norm_snd_le ab).trans habR])
    have he : ‖e‖ ≤ A := (WeightedCoeff.norm_inclusionCLM_le _ _ hweights
      (sourceBoundaryAntiFourierRemainder s .dirichlet ab)).trans (hAc ab hab.1.1).1
    have hq : ‖q‖ ≤ Q := (hQc ab hab.1.2).1
    refine ⟨b,?_,hbn.trans ?_⟩
    · intro n
      rw [hb n,heval n]
      simpa only [a,WeightedCoeff.sub_val,WeightedCoeff.reflection_apply,
        P,sign,f,J] using
        (sourceEtaSineFourierError_eq_signed_quotient s ab n).symm
    · dsimp only [B]
      apply div_le_div_of_nonneg_right _ (by norm_num)
      exact add_le_add
        (mul_le_mul (add_le_add hq le_rfl) he (norm_nonneg _) (by positivity))
        (mul_le_mul hq ha (norm_nonneg _) hQ)
  obtain ⟨han,hval⟩ := WeightedCoeff.analytic_realization_of_bound
    (p := 2) (Weight.sobolev ((s:ℝ)+1)) f hU hf B hfull
  exact ⟨U,hU,haU,B,hB,han,hval⟩

end NLS.ZakharovShabat
