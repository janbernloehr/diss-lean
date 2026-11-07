import NLS.KdV.HillAbelianEnergyQuotient

/-! The filled energy quotient satisfies the SAME original Hill
radicand equation in every Miura patch. Its normalization at branch
points is encoded by analyticity, with no sheet/gap division there. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch

theorem offIndexAbelianEnergyQuotient_equation_at_positive_frequency
    (P : HillProductEquationPatch) (n m : ℕ+) (hmn : m ≠ n)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (z : ℂ) (hz : 0 < z.re)
    (hdisc : z ∈ ball (P.centers ((m:ℕ):ℤ):ℂ) (P.radii ((m:ℕ):ℤ))) :
    hillHminusRadicand q (z^2-(P.parent.parent.miuraBall.actionBall.shift:ℂ))*
        deriv (fun E => P.offIndexAbelianEnergyQuotient n m (E,q)) (z^2-(P.parent.parent.miuraBall.actionBall.shift:ℂ))+
      (deriv (hillHminusRadicand q) (z^2-(P.parent.parent.miuraBall.actionBall.shift:ℂ))/2)*
        P.offIndexAbelianEnergyQuotient n m (z^2-(P.parent.parent.miuraBall.actionBall.shift:ℂ),q) =
      hillHminusCanonicalPsi n (z^2-(P.parent.parent.miuraBall.actionBall.shift:ℂ),q) := by
  let c : ℂ := P.parent.parent.miuraBall.actionBall.shift
  let E := z^2-c
  let H : ℂ → ℂ := fun w => P.offIndexAbelianFilledQuotient n m (w,q)
  let K : ℂ → ℂ := fun w => P.abelianGapRootMultiplier m (w,q)
  let Q := sourceAngularSelectedPolynomial (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ)
  let G : ℂ → ℂ := fun e => P.offIndexAbelianEnergyQuotient n m (e,q)
  have hH := (P.analytic_offIndexAbelianFilledQuotient n m hmn (z,q) ⟨hdisc,hq⟩).comp
    (f := fun w : ℂ => (w,q)) (analyticAt_id.prod analyticAt_const)
  have hK := (P.analytic_abelianGapRootMultiplier m (z,q) ⟨hdisc,hq⟩).comp
    (f := fun w : ℂ => (w,q)) (analyticAt_id.prod analyticAt_const)
  have hQ : HasDerivAt Q (2*(z-sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ))) z :=
    hasDerivAt_quadraticRootPolynomial _ _ z
  have hKe : K z ≠ 0 := P.abelianGapRootMultiplier_ne_zero m (z,q) ⟨hdisc,hq⟩
  have hE : (E,q) ∈ P.abelianFilledEnergyDomain m :=
    P.abelianFilledEnergyDomain_mem_of_positive_frequency m q hq z hz hdisc
  have hG : AnalyticAt ℂ G E := (P.analytic_offIndexAbelianEnergyQuotient n m hmn (E,q) hE).comp
    (f := fun e : ℂ => (e,q)) (analyticAt_id.prod analyticAt_const)
  have hD : AnalyticAt ℂ (hillHminusRadicand q) E := analyticOnNhd_hillHminusRadicand q E (mem_univ _)
  have hquad : Q z*deriv H z+(deriv Q z/2)*H z = P.abelianGapNumerator n m (z,q) := by
    rw [hQ.deriv]
    convert P.offIndexAbelianFilledQuotient_equation n m hmn q hq z hdisc using 1
    dsimp only [Q,H]
    ring
  have hquot := radicand_equation_divide_multiplier Q K H z (P.abelianGapNumerator n m (z,q))
    hQ.differentiableAt hK.differentiableAt hH.differentiableAt hKe hquad
  have hco : (fun w => K w^2*Q w) =ᶠ[𝓝 z] (fun w => hillHminusRadicand q (w^2-c)) := by
    filter_upwards [isOpen_ball.mem_nhds hdisc] with w hw
    exact P.abelianGapRootMultiplier_sq_mul_polynomial m (w,q) ⟨hw,hq⟩
  have hval : K z^2*Q z = hillHminusRadicand q E := hco.eq_of_nhds
  have hquotco : (fun w => H w/K w) =ᶠ[𝓝 z] (fun w => G (w^2-c)) := by
    have hr : {w : ℂ | 0 < w.re} ∈ 𝓝 z :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz
    filter_upwards [hr] with w hw
    exact (P.offIndexAbelianEnergyQuotient_at_positive_frequency n m q w hw).symm
  have hsquare : HasDerivAt (fun w : ℂ => w^2-c) (2*z) z := by
    simpa only [Pi.pow_apply,id_eq,Nat.cast_ofNat,show (2:ℕ)-1 = 1 from rfl,pow_one,mul_one] using
      (((hasDerivAt_id z).pow 2).sub_const c)
  have hdD := hD.differentiableAt.hasDerivAt.comp z hsquare
  have hdG := hG.differentiableAt.hasDerivAt.comp z hsquare
  change HasDerivAt (fun w => hillHminusRadicand q (w^2-c)) _ z at hdD
  change HasDerivAt (fun w => G (w^2-c)) _ z at hdG
  rw [hval,hco.deriv_eq,hdD.deriv,hquotco.deriv_eq,hdG.deriv] at hquot
  have hGval : H z/K z = G E := hquotco.eq_of_nhds
  rw [hGval] at hquot
  have hforce : K z*P.abelianGapNumerator n m (z,q) = 2*z*hillHminusCanonicalPsi n (E,q) := by
    change K z*((2*z*hillHminusCanonicalPsi n (E,q))/K z) = _
    exact mul_div_cancel₀ _ hKe
  rw [hforce] at hquot
  have hzn : z ≠ 0 := by intro he; simp only [he,zero_re,lt_self_iff_false] at hz
  apply (mul_left_cancel₀ (mul_ne_zero (by norm_num : (2:ℂ) ≠ 0) hzn))
  change 2*z*(hillHminusRadicand q E*deriv G E+(deriv (hillHminusRadicand q) E/2)*G E) = 2*z*hillHminusCanonicalPsi n (E,q)
  linear_combination hquot

theorem principal_sqrt_re_pos_of_slit (v : ℂ) (hv : v ∈ slitPlane) : 0 < (Complex.sqrt v).re := by
  have hn := re_sqrt_nonneg v
  by_contra! h
  have he : (Complex.sqrt v).re = 0 := le_antisymm h hn
  have hs := complex_sqrt_sq v
  have hre := congrArg Complex.re hs
  have him := congrArg Complex.im hs
  simp only [pow_two,mul_re,mul_im,he,zero_mul,mul_zero,zero_add] at hre him
  rcases mem_slitPlane_iff.mp hv with hp | hi
  · nlinarith [sq_nonneg (Complex.sqrt v).im]
  · exact hi him.symm

theorem offIndexAbelianEnergyQuotient_equation
    (P : HillProductEquationPatch) (n m : ℕ+) (hmn : m ≠ n)
    (q : PeriodOneHminusOne) (E : ℂ) (ht : (E,q) ∈ P.abelianFilledEnergyDomain m) :
    hillHminusRadicand q E*deriv (fun e => P.offIndexAbelianEnergyQuotient n m (e,q)) E+
      (deriv (hillHminusRadicand q) E/2)*P.offIndexAbelianEnergyQuotient n m (E,q) =
      hillHminusCanonicalPsi n (E,q) := by
  let c : ℂ := P.parent.parent.miuraBall.actionBall.shift
  let z := Complex.sqrt (E+c)
  have hs : z^2-c = E := by dsimp only [z]; rw [complex_sqrt_sq]; ring
  have h := P.offIndexAbelianEnergyQuotient_equation_at_positive_frequency n m hmn q ht.2.2 z
    (principal_sqrt_re_pos_of_slit (E+c) ht.1) ht.2.1
  change hillHminusRadicand q (z^2-c)*deriv (fun e => P.offIndexAbelianEnergyQuotient n m (e,q)) (z^2-c)+
    (deriv (hillHminusRadicand q) (z^2-c)/2)*P.offIndexAbelianEnergyQuotient n m (z^2-c,q) =
      hillHminusCanonicalPsi n (z^2-c,q) at h
  simpa only [hs] using h

end NLS.KdV.HillProductEquationPatch
