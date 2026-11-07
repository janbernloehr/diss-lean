import NLS.KdV.HillFreePeriodResidues

/-! The exact ORIGINAL inverse-index l2 weighting makes the free
Hill period coordinate Jacobian the identity, including the omitted
coordinate. These are period derivatives, not zero-evaluation entries. -/
noncomputable section
open Set Metric Complex NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV

def hillPeriodEquationWeight (n m : ℕ+) : ℂ :=
  (2*Real.pi:ℂ)*((((n:ℕ):ℂ)^2-((m:ℕ):ℂ)^2)/((n:ℕ):ℂ)^2)

theorem pnat_complex_squares_ne {n m : ℕ+} (hnm : n ≠ m) : ((n:ℕ):ℂ)^2 ≠ ((m:ℕ):ℂ)^2 := by
  intro h
  rcases eq_or_eq_neg_of_sq_eq_sq ((n:ℕ):ℂ) ((m:ℕ):ℂ) h with he | he
  · exact hnm (Subtype.ext (Nat.cast_injective he))
  · have hr := congrArg Complex.re he
    simp only [Complex.natCast_re,neg_re] at hr
    have hn : (0:ℝ) < (n:ℕ) := by exact_mod_cast n.pos
    have hm : (0:ℝ) < (m:ℕ) := by exact_mod_cast m.pos
    linarith

theorem hillFree_quadratic_kernel_integrable (m r : ℕ+)
    (D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num) (0:CoeffPair 2) ((m:ℕ):ℤ)) :
    CircleIntegrable (fun z : ℂ => I/(((Real.pi:ℂ)*(r:ℕ))^2-z^2)) (D.center:ℂ) D.radius := by
  apply ContinuousOn.circleIntegrable D.radius_pos.le
  apply ContinuousOn.div continuousOn_const (continuousOn_const.sub (continuousOn_id.pow 2))
  intro z hz
  exact hillFree_energy_denominator_ne_zero r z (D.sphere_subset_rootDomain hz)

theorem hillFree_weighted_period_column (n m r : ℕ+) (hmn : m ≠ n)
    (D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num) (0:CoeffPair 2) ((m:ℕ):ℤ)) :
    hillPeriodEquationWeight n m*hillEnergyProductPeriodColumn n r 0 (0:CoeffPair 2) D 0 =
      if m = r then 1 else 0 := by
  by_cases hrn : r = n
  · subst r
    simp [hillEnergyProductPeriodColumn,hillEnergyProductCoordinateDerivative_omitted,hmn,circleIntegral]
  have hsq := pnat_complex_squares_ne (Ne.symm hrn)
  let A : ℂ := ((Real.pi:ℂ)*(n:ℕ))^2
  let B : ℂ := ((Real.pi:ℂ)*(r:ℕ))^2
  let C : ℂ := ((r:ℕ):ℂ)*A/(A-B)
  have hAB : A-B ≠ 0 := by
    have hpi : (Real.pi:ℂ)^2 ≠ 0 := pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
    have he : A-B = (Real.pi:ℂ)^2*(((n:ℕ):ℂ)^2-((r:ℕ):ℂ)^2) := by dsimp [A,B]; ring
    rw [he]
    exact mul_ne_zero hpi (sub_ne_zero.mpr hsq)
  have hpoint (z : ℂ) (hz : z ∈ sphere (D.center:ℂ) D.radius) :
      (2*z*hillEnergyProductCoordinateDerivative n r (z^2,0))/
        sourceCanonicalRoot (by norm_num) (by norm_num) (0:CoeffPair 2) z =
      C*(I/(B-z^2)-I/(A-z^2)) := by
    have hzdom := D.sphere_subset_rootDomain hz
    have hA : A-z^2 ≠ 0 := hillFree_energy_denominator_ne_zero n z hzdom
    have hB : B-z^2 ≠ 0 := hillFree_energy_denominator_ne_zero r z hzdom
    have hrest := hillEnergyProductCoordinateDerivative_restore n r hrn (z^2) 0
    simp only [hillEnergySequenceZero,lp.coeFn_zero,Pi.zero_apply,mul_zero,add_zero] at hrest
    have hder : hillEnergyProductCoordinateDerivative n r (z^2,0) =
        ((r:ℕ):ℂ)*hillEnergySequenceProduct n (z^2,0)/(B-z^2) :=
      (eq_div_iff hB).mpr ((mul_comm _ _).trans hrest)
    calc
      _ = ((r:ℕ):ℂ)/(B-z^2)*((2*z*hillEnergySequenceProduct n (z^2,0))/
          sourceCanonicalRoot (by norm_num) (by norm_num) (0:CoeffPair 2) z) := by rw [hder]; ring
      _ = ((r:ℕ):ℂ)/(B-z^2)*(I*A/(A-z^2)) := by rw [hillEnergyProductPeriodIntegrand_free n z hzdom]
      _ = C*(I/(B-z^2)-I/(A-z^2)) := by dsimp only [C]; field_simp [hA,hB,hAB]; ring
  unfold hillEnergyProductPeriodColumn
  simp only [sub_zero]
  rw [circleIntegral.integral_congr D.radius_pos.le hpoint,circleIntegral.integral_const_mul,
    circleIntegral.integral_sub (hillFree_quadratic_kernel_integrable m r D) (hillFree_quadratic_kernel_integrable m n D)]
  have hR := hillFree_quadratic_kernel_integral m r D
  have hN := hillFree_quadratic_kernel_integral m n D
  change (∮ z in C((D.center:ℂ),D.radius),I/(B-z^2)) = _ at hR
  change (∮ z in C((D.center:ℂ),D.radius),I/(A-z^2)) = _ at hN
  rw [hR,hN,if_neg hmn,sub_zero]
  by_cases hmr : m = r
  · rw [if_pos hmr,if_pos hmr]
    subst r
    have hpi : (Real.pi:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have hn : ((n:ℕ):ℂ) ≠ 0 := by exact_mod_cast n.ne_zero
    have hm : ((m:ℕ):ℂ) ≠ 0 := by exact_mod_cast m.ne_zero
    have hnm := sub_ne_zero.mpr (pnat_complex_squares_ne (Ne.symm hmn))
    dsimp only [C,A,B,hillPeriodEquationWeight]
    field_simp
  · simp only [if_neg hmr,mul_zero]

def hillFreePeriodEquationRow (n m : ℕ+)
    (D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num) (0:CoeffPair 2) ((m:ℕ):ℤ))
    (d : lp (fun _ : ℕ+ => ℂ) 2) : ℂ :=
  if m = n then d n else hillPeriodEquationWeight n m*hillEnergyProductFixedPeriod n 0 (0:CoeffPair 2) D d

theorem hillFreePeriodEquationRow_zero (n m : ℕ+)
    (D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num) (0:CoeffPair 2) ((m:ℕ):ℤ)) :
    hillFreePeriodEquationRow n m D 0 = 0 := by
  by_cases hmn : m = n
  · simp only [hillFreePeriodEquationRow,if_pos hmn,lp.coeFn_zero,Pi.zero_apply]
  · simp only [hillFreePeriodEquationRow,if_neg hmn,hillEnergyProductFixedPeriod_free,mul_zero]

theorem analyticAt_hillFreePeriodEquationRow (n m : ℕ+)
    (D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num) (0:CoeffPair 2) ((m:ℕ):ℤ))
    (d : lp (fun _ : ℕ+ => ℂ) 2) : AnalyticAt ℂ (hillFreePeriodEquationRow n m D) d := by
  unfold hillFreePeriodEquationRow
  by_cases hmn : m = n
  · simp only [if_pos hmn]
    exact (lp.evalCLM ℂ (fun _ : ℕ+ => ℂ) 2 n).analyticAt d
  · simp only [if_neg hmn]
    exact analyticAt_const.mul (analyticOnNhd_hillEnergyProductFixedPeriod n 0 (0:CoeffPair 2) (by simp) D d (mem_univ _))

theorem hillFreePeriodEquationRow_fderiv_single (n m r : ℕ+)
    (D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num) (0:CoeffPair 2) ((m:ℕ):ℤ)) :
    fderiv ℂ (hillFreePeriodEquationRow n m D) 0 (lp.single 2 r 1) = if m = r then 1 else 0 := by
  by_cases hmn : m = n
  · have he : hillFreePeriodEquationRow n m D = (lp.evalCLM ℂ (fun _ : ℕ+ => ℂ) 2 n) := by
      funext d
      simp only [hillFreePeriodEquationRow,if_pos hmn]
      rfl
    rw [he,ContinuousLinearMap.fderiv]
    subst m
    change (lp.single 2 r 1 : lp (fun _ : ℕ+ => ℂ) 2) n = (if n = r then 1 else 0)
    simp only [lp.single_apply,Pi.single_apply]
  · have he : hillFreePeriodEquationRow n m D = fun d =>
        hillPeriodEquationWeight n m*hillEnergyProductFixedPeriod n 0 (0:CoeffPair 2) D d := by
      funext d; simp only [hillFreePeriodEquationRow,if_neg hmn]
    have hd := ((analyticOnNhd_hillEnergyProductFixedPeriod n 0 (0:CoeffPair 2) (by simp) D 0 (mem_univ _)).differentiableAt.hasFDerivAt).const_mul
      (hillPeriodEquationWeight n m)
    rw [← he] at hd
    rw [hd.fderiv]
    change hillPeriodEquationWeight n m*(fderiv ℂ (hillEnergyProductFixedPeriod n 0 (0:CoeffPair 2) D) 0 (lp.single 2 r 1)) = _
    rw [fderiv_hillEnergyProductFixedPeriod_coordinate n r 0 (0:CoeffPair 2) (by simp) D 0]
    exact hillFree_weighted_period_column n m r hmn D

end NLS.KdV
