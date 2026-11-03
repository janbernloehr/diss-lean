import NLS.KdV.HillProductFixedPeriods
import NLS.KdV.HminusOneHillPsiProductContinuity

/-! The ACTUAL original Hill zero sequence solves the literal
off-diagonal product period equations on genuine nonempty circles.
The diagonal period is the reciprocal of the actual nonzero scalar;
the universal pi*n/2 value is not assumed. -/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV
namespace HillHminusPsiBall

theorem product_period_entire (B : HillHminusPsiBall) (n m : ℕ+) (q : PeriodOneHminusOne)
    (hq : q ∈ B.source) (hr : IsRealPeriodOneHminusOne q)
    (D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num)
      (hillMiuraDiagonal (B.parent.miuraBall.actionBall.lift q)) ((m:ℕ):ℤ)) :
    AnalyticOnNhd ℂ (hillEnergyProductFixedPeriod n (B.parent.miuraBall.actionBall.shift:ℂ)
      (hillMiuraDiagonal (B.parent.miuraBall.actionBall.lift q)) D) univ := by
  let u : PeriodOneRealL2 := ⟨B.parent.miuraBall.actionBall.lift q,
    B.parent.miuraBall.actionBall.lift_real q (B.subset hq).1 hr⟩
  exact analyticOnNhd_hillEnergyProductFixedPeriod n _ _ (hillMiuraRealSource u).property D

theorem product_period_scalar (B : HillHminusPsiBall) (n m : ℕ+) (q : PeriodOneHminusOne)
    (hq : q ∈ B.source) (hr : IsRealPeriodOneHminusOne q)
    (D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num)
      (hillMiuraDiagonal (B.parent.miuraBall.actionBall.lift q)) ((m:ℕ):ℤ)) :
    hillHminusPsiProductScalar n q hr*
      hillEnergyProductFixedPeriod n (B.parent.miuraBall.actionBall.shift:ℂ)
        (hillMiuraDiagonal (B.parent.miuraBall.actionBall.lift q)) D
        (hillHminusPsiZeroDisplacement n ⟨q,hr⟩) = if m = n then 1 else 0 := by
  let d := hillHminusPsiZeroDisplacement n ⟨q,hr⟩
  let A := hillHminusPsiProductScalar n q hr
  let c : ℂ := B.parent.miuraBall.actionBall.shift
  let ψ := hillMiuraDiagonal (B.parent.miuraBall.actionBall.lift q)
  have hi (z : ℂ) : (2*z*hillHminusCanonicalPsi n (z^2-c,q))/
      sourceCanonicalRoot (by norm_num) (by norm_num) ψ z = A*hillEnergyProductPeriodIntegrand n c ψ (z,d) := by
    rw [hillHminusCanonicalPsi_eq_scalar_mul_literalProduct n (z^2-c) ⟨q,hr⟩]
    change (2*z*(A*hillEnergySequenceProduct n (z^2-c,d)))/
      sourceCanonicalRoot (by norm_num) (by norm_num) ψ z =
      A*((2*z*hillEnergySequenceProduct n (z^2-c,d))/sourceCanonicalRoot (by norm_num) (by norm_num) ψ z)
    ring
  have hp := B.canonical_pullback_period n m q hq D
  change (2*Real.pi:ℂ)⁻¹*(∮ z in C((D.center:ℂ),D.radius),
    (2*z*hillHminusCanonicalPsi n (z^2-c,q))/sourceCanonicalRoot (by norm_num) (by norm_num) ψ z) = _ at hp
  simp_rw [hi] at hp
  rw [circleIntegral.integral_const_mul] at hp
  change A*((2*Real.pi:ℂ)⁻¹*(∮ z in C((D.center:ℂ),D.radius),hillEnergyProductPeriodIntegrand n c ψ (z,d))) = _
  calc
    _ = (2*Real.pi:ℂ)⁻¹*(A*(∮ z in C((D.center:ℂ),D.radius),hillEnergyProductPeriodIntegrand n c ψ (z,d))) := by ring
    _ = _ := hp

theorem product_off_diagonal_period_zero (B : HillHminusPsiBall) (n m : ℕ+) (hmn : m ≠ n)
    (q : PeriodOneHminusOne) (hq : q ∈ B.source) (hr : IsRealPeriodOneHminusOne q)
    (D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num)
      (hillMiuraDiagonal (B.parent.miuraBall.actionBall.lift q)) ((m:ℕ):ℤ)) :
    hillEnergyProductFixedPeriod n (B.parent.miuraBall.actionBall.shift:ℂ)
      (hillMiuraDiagonal (B.parent.miuraBall.actionBall.lift q)) D
      (hillHminusPsiZeroDisplacement n ⟨q,hr⟩) = 0 := by
  have h := B.product_period_scalar n m q hq hr D
  rw [if_neg hmn] at h
  exact (mul_eq_zero.mp h).resolve_left (hillHminusPsiProductScalar_ne_zero n q hr)

theorem product_diagonal_period (B : HillHminusPsiBall) (n : ℕ+)
    (q : PeriodOneHminusOne) (hq : q ∈ B.source) (hr : IsRealPeriodOneHminusOne q)
    (D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num)
      (hillMiuraDiagonal (B.parent.miuraBall.actionBall.lift q)) ((n:ℕ):ℤ)) :
    hillEnergyProductFixedPeriod n (B.parent.miuraBall.actionBall.shift:ℂ)
      (hillMiuraDiagonal (B.parent.miuraBall.actionBall.lift q)) D
      (hillHminusPsiZeroDisplacement n ⟨q,hr⟩) = (hillHminusPsiProductScalar n q hr)⁻¹ := by
  apply mul_left_cancel₀ (hillHminusPsiProductScalar_ne_zero n q hr)
  rw [B.product_period_scalar n n q hq hr D,if_pos rfl,
    mul_inv_cancel₀ (hillHminusPsiProductScalar_ne_zero n q hr)]

end HillHminusPsiBall
end NLS.KdV
