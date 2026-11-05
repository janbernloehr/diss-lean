import NLS.KdV.HillHminusOneIntrinsicDirichletSpectrum
import NLS.KdV.HillHminusOneWeakFormReality

/-! # Reality of intrinsic rough Hill Dirichlet and unitary Floquet energies

Testing with the actual conjugate H1 curve gives a real intrinsic
quadratic form and a nonzero physical L2 mass. Thus weak Dirichlet and
all unit-modulus Floquet energies are real for every real H^-1 potential.
The entire normalized Dirichlet characteristic has no nonreal zeros.
Closed/self-adjoint operator domains and algebraic multiplicities are
not inferred from this weak spectral statement.
-/
noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory Filter Topology
open scoped ComplexConjugate
open NLS.LinearVolterra NLS.ZakharovShabat NLS.FunctionalAnalysis
namespace NLS.KdV

theorem energy_im_zero_of_intrinsic_weak_self_test (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) (lambda : ℂ) (y : Curve ℂ) (hyn : y ≠ 0)
    (hy : AbsolutelyContinuousOnInterval (extend y) 0 1)
    (hy₂ : MemLp (deriv (extend y)) 2 (volume.restrict (Ioc (0 : ℝ) 1)))
    (hend : extend y 1*conj (extend y 1) = extend y 0*conj (extend y 0))
    (hw : hillHminusWeakForm q y (star y) =
      lambda*(∫ s in (0 : ℝ)..1, extend y s*conj (extend y s))) : lambda.im = 0 := by
  let m := ∫ s in (0 : ℝ)..1, extend y s*conj (extend y s)
  have hm : conj m = m := by
    dsimp only [m]
    rw [← intervalIntegral.intervalIntegral_conj]
    apply intervalIntegral.integral_congr
    intro s _
    simp only [map_mul,conj_conj]
    ring
  have hstar := hillHminusWeakForm_star_self q hr y hy hy₂ hend
  rw [hw,map_mul,hm] at hstar
  have hc : conj lambda = lambda :=
    mul_right_cancel₀ (integral_curve_mul_conj_ne_zero y hyn) hstar
  have hi := congrArg Complex.im hc
  simp only [conj_im] at hi
  linarith

theorem intrinsic_dirichlet_energy_im_zero (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) (lambda : ℂ) (y : Curve ℂ)
    (hy : IsIntrinsicHillDirichletEigenfunction q lambda y) : lambda.im = 0 := by
  obtain ⟨hyn,hyAC,hy₂,hy₀,hy₁,hw⟩ := hy
  have hys := absolutelyContinuous_curve_star y hyAC
  have hys₂ := memLp_deriv_curve_star y hy₂
  apply energy_im_zero_of_intrinsic_weak_self_test q hr lambda y hyn hyAC hy₂
  · rw [hy₀,hy₁]
  · exact hw (star y) hys hys₂ (by change conj (extend y 0) = 0; rw [hy₀,map_zero])
      (by change conj (extend y 1) = 0; rw [hy₁,map_zero])

theorem hillHminusDirichlet_zero_energy_im_zero (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) (lambda : ℂ) (hz : hillHminusDirichlet q lambda = 0) :
    lambda.im = 0 := by
  obtain ⟨y,hy⟩ := (hillHminusDirichlet_eq_zero_iff_intrinsic_dirichlet q lambda).mp hz
  exact intrinsic_dirichlet_energy_im_zero q hr lambda y hy

theorem hillHminusDirichlet_nonzero_of_im_ne_zero (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) (lambda : ℂ) (h : lambda.im ≠ 0) :
    hillHminusDirichlet q lambda ≠ 0 :=
  fun hz => h (hillHminusDirichlet_zero_energy_im_zero q hr lambda hz)

/-- Every unit-modulus Floquet condition is covered, not just signs +1
and -1. The reciprocal test multiplier equals the conjugate multiplier. -/
theorem intrinsic_weak_unitary_Floquet_energy_im_zero (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) (lambda sigma : ℂ) (hunit : ‖sigma‖ = 1)
    (y : Curve ℂ) (hy : IsIntrinsicHillWeakEigenfunction q lambda sigma y) : lambda.im = 0 := by
  obtain ⟨hsigma,hyn,hyAC,hy₂,hyend,hw⟩ := hy
  have hprod : sigma*conj sigma = 1 := by
    rw [mul_conj,Complex.normSq_eq_norm_sq,hunit]
    norm_num
  have hinv : conj sigma = sigma⁻¹ := by
    have he := congrArg (fun z : ℂ => sigma⁻¹*z) hprod
    simpa only [← mul_assoc,inv_mul_cancel₀ hsigma,one_mul,mul_one] using he
  have hend : extend y 1*conj (extend y 1) = extend y 0*conj (extend y 0) := by
    rw [hyend,map_mul]
    calc
      _ = (sigma*conj sigma)*(extend y 0*conj (extend y 0)) := by ring
      _ = _ := by rw [hprod,one_mul]
  apply energy_im_zero_of_intrinsic_weak_self_test q hr lambda y hyn hyAC hy₂ hend
  exact hw (star y) (absolutelyContinuous_curve_star y hyAC) (memLp_deriv_curve_star y hy₂) (by
    change conj (extend y 1) = sigma⁻¹*conj (extend y 0)
    rw [hyend,map_mul,hinv])

/-- A nonreal energy admits no unit-circle characteristic multiplier
for the actual entire rough discriminant. -/
theorem hillHminusDiscriminant_no_unitary_multiplier_of_im_ne_zero
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (lambda sigma : ℂ)
    (him : lambda.im ≠ 0) (hunit : ‖sigma‖ = 1) :
    sigma^2-hillHminusDiscriminant q lambda*sigma+1 ≠ 0 := by
  intro hz
  obtain ⟨y,hy⟩ := (exists_intrinsic_weak_eigenfunction_iff_characteristic q lambda sigma).mpr hz
  exact him (intrinsic_weak_unitary_Floquet_energy_im_zero q hr lambda sigma hunit y hy)

end NLS.KdV
