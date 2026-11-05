import NLS.KdV.HillHminusOneFreeDirichletPairing
import NLS.MKdV.L2QuasiHillFreeCosine
import NLS.Fourier.SineCosinePairing

/-! # The free cosine test and exact original H^-1 norming pairing -/
noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory
open NLS.LinearVolterra NLS.ZakharovShabat NLS.MKdV NLS.Fourier
namespace NLS.KdV

def freeDirichletCosineTest (n : ℕ+) : Curve ℂ :=
  l2QuasiHillPosition 0 (freeHillValue (n : ℕ)) (1,0)

theorem freeDirichletCosineTest_H1 (n : ℕ+) :
    AbsolutelyContinuousOnInterval (extend (freeDirichletCosineTest n)) 0 1 ∧
      MemLp (deriv (extend (freeDirichletCosineTest n))) 2 (volume.restrict (Ioc (0 : ℝ) 1)) :=
  ⟨absolutelyContinuous_l2QuasiHillPosition _ _ _,memLp_deriv_l2QuasiHillPosition _ _ _⟩

theorem freeDirichletCosineTest_apply (n : ℕ+) (t : Icc (0 : ℝ) 1) :
    freeDirichletCosineTest n t = cos ((n : ℂ)*(Real.pi : ℂ)*t.val) := by
  have he : (freeHillValue (n : ℕ) : ℂ) = ((n : ℂ)*(Real.pi : ℂ))^2 := by
    unfold freeHillValue
    push_cast
    ring
  change l2QuasiHillPosition 0 (freeHillValue (n : ℕ)) (1,0) t = _
  rw [he,l2QuasiHillPosition_zero_profile_cosine]

theorem freeDirichletCosineTest_extend (n : ℕ+) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    extend (freeDirichletCosineTest n) s = cos ((n : ℂ)*(Real.pi : ℂ)*s) := by
  rw [show s = (⟨s,hs⟩ : Icc (0 : ℝ) 1).val from rfl,extend_coe]
  exact freeDirichletCosineTest_apply n ⟨s,hs⟩

theorem freeDirichletCosineTest_endpoints (n : ℕ+) :
    extend (freeDirichletCosineTest n) 0 = 1 ∧ extend (freeDirichletCosineTest n) 1 = (-1 : ℂ)^(n : ℕ) := by
  constructor
  · exact l2QuasiHillPosition_initial _ _ _
  rw [freeDirichletCosineTest_extend n 1 (by norm_num),ofReal_one,mul_one]
  have he : (n : ℂ)*(Real.pi : ℂ) = (((n : ℕ) : ℝ)*Real.pi : ℝ) := by push_cast; rfl
  rw [he,← ofReal_cos,Real.cos_nat_mul_pi]
  push_cast
  rfl

theorem freeDirichlet_sine_cosine_overlap_zero (n : ℕ+) :
    (∫ s in (0 : ℝ)..1, extend (hillHminusDirichletColumn 0 (freeHillValue (n : ℕ))) s*
      extend (freeDirichletCosineTest n) s) = 0 := by
  have hs : (∫ s in (0 : ℝ)..1, sin ((n : ℂ)*(Real.pi : ℂ)*s)*cos ((n : ℂ)*(Real.pi : ℂ)*s)) = 0 := by
    simpa only [Int.cast_natCast] using integral_sine_cosine_unit (n : ℤ) (by exact_mod_cast n.ne_zero)
  calc
    _ = ∫ s in (0 : ℝ)..1,
        (sin ((n : ℂ)*(Real.pi : ℂ)*s)*cos ((n : ℂ)*(Real.pi : ℂ)*s))/((n : ℂ)*(Real.pi : ℂ)) := by
      apply intervalIntegral.integral_congr
      intro s hsi
      dsimp only
      rw [hillHminusDirichletColumn_zero_free_extend n s (by simpa using hsi),
        freeDirichletCosineTest_extend n s (by simpa using hsi)]
      ring
    _ = _ := by rw [intervalIntegral.integral_div,hs,zero_div]

theorem hillHminusWeakPotential_free_norming_product (q : PeriodOneHminusOne) (n : ℕ+) :
    hillHminusWeakPotential q (hillHminusDirichletColumn 0 (freeHillValue (n : ℕ)))
      (freeDirichletCosineTest n) =
      (q.val (-(n : ℤ))-q.val (n : ℤ))/(4*I*((n : ℂ)*(Real.pi : ℂ))) := by
  let y := hillHminusDirichletColumn 0 (freeHillValue (n : ℕ))
  let φ := freeDirichletCosineTest n
  have hy := hillHminusDirichletColumn_H1 0 (freeHillValue (n : ℕ))
  have hφ := freeDirichletCosineTest_H1 n
  have hy₀ : extend y 0 = 0 := hillHminusDirichletColumn_initial _ _
  have hy₁ : extend y 1 = 0 := (hillHminusDirichletColumn_terminal _ _).trans
    (hillHminusDirichlet_free_nat_root (n : ℕ) n.property)
  have hend : extend y 1*extend φ 1 = extend y 0*extend φ 0 := by rw [hy₀,hy₁,zero_mul,zero_mul]
  have hcoord (k : ℤ) : Continuous (fun p : PeriodOneHminusOne => p.val k) :=
    (WeightedCoeff.evalCLM (Weight.sobolev (-1)) 2 k).continuous
  have hL := continuous_hillHminusWeakPotential y φ hy.1 hφ.1 hy.2 hφ.2 hend
  have hR : Continuous (fun p : PeriodOneHminusOne =>
      (p.val (-(n : ℤ))-p.val (n : ℤ))/(4*I*((n : ℂ)*(Real.pi : ℂ)))) :=
    ((hcoord (-(n : ℤ))).sub (hcoord (n : ℤ))).div_const _
  have he : (fun p : PeriodOneHminusOne => hillHminusWeakPotential p y φ) =
      (fun p : PeriodOneHminusOne => (p.val (-(n : ℤ))-p.val (n : ℤ))/(4*I*((n : ℂ)*(Real.pi : ℂ)))) := by
    apply denseRange_periodOneL2Inclusion.equalizer hL hR
    funext p
    dsimp only [Function.comp_def]
    rw [hillHminusWeakPotential_eq_physicalL2 y φ hy.1 hφ.1 hy.2 hφ.2 hend,physicalL2HillPotentialPairing_apply]
    have hcoef (k : ℤ) : intervalFourierCoefficient 1 (unitL2SynthesisEquiv p) k = p k := by
      rw [← unitL2SynthesisEquiv_symm_coefficient,LinearIsometryEquiv.symm_apply_apply]
    have hp : (∫ s in (0 : ℝ)..1, unitL2SynthesisEquiv p s*(extend y s*extend φ s)) =
        (∫ s in (0 : ℝ)..1, unitL2SynthesisEquiv p s*
          (sin ((n : ℂ)*(Real.pi : ℂ)*s)*cos ((n : ℂ)*(Real.pi : ℂ)*s)))/((n : ℂ)*(Real.pi : ℂ)) := by
      rw [← intervalIntegral.integral_div]
      apply intervalIntegral.integral_congr
      intro s hs
      dsimp only [y,φ]
      rw [hillHminusDirichletColumn_zero_free_extend n s (by simpa using hs),
        freeDirichletCosineTest_extend n s (by simpa using hs)]
      ring
    rw [hp]
    have hs := intervalL2_sine_cosine_pairing (unitL2SynthesisEquiv p) (n : ℤ)
    simp only [Int.cast_natCast,hcoef] at hs
    rw [hs,div_div]
    simp only [periodOneL2Inclusion_apply]
  exact congrFun he q

end NLS.KdV
