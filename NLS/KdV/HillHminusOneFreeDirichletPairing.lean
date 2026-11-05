import NLS.KdV.HillHminusOneFreeDirichletColumn
import NLS.Fourier.SineSquarePairing

/-! # Exact free column mass and H^-1 squared-column pairing

The unit Fourier convention retains both signed coefficients. Density
extends the physical sine-square integral to every complex H^-1 input.
-/
noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory
open NLS.LinearVolterra NLS.ZakharovShabat NLS.MKdV NLS.Fourier
namespace NLS.KdV

theorem hillHminusDirichletColumn_zero_free_extend (n : ℕ+) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    extend (hillHminusDirichletColumn 0 (freeHillValue (n : ℕ))) s =
      sin ((n : ℂ)*(Real.pi : ℂ)*s)/((n : ℂ)*(Real.pi : ℂ)) := by
  rw [show s = (⟨s,hs⟩ : Icc (0 : ℝ) 1).val from rfl,extend_coe]
  exact hillHminusDirichletColumn_zero_free n ⟨s,hs⟩

theorem hillHminusDirichletColumn_free_square_integral (n : ℕ+) :
    (∫ s in (0 : ℝ)..1, extend (hillHminusDirichletColumn 0 (freeHillValue (n : ℕ))) s*
      extend (hillHminusDirichletColumn 0 (freeHillValue (n : ℕ))) s) =
      1/(2*((n : ℂ)*(Real.pi : ℂ))^2) := by
  have hs : (∫ s in (0 : ℝ)..1, sin ((n : ℂ)*(Real.pi : ℂ)*s)^2) = (1 : ℂ)/2 := by
    simpa only [Int.cast_natCast] using integral_sine_square_unit (n : ℤ) (by exact_mod_cast n.ne_zero)
  calc
    _ = ∫ s in (0 : ℝ)..1, sin ((n : ℂ)*(Real.pi : ℂ)*s)^2/((n : ℂ)*(Real.pi : ℂ))^2 := by
      apply intervalIntegral.integral_congr
      intro s hs
      dsimp only
      rw [hillHminusDirichletColumn_zero_free_extend n s (by simpa using hs)]
      ring
    _ = _ := by rw [intervalIntegral.integral_div,hs,div_div]

theorem hillHminusWeakPotential_free_Dirichlet_square (q : PeriodOneHminusOne) (n : ℕ+) :
    hillHminusWeakPotential q (hillHminusDirichletColumn 0 (freeHillValue (n : ℕ)))
      (hillHminusDirichletColumn 0 (freeHillValue (n : ℕ))) =
      (2*q.val 0-q.val (n : ℤ)-q.val (-(n : ℤ)))/(4*((n : ℂ)*(Real.pi : ℂ))^2) := by
  let y := hillHminusDirichletColumn 0 (freeHillValue (n : ℕ))
  have hy := hillHminusDirichletColumn_H1 0 (freeHillValue (n : ℕ))
  have hy₀ : extend y 0 = 0 := hillHminusDirichletColumn_initial _ _
  have hy₁ : extend y 1 = 0 := (hillHminusDirichletColumn_terminal _ _).trans
    (hillHminusDirichlet_free_nat_root (n : ℕ) n.property)
  have hend : extend y 1*extend y 1 = extend y 0*extend y 0 := by rw [hy₀,hy₁]
  have hcoord (k : ℤ) : Continuous (fun p : PeriodOneHminusOne => p.val k) :=
    (WeightedCoeff.evalCLM (Weight.sobolev (-1)) 2 k).continuous
  have hL := continuous_hillHminusWeakPotential y y hy.1 hy.1 hy.2 hy.2 hend
  have hR : Continuous (fun p : PeriodOneHminusOne =>
      (2*p.val 0-p.val (n : ℤ)-p.val (-(n : ℤ)))/(4*((n : ℂ)*(Real.pi : ℂ))^2)) :=
    (((continuous_const.mul (hcoord 0)).sub (hcoord (n : ℤ))).sub (hcoord (-(n : ℤ)))).div_const _
  have he : (fun p : PeriodOneHminusOne => hillHminusWeakPotential p y y) =
      (fun p : PeriodOneHminusOne =>
        (2*p.val 0-p.val (n : ℤ)-p.val (-(n : ℤ)))/(4*((n : ℂ)*(Real.pi : ℂ))^2)) := by
    apply denseRange_periodOneL2Inclusion.equalizer hL hR
    funext p
    dsimp only [Function.comp_def]
    rw [hillHminusWeakPotential_eq_physicalL2 y y hy.1 hy.1 hy.2 hy.2 hend,physicalL2HillPotentialPairing_apply]
    have hcoef (k : ℤ) : intervalFourierCoefficient 1 (unitL2SynthesisEquiv p) k = p k := by
      rw [← unitL2SynthesisEquiv_symm_coefficient,LinearIsometryEquiv.symm_apply_apply]
    have hp : (∫ s in (0 : ℝ)..1, unitL2SynthesisEquiv p s*(extend y s*extend y s)) =
        (∫ s in (0 : ℝ)..1, unitL2SynthesisEquiv p s*sin ((n : ℂ)*(Real.pi : ℂ)*s)^2)/
          ((n : ℂ)*(Real.pi : ℂ))^2 := by
      rw [← intervalIntegral.integral_div]
      apply intervalIntegral.integral_congr
      intro s hs
      dsimp only [y]
      rw [hillHminusDirichletColumn_zero_free_extend n s (by simpa using hs)]
      ring
    rw [hp]
    have hs := intervalL2_sine_square_pairing (unitL2SynthesisEquiv p) (n : ℤ)
    simp only [Int.cast_natCast,hcoef] at hs
    rw [hs,div_div]
    simp only [periodOneL2Inclusion_apply]
  exact congrFun he q

end NLS.KdV
