import NLS.KdV.HillL2CutSquareTrace

/-! # Simple endpoints and a nonvanishing unit for the Hill primitive square

The derivative of the even cosh coordinate at zero is one half. Hence
the filled square inherits each simple actual endpoint, with exact
derivative `(-1)^n Delta'`. Deflating those two zeros gives an analytic
nowhere-zero unit throughout the local disc.
-/

noncomputable section
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis
namespace NLS.KdV

theorem HillRealHighGapPair.trace_derivs_ne_zero_of_open
    (q : Coeff 2) (n : ℕ) (p : HillRealHighGapPair q n) (hopen : p.left ≠ p.right) :
    deriv (hillL2Discriminant q) p.left ≠ 0 ∧ deriv (hillL2Discriminant q) p.right ≠ 0 := by
  have hab : (p.left : ℂ) ≠ (p.right : ℂ) := fun he => hopen (ofReal_inj.mp he)
  have hleft : analyticOrderNatAt (hillL2Radicand q) p.left = 1 := by
    rw [p.orders p.left p.left_mem]
    simp [hab]
  have hright : analyticOrderNatAt (hillL2Radicand q) p.right = 1 := by
    rw [p.orders p.right p.right_mem]
    simp [hab,hab.symm]
  have hD (x : ℂ) (ho : analyticOrderNatAt (hillL2Radicand q) x = 1) :
      deriv (hillL2Discriminant q) x ≠ 0 := by
    have hd := deriv_ne_zero_of_analyticOrderNatAt_eq_one _ x
      (analyticOnNhd_hillL2Radicand q x (mem_univ _)) ho
    have hrad : HasDerivAt (hillL2Radicand q)
        (2*hillL2Discriminant q x*deriv (hillL2Discriminant q) x) x := by
      change HasDerivAt (fun z : ℂ => hillL2Discriminant q z^2-4) _ x
      simpa only [Pi.pow_apply,Nat.cast_ofNat,Nat.add_one_sub_one,pow_one] using
        (((analyticOnNhd_hillL2Discriminant q x (mem_univ _)).differentiableAt.hasDerivAt.pow 2).sub_const 4)
    intro he
    apply hd
    rw [hrad.deriv,he,mul_zero]
  exact ⟨hD p.left hleft,hD p.right hright⟩

theorem HillL2NormalizedCutPrimitive.square_deriv_at_zero
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hreal : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (n : ℕ) (hn : 2 ≤ n) (hcut : 16*‖q‖ ≤ (n : ℝ))
    (p : HillRealHighGapPair (SpectralWeight.one.toCoeff q) n) (hopen : p.left ≠ p.right)
    (R F : ℂ → ℂ)
    (h : HillL2NormalizedCutPrimitive (SpectralWeight.one.toCoeff q) n p R F)
    (z : ℂ) (hz : z ∈ ball (freeHillValue n : ℂ) (7*(n : ℝ)/8))
    (hzero : hillL2CutPrimitiveSquare n p.left p.right F z = 0) :
    deriv (hillL2CutPrimitiveSquare n p.left p.right F) z =
      (-1 : ℂ)^n*deriv (hillL2Discriminant (SpectralWeight.one.toCoeff q)) z := by
  let X := hillL2CutPrimitiveSquare n p.left p.right F
  obtain ⟨hX,_,_,_⟩ := h.square_extension q hq hreal n hn hcut p hopen R F
  have he : (fun w => coshSquareCoordinate (X w)) =ᶠ[𝓝 z]
      (fun w => (-1 : ℂ)^n*hillL2Discriminant (SpectralWeight.one.toCoeff q) w/2) := by
    filter_upwards [isOpen_ball.mem_nhds hz] with w hw
    exact h.square_trace q hq hreal n hn hcut p hopen R F w hw
  have hd := ((analyticOnNhd_coshSquareCoordinate (X z) (mem_univ _)).differentiableAt.hasDerivAt).comp z
    (hX z hz).differentiableAt.hasDerivAt
  change X z = 0 at hzero
  rw [hzero,deriv_coshSquareCoordinate_zero] at hd
  have hv := (hd.congr_of_eventuallyEq he.symm).unique
    (((analyticOnNhd_hillL2Discriminant _ z (mem_univ _)).differentiableAt.hasDerivAt.const_mul
      ((-1 : ℂ)^n)).div_const 2)
  linear_combination 2*hv

theorem HillL2NormalizedCutPrimitive.square_deflated_unit
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hreal : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (n : ℕ) (hn : 2 ≤ n) (hcut : 16*‖q‖ ≤ (n : ℝ))
    (p : HillRealHighGapPair (SpectralWeight.one.toCoeff q) n) (hopen : p.left ≠ p.right)
    (R F : ℂ → ℂ)
    (h : HillL2NormalizedCutPrimitive (SpectralWeight.one.toCoeff q) n p R F) :
    AnalyticOnNhd ℂ (twoZeroQuotient (hillL2CutPrimitiveSquare n p.left p.right F) p.left p.right)
      (ball (freeHillValue n : ℂ) (7*(n : ℝ)/8)) ∧
    (∀ z, hillL2CutPrimitiveSquare n p.left p.right F z =
      (z-p.left)*(z-p.right)*twoZeroQuotient (hillL2CutPrimitiveSquare n p.left p.right F) p.left p.right z) ∧
    ∀ z ∈ ball (freeHillValue n : ℂ) (7*(n : ℝ)/8),
      twoZeroQuotient (hillL2CutPrimitiveSquare n p.left p.right F) p.left p.right z ≠ 0 := by
  let X := hillL2CutPrimitiveSquare n p.left p.right F
  let Ω := ball (freeHillValue n : ℂ) (7*(n : ℝ)/8)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  obtain ⟨hX,_,hleft,hright⟩ := h.square_extension q hq hreal n hn hcut p hopen R F
  have hloc := p.localization q hq n (by omega) (by linarith [norm_nonneg q])
  have hl : (p.left : ℂ) ∈ Ω := by
    rw [mem_ball,dist_eq_norm,← ofReal_sub,norm_real,Real.norm_eq_abs]
    linarith [hloc.1]
  have hr : (p.right : ℂ) ∈ Ω := by
    rw [mem_ball,dist_eq_norm,← ofReal_sub,norm_real,Real.norm_eq_abs]
    linarith [hloc.2]
  have hab : (p.left : ℂ) ≠ (p.right : ℂ) := fun he => hopen (ofReal_inj.mp he)
  have hdouble : (p.left : ℂ) = (p.right : ℂ) → deriv X p.left = 0 := fun he => (hab he).elim
  have hDn := p.trace_derivs_ne_zero_of_open _ n hopen
  have horder (a : ℂ) (ha : a ∈ Ω) (hXa : X a = 0) (hDa : deriv (hillL2Discriminant (SpectralWeight.one.toCoeff q)) a ≠ 0) :
      analyticOrderNatAt X a = 1 := by
    have hd : deriv X a ≠ 0 := by
      rw [h.square_deriv_at_zero q hq hreal n hn hcut p hopen R F a ha hXa]
      exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hDa
    have ho := (hX a ha).analyticOrderAt_eq_one_of_zero_deriv_ne_zero hXa hd
    simpa only [analyticOrderNatAt,ENat.toNat_one] using congrArg ENat.toNat ho
  have horderL := horder p.left hl hleft hDn.1
  have horderR := horder p.right hr hright hDn.2
  refine ⟨analyticOnNhd_twoZeroQuotient X Ω p.left p.right hX hl hr,
    twoZeroQuotient_factor X p.left p.right hleft hright hdouble,?_⟩
  intro z hz
  apply twoZeroQuotient_ne_zero X Ω p.left p.right z hX hl hr hz hleft hright hdouble
    (fun he => (h.square_zero_iff q hq hreal n hn hcut p hopen R F z hz).mp he)
  intro he
  rcases (h.square_zero_iff q hq hreal n hn hcut p hopen R F z hz).mp he with rfl | rfl
  · rw [horderL]
    simp [hab]
  · rw [horderR]
    simp [hab,hab.symm]

end NLS.KdV
