import NLS.KdV.HillAngularPeriods
import NLS.KdV.HillDirichletTerminalAngle
import NLS.ComplexAnalysis.ParametricTrigonometricTerminal

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV



variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

def hillRegularAbelianPrimitive (n : ℕ) (hn : 1 ≤ n) (k : ℕ) (θ : ℂ) : ℂ :=
  hillAbelianCosinePrimitive q hq hr n hn k θ-(if k=n then 1 else 0)*(θ-(Real.pi:ℂ))

theorem hillRegularAbelianPrimitive_real_add_int_period (n : ℕ) (hn : 1 ≤ n) (k : ℕ) (hk : 1 ≤ k)
    (θ : ℝ) (j : ℤ) :
    hillRegularAbelianPrimitive q hq hr n hn k ((θ+j • (2*Real.pi) : ℝ):ℂ) =
      hillRegularAbelianPrimitive q hq hr n hn k (θ:ℂ) := by
  unfold hillRegularAbelianPrimitive
  rw [hillAbelianCosinePrimitive_real_add_int_period q hq hr n hn k hk θ j]
  simp only [zsmul_eq_mul]
  push_cast
  ring

theorem hillRegularAbelianPrimitive_im_eq_zero (n : ℕ) (hn : 1 ≤ n) (k : ℕ) (hk : 1 ≤ k) (θ : ℝ) :
    (hillRegularAbelianPrimitive q hq hr n hn k (θ:ℂ)).im = 0 := by
  unfold hillRegularAbelianPrimitive
  have hF := hillAbelianCosinePrimitive_im_eq_zero q hq hr n hn k hk θ
  by_cases hkn : k=n
  · rw [if_pos hkn,one_mul]
    simp only [sub_im,hF,ofReal_im,sub_self]
  · rw [if_neg hkn,zero_mul,sub_zero]
    exact hF

theorem hillRegularAbelianPrimitive_terminal_independent
    (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (hgap : hillRealGapHalfLength q hq hr k ≠ 0)
    (θ φ : ℝ)
    (hθ : cosineGapPoint (hillRealGapCenter q hq hr k) (hillRealGapHalfLength q hq hr k) (θ:ℂ) =
      (hillDirichletEnergy q hq hr k hk : ℂ))
    (hφ : cosineGapPoint (hillRealGapCenter q hq hr k) (hillRealGapHalfLength q hq hr k) (φ:ℂ) =
      (hillDirichletEnergy q hq hr k hk : ℂ))
    (hsinθ : Complex.sin (θ:ℂ) = hillDirichletGapSine q hq hr k hk)
    (hsinφ : Complex.sin (φ:ℂ) = hillDirichletGapSine q hq hr k hk) :
    hillRegularAbelianPrimitive q hq hr n hn k (θ:ℂ) = hillRegularAbelianPrimitive q hq hr n hn k (φ:ℂ) := by
  have hδ : (hillRealGapHalfLength q hq hr k : ℂ) ≠ 0 := ofReal_ne_zero.mpr hgap
  have hcos : Complex.cos (θ:ℂ) = Complex.cos (φ:ℂ) := by
    apply mul_right_cancel₀ hδ
    dsimp only [cosineGapPoint] at hθ hφ
    linear_combination hθ-hφ
  obtain ⟨j,hj⟩ := eq_mod_two_pi_of_cos_eq_of_sin_eq (θ:ℂ) (φ:ℂ) hcos (hsinθ.trans hsinφ.symm)
  have hθφ : θ = φ+j • (2*Real.pi) := by
    apply Complex.ofReal_injective
    simpa only [zsmul_eq_mul,ofReal_add,ofReal_mul,ofReal_ofNat,ofReal_intCast] using hj
  rw [hθφ,hillRegularAbelianPrimitive_real_add_int_period q hq hr n hn k hk φ j]

end NLS.KdV
