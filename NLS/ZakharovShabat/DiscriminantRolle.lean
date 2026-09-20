import NLS.ZakharovShabat.RealDiscriminantValues

/-!
# Real discriminant critical points between equal values

Rolle's theorem applies to the real discriminant. At a repeated periodic
root, its derivative vanishes by the exact analytic multiplicity of the
full characteristic function. These cover open and collapsed gaps.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Equal discriminant values at two distinct real points enclose a critical point. -/
theorem exists_discriminant_critical_between (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (hφ : φ ∈ pairParitySubspace 0) (hreal : IsRealType φ)
    {a b : ℝ} (hab : a < b) (he : canonicalDiscriminant hp φ a = canonicalDiscriminant hp φ b) :
    ∃ c ∈ Ioo a b, deriv (canonicalDiscriminant hp φ) (c : ℂ) = 0 :=
  NLS.ComplexAnalysis.exists_deriv_eq_zero_between_real _
    (fun z => (analyticOnNhd_canonicalDiscriminant hp hp1 φ hφ z (mem_univ _)).differentiableAt)
    (canonicalDiscriminant_im_eq_zero_of_realType hp hp1 φ hφ hreal) hab he

/-- Every periodic root of algebraic multiplicity at least two is a discriminant critical point. -/
theorem discriminant_derivative_eq_zero_of_multiplicity_ge_two (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (hφ : φ ∈ pairParitySubspace 0) (z : ℂ)
    (hz : z ∈ periodicSpectrum hp φ) (hm : 2 ≤ periodicAlgebraicMultiplicity hp φ z) :
    deriv (canonicalDiscriminant hp φ) z = 0 := by
  have hval := (canonicalDiscriminant_sq_eq_four_iff_finite hp hp1 φ hφ z).mpr hz
  have hn : canonicalDiscriminant hp φ z ≠ 0 := by
    intro he
    rw [he] at hval
    norm_num at hval
  have ha := analyticOnNhd_canonicalDiscriminant hp hp1 φ hφ z (mem_univ _)
  have hchar : AnalyticAt ℂ (fun w => (canonicalDiscriminant hp φ w)^2-4) z :=
    (ha.pow 2).sub analyticAt_const
  have hd : deriv (fun w => (canonicalDiscriminant hp φ w)^2-4) z =
      2*canonicalDiscriminant hp φ z*deriv (canonicalDiscriminant hp φ) z := by
    simpa only [Nat.cast_ofNat, Nat.reduceSub, pow_one, Pi.pow_apply] using ((ha.differentiableAt.hasDerivAt.pow 2).sub_const 4).deriv
  by_contra hder
  have ho := hchar.analyticOrderAt_eq_one_of_zero_deriv_ne_zero (by simp only [hval, sub_self])
    (by rw [hd]; exact mul_ne_zero (mul_ne_zero (by norm_num) hn) hder)
  rw [analyticOrderAt_canonicalDiscriminant_sq_sub_four hp hp1 φ hφ] at ho
  have hm1 : periodicAlgebraicMultiplicity hp φ z = 1 := by exact_mod_cast ho
  omega

end NLS.ZakharovShabat
