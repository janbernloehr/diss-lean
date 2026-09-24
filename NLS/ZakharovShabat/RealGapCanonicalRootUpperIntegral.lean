import NLS.ZakharovShabat.RealGapCanonicalRootRealAxis

/-!
# The canonical-root upper boundary integral on a real gap

The complex discriminant derivative is, according to the parity of
the gap index, twice the signed half-discriminant derivative or its
negative. Together with the constant sign of the canonical-root
boundary value, this reduces its quotient integral to the real arcosh
integral.
-/

noncomputable section
open Set Complex MeasureTheory intervalIntegral
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- On a real-type source, the complex spectral derivative is twice
the signed real half-discriminant derivative, with a parity sign that
is constant in the spectral parameter. -/
theorem discriminant_derivative_eq_or_eq_neg_two_realGapHalfDiscriminant_deriv
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (heven : φ ∈ pairParitySubspace 0)
    (hreal : IsRealType φ) (n : ℤ) :
    (∀ x : ℝ, deriv (canonicalDiscriminant hp φ) (x:ℂ) =
      ((2*deriv (realGapHalfDiscriminant hp φ n) x : ℝ):ℂ)) ∨
    (∀ x : ℝ, deriv (canonicalDiscriminant hp φ) (x:ℂ) =
      ((-2*deriv (realGapHalfDiscriminant hp φ n) x : ℝ):ℂ)) := by
  let D : ℝ → ℝ := fun x => (canonicalDiscriminant hp φ x).re
  have hdiff : Differentiable ℂ (canonicalDiscriminant hp φ) :=
    fun z => (analyticOnNhd_canonicalDiscriminant hp hp1 φ heven z (mem_univ _)).differentiableAt
  have hDderiv (x : ℝ) : deriv D x =
      (deriv (canonicalDiscriminant hp φ) (x:ℂ)).re :=
    NLS.ComplexAnalysis.deriv_real_axis_re _ hdiff x
  have hcast (x : ℝ) :
      (((deriv (canonicalDiscriminant hp φ) (x:ℂ)).re:ℝ):ℂ) =
        deriv (canonicalDiscriminant hp φ) (x:ℂ) := by
    have him := discriminant_derivative_im_eq_zero_of_realType
      hp hp1 φ heven hreal x
    apply Complex.ext
    · simp
    · change 0 = (deriv (canonicalDiscriminant hp φ) (x:ℂ)).im
      exact him.symm
  by_cases hn : n % 2 = 0
  · left
    have he : realGapHalfDiscriminant hp φ n = fun x : ℝ => D x/2 := by
      funext x
      simp [realGapHalfDiscriminant,D,hn]
    intro x
    have hg : deriv (realGapHalfDiscriminant hp φ n) x = deriv D x/2 := by
      rw [he,deriv_div_const]
    rw [← hcast x]
    congr 1
    rw [hg,hDderiv]
    ring
  · right
    have he : realGapHalfDiscriminant hp φ n = fun x : ℝ => -D x/2 := by
      funext x
      simp [realGapHalfDiscriminant,D,hn]
    intro x
    have hg : deriv (realGapHalfDiscriminant hp φ n) x = -deriv D x/2 := by
      rw [he,deriv_div_const]
      change deriv (-D) x / 2 = -deriv D x / 2
      rw [deriv.neg]
    rw [← hcast x]
    congr 1
    rw [hg,hDderiv]
    ring

/-- Cancellation of the common factor two in the real-gap quotient. -/
private theorem two_deriv_div_two_sqrt_eq_cast
    (u v : ℝ) (hv : v ≠ 0) :
    (((2*u:ℝ):ℂ) / ((2*v:ℝ):ℂ)) = ((u/v:ℝ):ℂ) := by
  have hvC : (v:ℂ) ≠ 0 := by exact_mod_cast hv
  push_cast
  field_simp

/-- The upper boundary integral of the discriminant derivative divided
by the full canonical root vanishes on every open real source gap. -/
theorem integral_discriminant_derivative_div_realGapCanonicalRootUpperValue_eq_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re) :
    (∫ x in (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re..
        (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
          (periodOnePotential_mem ψ) n).re,
      deriv (canonicalDiscriminant hp (periodOnePotential ψ)) (x:ℂ) /
        realGapCanonicalRootUpperValue hp hp1 ψ n x) = 0 := by
  let φ := periodOnePotential ψ
  let a := (canonicalPeriodicLeft hp hp1 φ (periodOnePotential_mem ψ) n).re
  let b := (canonicalPeriodicRight hp hp1 φ (periodOnePotential_mem ψ) n).re
  let g := realGapHalfDiscriminant hp φ n
  let D (x : ℝ) := deriv (canonicalDiscriminant hp φ) (x:ℂ)
  let U := realGapCanonicalRootUpperValue hp hp1 ψ n
  let K (x : ℝ) : ℂ := ((deriv g x / Real.sqrt (g x^2-1):ℝ):ℂ)
  have hnum := discriminant_derivative_eq_or_eq_neg_two_realGapHalfDiscriminant_deriv
    hp hp1 φ (periodOnePotential_mem ψ)
    (isRealType_periodOnePotential ψ hreal) n
  have hden := realGapCanonicalRootUpperValue_eq_or_eq_neg_two_sqrt
    hp hp1 ψ hreal n hopen
  have hratio (x : ℝ) (hx : x ∈ Ioo a b) :
      (((2*deriv g x:ℝ):ℂ) /
        ((2*Real.sqrt (g x^2-1):ℝ):ℂ)) = K x := by
    have ht := realGapInverseCoordinate_mem_Ioo hp hp1 ψ n hx
    have hrad := realGapHalfDiscriminant_radicand_pos_at_affinePoint
      hp hp1 ψ hreal n hopen ht
    rw [realGapAffinePoint_inverse hp hp1 ψ n hopen x] at hrad
    exact two_deriv_div_two_sqrt_eq_cast _ _
      (ne_of_gt (Real.sqrt_pos.mpr hrad))
  have hpoint :
      (∀ x ∈ Ioo a b, D x / U x = K x) ∨
      (∀ x ∈ Ioo a b, D x / U x = -K x) := by
    rcases hnum with hn | hn <;> rcases hden with hd | hd
    · left
      intro x hx
      change deriv (canonicalDiscriminant hp φ) (x:ℂ) /
        realGapCanonicalRootUpperValue hp hp1 ψ n x = K x
      rw [hn x,hd x hx]
      exact hratio x hx
    · right
      intro x hx
      change deriv (canonicalDiscriminant hp φ) (x:ℂ) /
        realGapCanonicalRootUpperValue hp hp1 ψ n x = -K x
      rw [hn x,hd x hx,div_neg]
      exact congrArg Neg.neg (hratio x hx)
    · right
      intro x hx
      change deriv (canonicalDiscriminant hp φ) (x:ℂ) /
        realGapCanonicalRootUpperValue hp hp1 ψ n x = -K x
      rw [hn x,hd x hx]
      simp only [neg_mul,Complex.ofReal_neg,neg_div]
      exact congrArg Neg.neg (hratio x hx)
    · left
      intro x hx
      change deriv (canonicalDiscriminant hp φ) (x:ℂ) /
        realGapCanonicalRootUpperValue hp hp1 ψ n x = K x
      rw [hn x,hd x hx]
      simp only [neg_mul,Complex.ofReal_neg,neg_div_neg_eq]
      exact hratio x hx
  have hbase : (∫ x in a..b, K x) = 0 := by
    have h := integral_realGapHalfDiscriminant_arcosh_deriv_eq_zero_of_source
      hp hp1 ψ hreal n hopen
    have hc := congrArg (fun r : ℝ => (r:ℂ)) h
    simpa only [K,intervalIntegral.integral_ofReal,Complex.ofReal_zero]
      using hc
  rcases hpoint with hpoint | hpoint
  · calc
      (∫ x in a..b, D x / U x) = ∫ x in a..b, K x := by
        apply intervalIntegral.integral_congr_uIoo
        have hab : a ≤ b := hopen.le
        rw [uIoo_of_le hab]
        exact hpoint
      _ = 0 := hbase
  · calc
      (∫ x in a..b, D x / U x) = ∫ x in a..b, -K x := by
        apply intervalIntegral.integral_congr_uIoo
        have hab : a ≤ b := hopen.le
        rw [uIoo_of_le hab]
        exact hpoint
      _ = -(∫ x in a..b, K x) := by rw [intervalIntegral.integral_neg]
      _ = 0 := by rw [hbase]; simp

end NLS.ZakharovShabat
