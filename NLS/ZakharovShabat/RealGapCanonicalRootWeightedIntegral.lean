import NLS.ZakharovShabat.RealGapWeightedArcoshIntegral
import NLS.ZakharovShabat.RealGapCanonicalRootUpperIntegral

/-!
# Weighted canonical-root boundary integral on an open real gap

The upper-side canonical-root value has a fixed sign relative to the
positive arcosh square root. Consequently its weighted quotient
integral is one of the two signs of a strictly negative real arcosh
integral. This is the boundary-integral sign calculation needed for
the real-type action in Lemma 11.1, before orienting the enclosing
contour and fixing the canonical-root sign.
-/

noncomputable section
open Set Complex MeasureTheory intervalIntegral
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

private theorem two_deriv_div_two_sqrt_eq_cast_weighted
    (u v : ℝ) (hv : v ≠ 0) :
    (((2*u:ℝ):ℂ) / ((2*v:ℝ):ℂ)) = ((u/v:ℝ):ℂ) := by
  have hvC : (v:ℂ) ≠ 0 := by exact_mod_cast hv
  push_cast
  field_simp

/-- The weighted upper boundary quotient is real and nonzero on an
open real gap. Its two possible signs reflect the global sign choice
of the canonical root. -/
theorem realGapCanonicalRootUpper_weighted_integral_sign
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re)
    (q : ℝ) :
    let a := (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re
    let b := (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re
    let W : ℂ := ∫ x in a..b,
      ((x-q:ℝ):ℂ) *
        (deriv (canonicalDiscriminant hp (periodOnePotential ψ)) (x:ℂ) /
          realGapCanonicalRootUpperValue hp hp1 ψ n x)
    W.im = 0 ∧ W ≠ 0 := by
  let φ := periodOnePotential ψ
  let a := (canonicalPeriodicLeft hp hp1 φ (periodOnePotential_mem ψ) n).re
  let b := (canonicalPeriodicRight hp hp1 φ (periodOnePotential_mem ψ) n).re
  let g := realGapHalfDiscriminant hp φ n
  let D (x : ℝ) := deriv (canonicalDiscriminant hp φ) (x:ℂ)
  let U := realGapCanonicalRootUpperValue hp hp1 ψ n
  let K (x : ℝ) : ℂ := ((deriv g x / Real.sqrt (g x^2-1):ℝ):ℂ)
  let J (x : ℝ) : ℂ := ((x-q:ℝ):ℂ) * K x
  let s : ℝ := ∫ x in a..b,
    (x-q) * (deriv g x / Real.sqrt (g x^2-1))
  have hs : s < 0 := (realGap_weighted_arcosh_integral_eq_and_neg
    hp hp1 ψ hreal n hopen q).2
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
    exact two_deriv_div_two_sqrt_eq_cast_weighted _ _
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
  have hJ : (∫ x in a..b, J x) = (s:ℂ) := by
    simp only [J,K,← Complex.ofReal_mul,intervalIntegral.integral_ofReal,s]
  have hW :
      (∫ x in a..b, ((x-q:ℝ):ℂ) * (D x / U x)) = (s:ℂ) ∨
      (∫ x in a..b, ((x-q:ℝ):ℂ) * (D x / U x)) = -(s:ℂ) := by
    rcases hpoint with hpnt | hpnt
    · left
      calc
        _ = ∫ x in a..b, J x := by
          apply intervalIntegral.integral_congr_uIoo
          rw [uIoo_of_le hopen.le]
          intro x hx
          change ((x-q:ℝ):ℂ) * (D x / U x) = ((x-q:ℝ):ℂ) * K x
          rw [hpnt x hx]
        _ = (s:ℂ) := hJ
    · right
      calc
        _ = ∫ x in a..b, -J x := by
          apply intervalIntegral.integral_congr_uIoo
          rw [uIoo_of_le hopen.le]
          intro x hx
          change ((x-q:ℝ):ℂ) * (D x / U x) = -(((x-q:ℝ):ℂ) * K x)
          rw [hpnt x hx]
          ring
        _ = -(s:ℂ) := by rw [intervalIntegral.integral_neg,hJ]
  have hsC : (s:ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_lt hs)
  change ((∫ x in a..b, ((x-q:ℝ):ℂ) * (D x / U x))).im = 0 ∧
    (∫ x in a..b, ((x-q:ℝ):ℂ) * (D x / U x)) ≠ 0
  rcases hW with hW | hW
  · rw [hW]
    exact ⟨by simp,hsC⟩
  · rw [hW]
    exact ⟨by simp,neg_ne_zero.mpr hsC⟩

end NLS.ZakharovShabat
