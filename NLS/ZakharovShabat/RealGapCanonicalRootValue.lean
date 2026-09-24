import NLS.ZakharovShabat.SourceCanonicalRootGapSideSquare
import NLS.ZakharovShabat.RealGapArcoshIntegrability

/-!
# Real-type canonical-root values on an open gap

For a real-type source potential, the complex affine parameter of a
canonical periodic gap is a real spectral point. The square of either
canonical-root boundary value is four times the radicand of the signed
half-discriminant arcosh derivative.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The real affine coordinate of the `n`th canonical gap. -/
def realGapAffinePoint (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n : ℤ) (t : ℝ) : ℝ :=
  let a := (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n).re
  let b := (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n).re
  (a+b)/2 + (b-a)/2*t

/-- The complex gap coordinate is the embedding of its real affine
coordinate for real-type potentials. -/
theorem sourceCanonicalRootGapPoint_eq_ofReal_realGapAffinePoint
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ) (t : ℝ) :
    sourceCanonicalRootGapPoint hp hp1 ψ n t =
      (realGapAffinePoint hp hp1 ψ n t : ℂ) := by
  let φ := periodOnePotential ψ
  let l := canonicalPeriodicLeft hp hp1 φ (periodOnePotential_mem ψ) n
  let r := canonicalPeriodicRight hp hp1 φ (periodOnePotential_mem ψ) n
  have hl : ((l.re : ℝ) : ℂ) = l := by
    have him := (canonicalPeriodicEndpoints_im_eq_zero_of_realType
      hp hp1 φ (periodOnePotential_mem ψ)
      (isRealType_periodOnePotential ψ hreal) n).1
    apply Complex.ext
    · simp
    · change 0 = l.im
      exact him.symm
  have hr : ((r.re : ℝ) : ℂ) = r := by
    have him := (canonicalPeriodicEndpoints_im_eq_zero_of_realType
      hp hp1 φ (periodOnePotential_mem ψ)
      (isRealType_periodOnePotential ψ hreal) n).2
    apply Complex.ext
    · simp
    · change 0 = r.im
      exact him.symm
  change (l+r)/2 + ((r-l)/2)*(t:ℂ) =
    (((l.re+r.re)/2 + (r.re-l.re)/2*t : ℝ):ℂ)
  rw [← hl,← hr]
  simp only [Complex.ofReal_re]
  push_cast
  ring

/-- An interior affine parameter lies strictly inside an open real
canonical gap. -/
theorem realGapAffinePoint_mem_Ioo
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re)
    {t : ℝ} (ht : t ∈ Ioo (-1) 1) :
    realGapAffinePoint hp hp1 ψ n t ∈ Ioo
      (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re := by
  let a := (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n).re
  let b := (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n).re
  change a < b at hopen
  have hδ : 0 < (b-a)/2 := by linarith
  have hplus : 0 < 1+t := by linarith [ht.1]
  have hminus : 0 < 1-t := by linarith [ht.2]
  have hxleft : 0 < (b-a)/2*(1+t) := mul_pos hδ hplus
  have hxright : 0 < (b-a)/2*(1-t) := mul_pos hδ hminus
  change a < (a+b)/2 + (b-a)/2*t ∧
    (a+b)/2 + (b-a)/2*t < b
  constructor <;> nlinarith

/-- On the real axis, the discriminant radicand is four times the
radicand of the signed half-discriminant. -/
theorem canonicalDiscriminant_sq_sub_four_eq_four_realGapHalfDiscriminant
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (heven : φ ∈ pairParitySubspace 0)
    (hreal : IsRealType φ) (n : ℤ) (x : ℝ) :
    (canonicalDiscriminant hp φ (x:ℂ))^2-4 =
      ((4*((realGapHalfDiscriminant hp φ n x)^2-1):ℝ):ℂ) := by
  let D := canonicalDiscriminant hp φ (x:ℂ)
  have him : D.im = 0 :=
    canonicalDiscriminant_im_eq_zero_of_realType hp hp1 φ heven hreal x
  have hcast : ((D.re : ℝ) : ℂ) = D := by
    apply Complex.ext
    · simp
    · change 0 = D.im
      exact him.symm
  have hg : (realGapHalfDiscriminant hp φ n x)^2 = D.re^2/4 := by
    dsimp [realGapHalfDiscriminant,D]
    split_ifs <;> ring
  have hre : D.re^2-4 = 4*((realGapHalfDiscriminant hp φ n x)^2-1) := by
    nlinarith [hg]
  change D^2-4 = _
  rw [← hcast]
  exact_mod_cast hre

/-- On a real-type source gap, the upper canonical-root boundary
value squares to four times the signed arcosh radicand. -/
theorem sourceCanonicalRootGapUpperValue_sq_eq_four_realGapHalfDiscriminant
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ) (t : ℝ) (htl : -1 ≤ t) (htr : t ≤ 1) :
    (sourceCanonicalRootGapUpperValue hp hp1 ψ n t)^2 =
      ((4*((realGapHalfDiscriminant hp (periodOnePotential ψ) n
        (realGapAffinePoint hp hp1 ψ n t))^2-1):ℝ):ℂ) := by
  obtain ⟨W,_,_,hrealW,hpoint⟩ :=
    exists_global_source_gapPoint_mem_omittedDomain hp hp1
  have hdom := hpoint ψ (hrealW hreal) n t htl htr
  have hsquare := sourceCanonicalRootGapUpperValue_sq_eq_discriminant_sq_sub_four
    hp hp1 ψ n t htl htr hdom
  rw [sourceCanonicalRootGapPoint_eq_ofReal_realGapAffinePoint
    hp hp1 ψ hreal n t] at hsquare
  exact hsquare.trans
    (canonicalDiscriminant_sq_sub_four_eq_four_realGapHalfDiscriminant
      hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ)
      (isRealType_periodOnePotential ψ hreal) n
      (realGapAffinePoint hp hp1 ψ n t))

/-- The lower canonical-root boundary value has the same squared
real-gap radicand. -/
theorem sourceCanonicalRootGapLowerValue_sq_eq_four_realGapHalfDiscriminant
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ) (t : ℝ) (htl : -1 ≤ t) (htr : t ≤ 1) :
    (sourceCanonicalRootGapLowerValue hp hp1 ψ n t)^2 =
      ((4*((realGapHalfDiscriminant hp (periodOnePotential ψ) n
        (realGapAffinePoint hp hp1 ψ n t))^2-1):ℝ):ℂ) := by
  have h := sourceCanonicalRootGapUpperValue_sq_eq_four_realGapHalfDiscriminant
    hp hp1 ψ hreal n t htl htr
  rw [sourceCanonicalRootGapUpperValue_eq_neg_lower] at h
  simpa only [Even.neg_pow even_two] using h

/-- A complex number whose square is strictly positive real is itself
real. -/
private theorem im_eq_zero_of_sq_eq_pos_real
    (z : ℂ) (r : ℝ) (hr : 0 < r) (hsq : z^2 = (r:ℂ)) :
    z.im = 0 := by
  have hre := congrArg Complex.re hsq
  have him := congrArg Complex.im hsq
  simp only [pow_two,Complex.mul_re,Complex.mul_im,
    Complex.ofReal_re,Complex.ofReal_im] at hre him
  by_contra hne
  have hrezero : z.re = 0 := by
    have hm : z.re*z.im = 0 := by nlinarith [him]
    exact (mul_eq_zero.mp hm).resolve_right hne
  rw [hrezero] at hre
  nlinarith [sq_nonneg z.im]

/-- In the interior of a real open gap, the upper canonical-root
boundary value is a nonzero real number. -/
theorem sourceCanonicalRootGapUpperValue_im_eq_zero_and_ne_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re)
    {t : ℝ} (ht : t ∈ Ioo (-1) 1) :
    (sourceCanonicalRootGapUpperValue hp hp1 ψ n t).im = 0 ∧
      sourceCanonicalRootGapUpperValue hp hp1 ψ n t ≠ 0 := by
  let φ := periodOnePotential ψ
  let x := realGapAffinePoint hp hp1 ψ n t
  have hx := realGapAffinePoint_mem_Ioo hp hp1 ψ n hopen ht
  have hGpos := canonicalDeletedPeriodicProduct_re_pos_on_realGap_interior
    hp hp1 φ (periodOnePotential_mem ψ)
    (isRealType_periodOnePotential ψ hreal) n x hx
  have hradfactor := realGapHalfDiscriminant_sq_sub_one_eq_deletedPair_re
    hp hp1 φ (periodOnePotential_mem ψ)
    (isRealType_periodOnePotential ψ hreal) n x
  have hrad : 0 < (realGapHalfDiscriminant hp φ n x)^2-1 := by
    rw [hradfactor]
    exact mul_pos
      (mul_pos (sub_pos.mpr hx.1) (sub_pos.mpr hx.2)) hGpos
  have hsquare := sourceCanonicalRootGapUpperValue_sq_eq_four_realGapHalfDiscriminant
    hp hp1 ψ hreal n t ht.1.le ht.2.le
  have h4 : 0 < 4*((realGapHalfDiscriminant hp φ n x)^2-1) :=
    mul_pos (by norm_num) hrad
  constructor
  · exact im_eq_zero_of_sq_eq_pos_real _ _ h4 hsquare
  · intro hzero
    rw [hzero] at hsquare
    have hre := congrArg Complex.re hsquare
    simp only [zero_pow (by norm_num : (2:ℕ) ≠ 0), Complex.zero_re,
      Complex.ofReal_re] at hre
    change 0 = 4*((realGapHalfDiscriminant hp φ n x)^2-1) at hre
    linarith

end NLS.ZakharovShabat
