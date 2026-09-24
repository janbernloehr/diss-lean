import NLS.ZakharovShabat.SourceStandardRootAlgebra
import NLS.ZakharovShabat.CanonicalPeriodicGapOrder

/-!
# Sign of a normalized standard root outside a real gap

The principal square root in the normalized standard factor is
positive on either real exterior ray. Hence the factor has the sign
of its linear midpoint term. This is the local sign input for
orienting the omitted canonical-root product on a selected gap.
-/

noncomputable section
open Set Complex ComplexOrder
open NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- On the positive real radicand, the normalized complex root is the
real square-root expression. -/
theorem normalizedStandardRoot_ofReal_of_radicand_nonneg
    (t g x : ℝ) (h : 0 ≤ 1-g/(4*(t-x)^2)) :
    normalizedStandardRoot (t:ℂ) (g:ℂ) (x:ℂ) =
      (((t-x)*Real.sqrt (1-g/(4*(t-x)^2)):ℝ):ℂ) := by
  unfold normalizedStandardRoot
  have hcast : 1-(g:ℂ)/(4*((t:ℂ)-(x:ℂ))^2) =
      ((1-g/(4*(t-x)^2):ℝ):ℂ) := by
    push_cast
    ring
  have hre : (1-(g:ℂ)/(4*((t:ℂ)-(x:ℂ))^2)).re =
      1-g/(4*(t-x)^2) := by
    simpa only [Complex.ofReal_re] using congrArg Complex.re hcast
  have hnonneg : (0:ℂ) ≤ 1-(g:ℂ)/(4*((t:ℂ)-(x:ℂ))^2) := by
    rw [hcast]
    exact_mod_cast h
  rw [Complex.sqrt_of_nonneg hnonneg, hre]
  push_cast
  ring

/-- The real radicand is positive whenever the spectral point lies
strictly farther from the midpoint than the half-gap. -/
theorem normalizedStandardRoot_real_radicand_pos
    (t d x : ℝ) (h : d^2 < (t-x)^2) :
    0 < 1-(2*d)^2/(4*(t-x)^2) := by
  have hden : 0 < (t-x)^2 := by nlinarith [sq_nonneg d]
  have hfrac : d^2/(t-x)^2 < 1 :=
    (div_lt_one hden).2 h
  have heq : (2*d)^2/(4*(t-x)^2) = d^2/(t-x)^2 := by
    field_simp
    ring
  rw [heq]
  linarith

/-- A normalized standard root is positive to the left of a real
gap, where its real midpoint factor is positive. -/
theorem normalizedStandardRoot_re_pos_of_real_left
    (t d x : ℝ) (hd : 0 ≤ d) (hx : x < t-d) :
    0 < (normalizedStandardRoot (t:ℂ) (((2*d)^2:ℝ):ℂ) (x:ℂ)).re := by
  have htx : 0 < t-x := by linarith
  have hsq : d^2 < (t-x)^2 := by nlinarith
  have hrad := normalizedStandardRoot_real_radicand_pos t d x hsq
  rw [normalizedStandardRoot_ofReal_of_radicand_nonneg t ((2*d)^2) x hrad.le]
  simpa only [Complex.ofReal_re] using
    mul_pos htx (Real.sqrt_pos.mpr hrad)

/-- A normalized standard root is negative to the right of a real
gap, where its real midpoint factor is negative. -/
theorem normalizedStandardRoot_re_neg_of_real_right
    (t d x : ℝ) (hd : 0 ≤ d) (hx : t+d < x) :
    (normalizedStandardRoot (t:ℂ) (((2*d)^2:ℝ):ℂ) (x:ℂ)).re < 0 := by
  have htx : t-x < 0 := by linarith
  have hsq : d^2 < (t-x)^2 := by nlinarith
  have hrad := normalizedStandardRoot_real_radicand_pos t d x hsq
  rw [normalizedStandardRoot_ofReal_of_radicand_nonneg t ((2*d)^2) x hrad.le]
  simpa only [Complex.ofReal_re] using
    mul_neg_of_neg_of_pos htx (Real.sqrt_pos.mpr hrad)

/-- With ordered real endpoints, the standard root is positive on
the left exterior ray. -/
theorem normalizedStandardRoot_re_pos_of_lt_leftEndpoint
    (a b x : ℝ) (hab : a ≤ b) (hx : x < a) :
    0 < (normalizedStandardRoot (((a+b)/2:ℝ):ℂ)
      (((b-a)^2:ℝ):ℂ) (x:ℂ)).re := by
  have hd : 0 ≤ (b-a)/2 := by linarith
  have hleft : x < (a+b)/2-(b-a)/2 := by linarith
  convert normalizedStandardRoot_re_pos_of_real_left
    ((a+b)/2) ((b-a)/2) x hd hleft using 1 <;> ring

/-- With ordered real endpoints, the standard root is negative on
the right exterior ray. -/
theorem normalizedStandardRoot_re_neg_of_gt_rightEndpoint
    (a b x : ℝ) (hab : a ≤ b) (hx : b < x) :
    (normalizedStandardRoot (((a+b)/2:ℝ):ℂ)
      (((b-a)^2:ℝ):ℂ) (x:ℂ)).re < 0 := by
  have hd : 0 ≤ (b-a)/2 := by linarith
  have hright : (a+b)/2+(b-a)/2 < x := by linarith
  convert normalizedStandardRoot_re_neg_of_real_right
    ((a+b)/2) ((b-a)/2) x hd hright using 1 <;> ring

/-- Every source standard-root factor is positive on the real axis to
the left of its canonical periodic pair. -/
theorem sourceStandardRoot_re_pos_of_real_lt_left
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (m : ℤ) (x : ℝ)
    (hx : x < (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) m).re) :
    0 < (sourceStandardRoot hp hp1 ψ m (x:ℂ)).re := by
  let φ := periodOnePotential ψ
  let l := canonicalPeriodicLeft hp hp1 φ (periodOnePotential_mem ψ) m
  let r := canonicalPeriodicRight hp hp1 φ (periodOnePotential_mem ψ) m
  let a := l.re
  let b := r.re
  have hends := canonicalPeriodicEndpoints_im_eq_zero_of_realType
    hp hp1 φ (periodOnePotential_mem ψ)
      (isRealType_periodOnePotential ψ hreal) m
  have hl : (a:ℂ) = l := by
    apply Complex.ext
    · rfl
    · exact hends.1.symm
  have hr : (b:ℂ) = r := by
    apply Complex.ext
    · rfl
    · exact hends.2.symm
  have hab : a ≤ b := re_le_of_complexLexLE
    ((canonicalPeriodicEndpoints_spec hp hp1 φ (periodOnePotential_mem ψ)).2.1 m)
  have hmid : canonicalPeriodicMidpoint hp hp1 φ (periodOnePotential_mem ψ) m =
      (((a+b)/2:ℝ):ℂ) := by
    change (l+r)/2 = _
    rw [← hl, ← hr]
    push_cast
    ring
  have hgap : canonicalPeriodicGap hp hp1 φ (periodOnePotential_mem ψ) m =
      ((b-a:ℝ):ℂ) := by
    change r-l = _
    rw [← hl, ← hr]
    push_cast
    ring
  change 0 < (normalizedStandardRoot
    (canonicalPeriodicMidpoint hp hp1 φ (periodOnePotential_mem ψ) m)
    ((canonicalPeriodicGap hp hp1 φ (periodOnePotential_mem ψ) m)^2)
    (x:ℂ)).re
  rw [hmid,hgap]
  simpa only [← Complex.ofReal_pow] using
    normalizedStandardRoot_re_pos_of_lt_leftEndpoint a b x hab hx

/-- Every source standard-root factor is negative on the real axis to
the right of its canonical periodic pair. -/
theorem sourceStandardRoot_re_neg_of_real_gt_right
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (m : ℤ) (x : ℝ)
    (hx : (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) m).re < x) :
    (sourceStandardRoot hp hp1 ψ m (x:ℂ)).re < 0 := by
  let φ := periodOnePotential ψ
  let l := canonicalPeriodicLeft hp hp1 φ (periodOnePotential_mem ψ) m
  let r := canonicalPeriodicRight hp hp1 φ (periodOnePotential_mem ψ) m
  let a := l.re
  let b := r.re
  have hends := canonicalPeriodicEndpoints_im_eq_zero_of_realType
    hp hp1 φ (periodOnePotential_mem ψ)
      (isRealType_periodOnePotential ψ hreal) m
  have hl : (a:ℂ) = l := by
    apply Complex.ext
    · rfl
    · exact hends.1.symm
  have hr : (b:ℂ) = r := by
    apply Complex.ext
    · rfl
    · exact hends.2.symm
  have hab : a ≤ b := re_le_of_complexLexLE
    ((canonicalPeriodicEndpoints_spec hp hp1 φ (periodOnePotential_mem ψ)).2.1 m)
  have hmid : canonicalPeriodicMidpoint hp hp1 φ (periodOnePotential_mem ψ) m =
      (((a+b)/2:ℝ):ℂ) := by
    change (l+r)/2 = _
    rw [← hl, ← hr]
    push_cast
    ring
  have hgap : canonicalPeriodicGap hp hp1 φ (periodOnePotential_mem ψ) m =
      ((b-a:ℝ):ℂ) := by
    change r-l = _
    rw [← hl, ← hr]
    push_cast
    ring
  change (normalizedStandardRoot
    (canonicalPeriodicMidpoint hp hp1 φ (periodOnePotential_mem ψ) m)
    ((canonicalPeriodicGap hp hp1 φ (periodOnePotential_mem ψ) m)^2)
    (x:ℂ)).re < 0
  rw [hmid,hgap]
  simpa only [← Complex.ofReal_pow] using
    normalizedStandardRoot_re_neg_of_gt_rightEndpoint a b x hab hx

/-- At a point inside the selected real gap, every earlier indexed
standard root has negative real value. -/
theorem sourceStandardRoot_re_neg_before_realGap
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    {m n : ℤ} (hmn : m < n) {x : ℝ}
    (hx : x ∈ Ioo
      (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re) :
    (sourceStandardRoot hp hp1 ψ m (x:ℂ)).re < 0 := by
  apply sourceStandardRoot_re_neg_of_real_gt_right hp hp1 ψ hreal m x
  exact (canonicalPeriodicRight_re_lt_left_of_lt hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ)
    (isRealType_periodOnePotential ψ hreal) hmn).trans hx.1

/-- At a point inside the selected real gap, every later indexed
standard root has positive real value. -/
theorem sourceStandardRoot_re_pos_after_realGap
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    {m n : ℤ} (hnm : n < m) {x : ℝ}
    (hx : x ∈ Ioo
      (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re) :
    0 < (sourceStandardRoot hp hp1 ψ m (x:ℂ)).re := by
  apply sourceStandardRoot_re_pos_of_real_lt_left hp hp1 ψ hreal m x
  exact hx.2.trans (canonicalPeriodicRight_re_lt_left_of_lt hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ)
    (isRealType_periodOnePotential ψ hreal) hnm)

end NLS.ZakharovShabat
