import NLS.ComplexAnalysis.ArcoshGapIntegral
import NLS.ZakharovShabat.RealGapDiscriminantLevels

/-!
# The arcosh primitive on a real periodic gap

The signed discriminant equals two at both endpoints of each real
periodic gap and exceeds two in an open gap's interior. Applying the
arcosh endpoint identity gives the real-variable vanishing step for
Lemma 10.11(ii), once integrability of the endpoint kernel is supplied.
-/

noncomputable section
open Set Complex MeasureTheory intervalIntegral
open NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Half the signed real-axis discriminant on the `n`th gap. -/
def realGapHalfDiscriminant (hp : p ≠ ⊤) (φ : PairSpace p)
    (n : ℤ) (x : ℝ) : ℝ :=
  (if n % 2 = 0 then (canonicalDiscriminant hp φ x).re
    else -(canonicalDiscriminant hp φ x).re)/2

/-- The real arcosh derivative integrates to zero across an open
periodic gap. The integrability hypothesis isolates the endpoint
square-root estimate from the fundamental-theorem step. -/
theorem integral_realGapHalfDiscriminant_arcosh_deriv_eq_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (heven : φ ∈ pairParitySubspace 0)
    (hreal : IsRealType φ) (n : ℤ)
    (hint : IntervalIntegrable
      (fun x : ℝ =>
        deriv (realGapHalfDiscriminant hp φ n) x /
          Real.sqrt ((realGapHalfDiscriminant hp φ n x)^2 - 1))
      volume (canonicalPeriodicLeft hp hp1 φ heven n).re
        (canonicalPeriodicRight hp hp1 φ heven n).re) :
    (∫ x in (canonicalPeriodicLeft hp hp1 φ heven n).re..
        (canonicalPeriodicRight hp hp1 φ heven n).re,
      deriv (realGapHalfDiscriminant hp φ n) x /
        Real.sqrt ((realGapHalfDiscriminant hp φ n x)^2 - 1)) = 0 := by
  let a := (canonicalPeriodicLeft hp hp1 φ heven n).re
  let b := (canonicalPeriodicRight hp hp1 φ heven n).re
  let g := realGapHalfDiscriminant hp φ n
  have hab : a ≤ b := re_le_of_complexLexLE
    ((canonicalPeriodicEndpoints_spec hp hp1 φ heven).2.1 n)
  have hcont : ContinuousOn g (Icc a b) := by
    have hc : Continuous (fun x : ℝ => (canonicalDiscriminant hp φ x).re) :=
      continuous_re.comp ((continuousOn_univ.mp
        (analyticOnNhd_canonicalDiscriminant hp hp1 φ heven).continuousOn).comp
          continuous_ofReal)
    by_cases hn : n % 2 = 0
    · have he : g = fun x : ℝ => (canonicalDiscriminant hp φ x).re/2 := by
        funext x
        simp [g,realGapHalfDiscriminant,hn]
      rw [he]
      exact (hc.div_const 2).continuousOn
    · have he : g = fun x : ℝ => -(canonicalDiscriminant hp φ x).re/2 := by
        funext x
        simp [g,realGapHalfDiscriminant,hn]
      rw [he]
      exact (hc.neg.div_const 2).continuousOn
  have hderiv (x : ℝ) (hx : x ∈ Ioo a b) : HasDerivAt g (deriv g x) x := by
    have hd : DifferentiableAt ℝ (fun y : ℝ => (canonicalDiscriminant hp φ y).re) x :=
      ((analyticOnNhd_canonicalDiscriminant hp hp1 φ heven x (mem_univ _)).differentiableAt.hasDerivAt.real_of_complex).differentiableAt
    have hg : DifferentiableAt ℝ g x := by
      by_cases hn : n % 2 = 0
      · have he : g = fun y : ℝ => (canonicalDiscriminant hp φ y).re/2 := by
          funext y
          simp [g,realGapHalfDiscriminant,hn]
        rw [he]
        exact hd.div_const 2
      · have he : g = fun y : ℝ => -(canonicalDiscriminant hp φ y).re/2 := by
          funext y
          simp [g,realGapHalfDiscriminant,hn]
        rw [he]
        exact hd.neg.div_const 2
    exact hg.hasDerivAt
  have hleft : g a = 1 := by
    have hl : ((canonicalPeriodicLeft hp hp1 φ heven n).re : ℂ) =
        canonicalPeriodicLeft hp hp1 φ heven n := by
      apply Complex.ext <;> simp [(canonicalPeriodicEndpoints_im_eq_zero_of_realType
        hp hp1 φ heven hreal n).1]
    have hlevel := (canonicalPeriodicEndpoints_discriminant_of_realType
      hp hp1 φ heven hreal n).1
    dsimp [g,realGapHalfDiscriminant,a]
    rw [hl,hlevel]
    split_ifs <;> norm_num
  have hright : g b = 1 := by
    have hr : ((canonicalPeriodicRight hp hp1 φ heven n).re : ℂ) =
        canonicalPeriodicRight hp hp1 φ heven n := by
      apply Complex.ext <;> simp [(canonicalPeriodicEndpoints_im_eq_zero_of_realType
        hp hp1 φ heven hreal n).2]
    have hlevel := (canonicalPeriodicEndpoints_discriminant_of_realType
      hp hp1 φ heven hreal n).2
    dsimp [g,realGapHalfDiscriminant,b]
    rw [hr,hlevel]
    split_ifs <;> norm_num
  have hgt (x : ℝ) (hx : x ∈ Ioo a b) : 1 < g x := by
    have h := signed_discriminant_gt_two_on_canonicalGap_interior
      hp hp1 φ heven hreal n x hx
    rw [neg_one_zpow_eq_ite] at h
    by_cases hn : n % 2 = 0
    · simp only [Int.even_iff, hn, if_true, one_mul] at h
      simp only [g,realGapHalfDiscriminant,if_pos hn]
      linarith
    · simp only [Int.even_iff, hn, if_false, neg_one_mul] at h
      simp only [g,realGapHalfDiscriminant,if_neg hn]
      linarith
  exact NLS.ComplexAnalysis.integral_deriv_div_sqrt_sq_sub_one_eq_zero
    g (deriv g) a b hab hcont hderiv hleft hright hgt hint

end NLS.ZakharovShabat
