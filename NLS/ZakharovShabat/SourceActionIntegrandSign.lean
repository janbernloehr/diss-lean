import NLS.ComplexAnalysis.SingleCriticalPointSign
import NLS.ZakharovShabat.SourceActionIntegrandCriticalZero
import NLS.ZakharovShabat.SourceLemma10_11RealCalculation

/-!
# Corrected signs of the literal recentered real action integrand

The displayed integrand is nonnegative inside a real gap and strictly
positive away from its unique critical coordinate. Its endpoint integral
is well-defined. The integer parity and positive square root are retained.
-/

noncomputable section
open Set Complex MeasureTheory intervalIntegral
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The literal real integrand is the recentered Section 10 boundary kernel. -/
theorem sourceRecenteredRealActionIntegrand_cast
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p)
    (hreal : IsRealType (CoeffPair.toMax p ψ)) (n : ℤ) (x : ℝ) :
    (sourceRecenteredRealActionIntegrand hp hp1 ψ n x : ℂ) =
      ((x-(canonicalCriticalPoints hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re : ℝ) : ℂ) *
        sourceLemma10_11RealKernel hp ψ n x := by
  have him := discriminant_derivative_im_eq_zero_of_realType hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ) (isRealType_periodOnePotential ψ hreal) x
  have he : ((deriv (canonicalDiscriminant hp (periodOnePotential ψ)) x).re : ℂ) =
      deriv (canonicalDiscriminant hp (periodOnePotential ψ)) x := by
    apply Complex.ext
    · rfl
    · simpa using him.symm
  unfold sourceRecenteredRealActionIntegrand sourceLemma10_11RealKernel
  push_cast
  rw [he]
  ring

/-- The same integrand is minus the centered derivative of the arcosh profile. -/
theorem sourceRecenteredRealActionIntegrand_eq_halfDiscriminant
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p)
    (hreal : IsRealType (CoeffPair.toMax p ψ)) (n : ℤ) (x : ℝ)
    (hx : x ∈ Ioo
      (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n).re
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n).re) :
    sourceRecenteredRealActionIntegrand hp hp1 ψ n x =
      -(x-(canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n).re) *
        (deriv (realGapHalfDiscriminant hp (periodOnePotential ψ) n) x /
          Real.sqrt ((realGapHalfDiscriminant hp (periodOnePotential ψ) n x)^2-1)) := by
  have he := sourceRecenteredRealActionIntegrand_cast hp hp1 ψ hreal n x
  rw [sourceLemma10_11RealKernel_eq_neg_upper hp hp1 ψ hreal n x hx,
    sourceRealGap_upperQuotient_eq_arcosh_deriv hp hp1 ψ hreal n x hx] at he
  have hre := congrArg Complex.re he
  simpa only [mul_re,ofReal_re,ofReal_im,neg_re,neg_im,zero_mul,sub_zero,mul_neg,neg_mul] using hre

/-- The actual half-discriminant increases before the critical coordinate and
decreases after it, for every open real gap and signed index. -/
theorem sourceRealGapHalfDiscriminant_deriv_signs
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p)
    (hreal : IsRealType (CoeffPair.toMax p ψ)) (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n).re) :
    let a := (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n).re
    let b := (canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n).re
    let c := (canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n).re
    let g := realGapHalfDiscriminant hp (periodOnePotential ψ) n
    (∀ x ∈ Ioo a c, 0 < deriv g x) ∧ (∀ x ∈ Ioo c b, deriv g x < 0) := by
  obtain ⟨_,hf,hd,ha,hb,hgt⟩ := realGapHalfDiscriminant_arcosh_gap_data hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ) (isRealType_periodOnePotential ψ hreal) n
  apply NLS.ComplexAnalysis.derivative_signs_of_unique_critical _ _ _ _ _
    (canonicalCriticalPoints_between_of_open_gap hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) (isRealType_periodOnePotential ψ hreal) n hopen)
    hf hd (continuous_realGapHalfDiscriminant_deriv hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).continuousOn (ha.trans hb.symm)
    (fun x hx => by rw [ha]; exact hgt x hx)
  intro x hx hz
  have hzC : deriv (canonicalDiscriminant hp (periodOnePotential ψ)) x = 0 := by
    rw [discriminant_derivative_eq_signed_two_realGapHalfDiscriminant_deriv hp hp1 ψ hreal n x,hz]
    simp
  have he := critical_eq_canonicalCriticalPoints_of_mem_gap hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) (isRealType_periodOnePotential ψ hreal) n (x : ℂ) hzC
    ⟨hx.1.le,hx.2.le⟩
  exact congrArg Complex.re he

/-- Corrected strictness: the literal integrand is positive at every interior
point other than the canonical critical coordinate. -/
theorem sourceRecenteredRealActionIntegrand_pos
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p)
    (hreal : IsRealType (CoeffPair.toMax p ψ)) (n : ℤ) (x : ℝ)
    (hx : x ∈ Ioo
      (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n).re
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n).re)
    (hne : x ≠ (canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n).re) :
    0 < sourceRecenteredRealActionIntegrand hp hp1 ψ n x := by
  let g := realGapHalfDiscriminant hp (periodOnePotential ψ) n
  have hgt := (realGapHalfDiscriminant_arcosh_gap_data hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) (isRealType_periodOnePotential ψ hreal) n).2.2.2.2.2 x hx
  have hden : 0 < Real.sqrt (g x^2-1) := Real.sqrt_pos.mpr (by change 1 < g x at hgt; nlinarith)
  have hs := sourceRealGapHalfDiscriminant_deriv_signs hp hp1 ψ hreal n (hx.1.trans hx.2)
  rw [sourceRecenteredRealActionIntegrand_eq_halfDiscriminant hp hp1 ψ hreal n x hx]
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact mul_pos (neg_pos.mpr (sub_neg.mpr hlt)) (div_pos (hs.1 x ⟨hx.1,hlt⟩) hden)
  · exact mul_pos_of_neg_of_neg (neg_neg_of_pos (sub_pos.mpr hgt))
      (div_neg_of_neg_of_pos (hs.2 x ⟨hgt,hx.2⟩) hden)

/-- Inside the gap the integrand is nonnegative and its only zero is critical. -/
theorem sourceRecenteredRealActionIntegrand_nonneg_and_eq_zero_iff
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p)
    (hreal : IsRealType (CoeffPair.toMax p ψ)) (n : ℤ) (x : ℝ)
    (hx : x ∈ Ioo
      (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n).re
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n).re) :
    0 ≤ sourceRecenteredRealActionIntegrand hp hp1 ψ n x ∧
      (sourceRecenteredRealActionIntegrand hp hp1 ψ n x = 0 ↔
        x = (canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n).re) := by
  by_cases he : x = (canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n).re
  · subst x
    rw [sourceRecenteredRealActionIntegrand_at_critical]
    exact ⟨le_rfl,iff_of_true rfl rfl⟩
  · have hpnt := sourceRecenteredRealActionIntegrand_pos hp hp1 ψ hreal n x hx he
    exact ⟨hpnt.le,iff_of_false hpnt.ne' he⟩

/-- Endpoint singularities of the literal real integrand are integrable;
the statement also includes collapsed gaps. -/
theorem sourceRecenteredRealActionIntegrand_intervalIntegrable
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p)
    (hreal : IsRealType (CoeffPair.toMax p ψ)) (n : ℤ) :
    IntervalIntegrable (sourceRecenteredRealActionIntegrand hp hp1 ψ n) volume
      (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n).re
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n).re := by
  have hc := (sourceLemma10_11RealKernel_intervalIntegrable hp hp1 ψ hreal n).continuousOn_mul
    (g := fun x : ℝ => ((x-(canonicalCriticalPoints hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re : ℝ) : ℂ)) (by fun_prop)
  simp_rw [← sourceRecenteredRealActionIntegrand_cast hp hp1 ψ hreal n] at hc
  exact ⟨hc.1.re,hc.2.re⟩

/-- The displayed numerator is nonnegative on the entire closed real gap,
including its endpoints and collapsed gaps. -/
theorem sourceRecenteredRealActionNumerator_nonneg
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p)
    (hreal : IsRealType (CoeffPair.toMax p ψ)) (n : ℤ) (x : ℝ)
    (hx : x ∈ Icc
      (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n).re
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n).re) :
    0 ≤ (-1 : ℝ)^(n+1) *
      (x-(canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n).re) *
      (deriv (canonicalDiscriminant hp (periodOnePotential ψ)) x).re := by
  let a := (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n).re
  let b := (canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n).re
  let c := (canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n).re
  let N : ℝ → ℝ := fun y => (-1 : ℝ)^(n+1)*(y-c)*
    (deriv (canonicalDiscriminant hp (periodOnePotential ψ)) y).re
  change x ∈ Icc a b at hx
  change 0 ≤ N x
  by_cases he : a = b
  · have hc := canonicalCriticalPoints_mem_canonicalPeriodicGap hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) (isRealType_periodOnePotential ψ hreal) n
    change a ≤ c ∧ c ≤ b at hc
    have hxc : x = c := by linarith [hx.1,hx.2,hc.1,hc.2]
    simp only [N,hxc,sub_self,mul_zero,zero_mul,le_refl]
  · have hD : Continuous (fun y : ℝ =>
        (deriv (canonicalDiscriminant hp (periodOnePotential ψ)) y).re) :=
      continuous_re.comp ((continuousOn_univ.mp (analyticOnNhd_discriminant_derivative hp hp1
        (periodOnePotential ψ) (periodOnePotential_mem ψ)).continuousOn).comp continuous_ofReal)
    have hN : Continuous N := (continuous_const.mul (continuous_id.sub continuous_const)).mul hD
    have hsub : Ioo a b ⊆ {y | 0 ≤ N y} := by
      intro y hy
      have h := (sourceRecenteredRealActionIntegrand_nonneg_and_eq_zero_iff hp hp1 ψ hreal n y hy).1
      change 0 ≤ N y / Real.sqrt ((canonicalDiscriminant hp (periodOnePotential ψ) y).re^2-4) at h
      rcases div_nonneg_iff.mp h with hpos | hneg
      · exact hpos.1
      · exact False.elim ((not_le_of_gt
          (sourceRecenteredRealActionIntegrand_denominator_pos hp hp1 ψ hreal n y hy)) hneg.2)
    have hall := closure_minimal hsub (isClosed_le continuous_const hN)
    rw [closure_Ioo he] at hall
    exact hall hx


end NLS.ZakharovShabat
