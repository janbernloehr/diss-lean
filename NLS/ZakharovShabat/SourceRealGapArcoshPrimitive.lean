import NLS.ZakharovShabat.SourceActionAllGapPositive

/-! # The exact arcosh primitive of the canonical gap-side quotient

The canonical upper-root orientation cancels the discriminant parity.
The resulting quotient is the derivative of the positive real arcosh
profile. Integrability at the endpoints gives exact partial integrals,
with the opposite sign on the lower side.
-/
noncomputable section
open Set Complex MeasureTheory intervalIntegral
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def sourceRealGapArcoshProfile (hp : p ≠ ⊤) (φ : CoeffPair p) (n : ℤ) (x : ℝ) : ℝ :=
  Real.arcosh (realGapHalfDiscriminant hp (periodOnePotential φ) n x)

/-- The actual upper-side canonical quotient has the positive arcosh
orientation at every signed index. -/
theorem sourceRealGap_upperQuotient_eq_arcosh_deriv
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) (x : ℝ)
    (hx : x ∈ Ioo
      (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re
      (canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re) :
    deriv (canonicalDiscriminant hp (periodOnePotential φ)) x /
      realGapCanonicalRootUpperValue hp hp1 φ n x =
      ((deriv (realGapHalfDiscriminant hp (periodOnePotential φ) n) x /
        Real.sqrt ((realGapHalfDiscriminant hp (periodOnePotential φ) n x)^2-1) : ℝ) : ℂ) := by
  have hopen := hx.1.trans hx.2
  have hrad := realGapHalfDiscriminant_radicand_pos_at_affinePoint hp hp1 φ hφ n hopen
    (realGapInverseCoordinate_mem_Ioo hp hp1 φ n hx)
  rw [realGapAffinePoint_inverse hp hp1 φ n hopen x] at hrad
  rw [discriminant_derivative_eq_signed_two_realGapHalfDiscriminant_deriv hp hp1 φ hφ n x,
    realGapCanonicalRootUpperValue_eq_signed_two_sqrt hp hp1 φ hφ n hopen hx]
  have hs : (((-1 : ℝ)^n.natAbs : ℝ) : ℂ) ≠ 0 := by norm_cast; exact pow_ne_zero _ (by norm_num)
  have hv : (Real.sqrt ((realGapHalfDiscriminant hp (periodOnePotential φ) n x)^2-1) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hrad).ne'
  push_cast
  field_simp

/-- The arcosh profile has the actual upper boundary quotient as its
real-variable derivative. -/
theorem hasDerivAt_sourceRealGapArcoshProfile
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) (x : ℝ)
    (hx : x ∈ Ioo
      (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re
      (canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re) :
    HasDerivAt (fun t : ℝ => (sourceRealGapArcoshProfile hp φ n t : ℂ))
      (deriv (canonicalDiscriminant hp (periodOnePotential φ)) x /
        realGapCanonicalRootUpperValue hp hp1 φ n x) x := by
  obtain ⟨_,_,hd,_,_,hgt⟩ := realGapHalfDiscriminant_arcosh_gap_data hp hp1
    (periodOnePotential φ) (periodOnePotential_mem φ) (isRealType_periodOnePotential φ hφ) n
  rw [sourceRealGap_upperQuotient_eq_arcosh_deriv hp hp1 φ hφ n x hx]
  have h := (Real.hasDerivAt_arcosh (hgt x hx)).comp x (hd x hx)
  simpa only [sourceRealGapArcoshProfile,Function.comp_def,div_eq_mul_inv,mul_comm] using! h.ofReal_comp

/-- Continuity, zero endpoint values, and strict interior positivity
of the real arcosh profile. -/
theorem sourceRealGapArcoshProfile_spec
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) :
    let a := (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re
    let b := (canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re
    ContinuousOn (sourceRealGapArcoshProfile hp φ n) (Icc a b) ∧
      sourceRealGapArcoshProfile hp φ n a = 0 ∧ sourceRealGapArcoshProfile hp φ n b = 0 ∧
      ∀ x ∈ Ioo a b, 0 < sourceRealGapArcoshProfile hp φ n x := by
  obtain ⟨hab,hc,_,ha,hb,hgt⟩ := realGapHalfDiscriminant_arcosh_gap_data hp hp1
    (periodOnePotential φ) (periodOnePotential_mem φ) (isRealType_periodOnePotential φ hφ) n
  refine ⟨Real.continuousOn_arcosh.comp hc ?_,?_,?_,fun x hx => Real.arcosh_pos (hgt x hx)⟩
  · intro x hx
    change (1 : ℝ) ≤ realGapHalfDiscriminant hp (periodOnePotential φ) n x
    rcases eq_or_lt_of_le hx.1 with h | h
    · simpa only [← h,ha] using (le_refl (1 : ℝ))
    rcases eq_or_lt_of_le hx.2 with h' | h'
    · simpa only [h',hb] using (le_refl (1 : ℝ))
    · exact (hgt x ⟨h,h'⟩).le
  · simp only [sourceRealGapArcoshProfile,ha,Real.arcosh_zero]
  · simp only [sourceRealGapArcoshProfile,hb,Real.arcosh_zero]

/-- Both actual canonical side kernels are integrable across the whole
closed gap, including through their endpoint singularities. -/
theorem sourceRealGap_sideQuotients_intervalIntegrable
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) :
    let a := (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re
    let b := (canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re
    IntervalIntegrable (fun x : ℝ => deriv (canonicalDiscriminant hp (periodOnePotential φ)) x /
      realGapCanonicalRootUpperValue hp hp1 φ n x) volume a b ∧
    IntervalIntegrable (fun x : ℝ => deriv (canonicalDiscriminant hp (periodOnePotential φ)) x /
      sourceCanonicalRootGapLowerValue hp hp1 φ n (realGapInverseCoordinate hp hp1 φ n x)) volume a b := by
  let a := (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re
  let b := (canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re
  have hab : a ≤ b := (realGapHalfDiscriminant_arcosh_gap_data hp hp1 (periodOnePotential φ)
    (periodOnePotential_mem φ) (isRealType_periodOnePotential φ hφ) n).1
  change IntervalIntegrable _ volume a b ∧ IntervalIntegrable _ volume a b
  by_cases he : a = b
  · rw [he]
    exact ⟨IntervalIntegrable.refl,IntervalIntegrable.refl⟩
  have hreal := intervalIntegrable_realGapHalfDiscriminant_arcosh_deriv hp hp1 φ hφ n (lt_of_le_of_ne hab he)
  have hc : IntervalIntegrable (fun x : ℝ =>
      ((deriv (realGapHalfDiscriminant hp (periodOnePotential φ) n) x /
        Real.sqrt ((realGapHalfDiscriminant hp (periodOnePotential φ) n x)^2-1) : ℝ) : ℂ)) volume a b :=
    ⟨hreal.1.ofReal,hreal.2.ofReal⟩
  have hu : IntervalIntegrable (fun x : ℝ => deriv (canonicalDiscriminant hp (periodOnePotential φ)) x /
      realGapCanonicalRootUpperValue hp hp1 φ n x) volume a b := by
    apply (intervalIntegrable_congr_uIoo ?_).mpr hc
    rw [uIoo_of_le hab]
    intro x hx
    exact sourceRealGap_upperQuotient_eq_arcosh_deriv hp hp1 φ hφ n x hx
  refine ⟨hu,?_⟩
  have heq (x : ℝ) : sourceCanonicalRootGapLowerValue hp hp1 φ n (realGapInverseCoordinate hp hp1 φ n x) =
      -realGapCanonicalRootUpperValue hp hp1 φ n x :=
    neg_eq_iff_eq_neg.mp (sourceCanonicalRootGapUpperValue_eq_neg_lower hp hp1 φ n _).symm
  simpa only [heq,div_neg] using! hu.neg

/-- Exact partial integral from the left endpoint to any point of the
closed gap, with endpoint integrability proved by the library. -/
theorem sourceRealGap_upperIntegral_eq_arcosh
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) (x : ℝ)
    (hx : x ∈ Icc
      (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re
      (canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re) :
    (∫ t in (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re..x,
      deriv (canonicalDiscriminant hp (periodOnePotential φ)) t /
        realGapCanonicalRootUpperValue hp hp1 φ n t) = (sourceRealGapArcoshProfile hp φ n x : ℂ) := by
  let a := (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re
  let b := (canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re
  let g := realGapHalfDiscriminant hp (periodOnePotential φ) n
  change (∫ t in a..x, _) = _
  by_cases he : a = x
  · have hs := (sourceRealGapArcoshProfile_spec hp hp1 φ hφ n).2.1
    rw [← he]
    simpa only [intervalIntegral.integral_same,ofReal_zero] using (congrArg (fun r : ℝ => (r : ℂ)) hs).symm
  have hax : a < x := lt_of_le_of_ne hx.1 he
  have hab : a < b := hax.trans_le hx.2
  obtain ⟨_,hc,hd,ha,_,hgt⟩ := realGapHalfDiscriminant_arcosh_gap_data hp hp1
    (periodOnePotential φ) (periodOnePotential_mem φ) (isRealType_periodOnePotential φ hφ) n
  have hsub : Icc a x ⊆ Icc a b := Icc_subset_Icc le_rfl hx.2
  have hint := (intervalIntegrable_realGapHalfDiscriminant_arcosh_deriv hp hp1 φ hφ n hab).mono_set (c := a) (d := x)
    (by
      change Set.uIcc a x ⊆ Set.uIcc a b
      rw [Set.uIcc_of_le (show a ≤ x from hx.1),Set.uIcc_of_le hab.le]
      exact hsub)
  have hderiv (t : ℝ) (ht : t ∈ Ioo a x) : HasDerivAt (sourceRealGapArcoshProfile hp φ n)
      (deriv g t / Real.sqrt (g t^2-1)) t := by
    have ht' : t ∈ Ioo a b := ⟨ht.1,ht.2.trans_le hx.2⟩
    simpa only [sourceRealGapArcoshProfile,Function.comp_def,div_eq_mul_inv,mul_comm,g] using!
      (Real.hasDerivAt_arcosh (hgt t ht')).comp t (hd t ht')
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx.1
    ((sourceRealGapArcoshProfile_spec hp hp1 φ hφ n).1.mono hsub) hderiv hint
  have hleft := (sourceRealGapArcoshProfile_spec hp hp1 φ hφ n).2.1
  rw [hleft,sub_zero] at hFTC
  calc
    _ = ∫ t in a..x, ((deriv g t / Real.sqrt (g t^2-1) : ℝ) : ℂ) := by
      apply intervalIntegral.integral_congr_uIoo
      rw [uIoo_of_le hx.1]
      intro t ht
      exact sourceRealGap_upperQuotient_eq_arcosh_deriv hp hp1 φ hφ n t ⟨ht.1,ht.2.trans_le hx.2⟩
    _ = _ := by rw [intervalIntegral.integral_ofReal,hFTC]

/-- The lower canonical sheet gives the negative arcosh profile. -/
theorem sourceRealGap_lowerIntegral_eq_neg_arcosh
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) (x : ℝ)
    (hx : x ∈ Icc
      (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re
      (canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re) :
    (∫ t in (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re..x,
      deriv (canonicalDiscriminant hp (periodOnePotential φ)) t /
        sourceCanonicalRootGapLowerValue hp hp1 φ n (realGapInverseCoordinate hp hp1 φ n t)) =
      -(sourceRealGapArcoshProfile hp φ n x : ℂ) := by
  have he (t : ℝ) : sourceCanonicalRootGapLowerValue hp hp1 φ n (realGapInverseCoordinate hp hp1 φ n t) =
      -realGapCanonicalRootUpperValue hp hp1 φ n t :=
    neg_eq_iff_eq_neg.mp (sourceCanonicalRootGapUpperValue_eq_neg_lower hp hp1 φ n _).symm
  simp_rw [he,div_neg]
  rw [intervalIntegral.integral_neg,sourceRealGap_upperIntegral_eq_arcosh hp hp1 φ hφ n x hx]

end NLS.ZakharovShabat
