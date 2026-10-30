import NLS.ZakharovShabat.SourceRealGapArcoshPrimitive
import NLS.ZakharovShabat.SourceCriticalRootPeriodZero

/-!
# The literal real-gap calculation in Lemma 10.11

The parity-weighted quotient with the positive real square root is the
lower canonical boundary quotient. Its partial integral is the negative
arcosh profile. The doubled partial formula fixes the printed coefficient
before evaluation at the two zero endpoint values. The final circle
identity retains every original disk and the existing common domain.
-/

noncomputable section
open Set Complex MeasureTheory intervalIntegral
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The half-discriminant uses the literal integer-index parity of the source. -/
theorem realGapHalfDiscriminant_eq_signed (hp : p ≠ ⊤) (φ : PairSpace p)
    (n : ℤ) (x : ℝ) :
    realGapHalfDiscriminant hp φ n x =
      (-1 : ℝ)^n * (canonicalDiscriminant hp φ x).re / 2 := by
  by_cases hn : n % 2 = 0
  · have he : Even n := Int.even_iff.mpr hn
    simp [realGapHalfDiscriminant,hn,he.neg_one_zpow]
  · have ho : Odd n := Int.not_even_iff_odd.mp (fun he => hn (Int.even_iff.mp he))
    simp [realGapHalfDiscriminant,hn,ho.neg_one_zpow]

/-- The integrand printed in the real-locus proof, before the outer factor two. -/
def sourceLemma10_11RealKernel (hp : p ≠ ⊤) (ψ : CoeffPair p) (n : ℤ) (x : ℝ) : ℂ :=
  (-1 : ℂ)^(n+1) * deriv (canonicalDiscriminant hp (periodOnePotential ψ)) x /
    (Real.sqrt ((canonicalDiscriminant hp (periodOnePotential ψ) x).re^2-4) : ℂ)

private theorem neg_one_zpow_eq_natAbs (n : ℤ) : (-1 : ℂ)^n = (-1 : ℂ)^n.natAbs := by
  by_cases he : Even n
  · rw [he.neg_one_zpow,(Int.natAbs_even.mpr he).neg_one_pow]
  · have ho : Odd n := Int.not_even_iff_odd.mp he
    rw [ho.neg_one_zpow,(Int.natAbs_odd.mpr ho).neg_one_pow]

/-- The printed parity and positive square root give the negative upper-side quotient. -/
theorem sourceLemma10_11RealKernel_eq_neg_upper
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p)
    (hreal : IsRealType (CoeffPair.toMax p ψ)) (n : ℤ) (x : ℝ)
    (hx : x ∈ Ioo
      (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n).re
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n).re) :
    sourceLemma10_11RealKernel hp ψ n x =
      -(deriv (canonicalDiscriminant hp (periodOnePotential ψ)) x /
        realGapCanonicalRootUpperValue hp hp1 ψ n x) := by
  let g := realGapHalfDiscriminant hp (periodOnePotential ψ) n x
  have hrad : (canonicalDiscriminant hp (periodOnePotential ψ) x).re^2-4 = 4*(g^2-1) := by
    dsimp [g,realGapHalfDiscriminant]
    split_ifs <;> ring
  have hsqrt : Real.sqrt ((canonicalDiscriminant hp (periodOnePotential ψ) x).re^2-4) =
      2*Real.sqrt (g^2-1) := by
    rw [hrad,Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    have hfour : Real.sqrt 4 = 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 4),Real.sqrt_nonneg 4]
    rw [hfour]
  have hsign : (-1 : ℂ)^(n+1) = -((-1 : ℂ)^n.natAbs) := by
    rw [zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0),neg_one_zpow_eq_natAbs]
    simp
  have hs : (((-1 : ℝ)^n.natAbs : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (pow_ne_zero n.natAbs (by norm_num : (-1 : ℝ) ≠ 0))
  have hgt := (realGapHalfDiscriminant_arcosh_gap_data hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ) (isRealType_periodOnePotential ψ hreal) n).2.2.2.2.2 x hx
  have hpos : 0 < g^2-1 := by
    change 1 < g at hgt
    nlinarith
  have hv : (Real.sqrt (g^2-1) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hpos).ne'
  rw [sourceLemma10_11RealKernel,hsign,hsqrt,
    realGapCanonicalRootUpperValue_eq_signed_two_sqrt hp hp1 ψ hreal n (hx.1.trans hx.2) hx]
  change -((-1 : ℂ)^n.natAbs) * _ / ((2*Real.sqrt (g^2-1) : ℝ) : ℂ) =
    -(_ / (((-1 : ℝ)^n.natAbs * (2*Real.sqrt (g^2-1)) : ℝ) : ℂ))
  push_cast at hs ⊢
  have hsq : ((-1 : ℂ)^n.natAbs)^2 = 1 := by rw [← pow_mul,mul_comm, pow_mul]; simp
  field_simp
  linear_combination -hsq * deriv (canonicalDiscriminant hp (periodOnePotential ψ)) x

/-- The same literal kernel is the actual lower canonical boundary quotient. -/
theorem sourceLemma10_11RealKernel_eq_lower
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p)
    (hreal : IsRealType (CoeffPair.toMax p ψ)) (n : ℤ) (x : ℝ)
    (hx : x ∈ Ioo
      (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n).re
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n).re) :
    sourceLemma10_11RealKernel hp ψ n x =
      deriv (canonicalDiscriminant hp (periodOnePotential ψ)) x /
        sourceCanonicalRootGapLowerValue hp hp1 ψ n (realGapInverseCoordinate hp hp1 ψ n x) := by
  rw [sourceLemma10_11RealKernel_eq_neg_upper hp hp1 ψ hreal n x hx]
  have he : sourceCanonicalRootGapLowerValue hp hp1 ψ n (realGapInverseCoordinate hp hp1 ψ n x) =
      -realGapCanonicalRootUpperValue hp hp1 ψ n x :=
    neg_eq_iff_eq_neg.mp (sourceCanonicalRootGapUpperValue_eq_neg_lower hp hp1 ψ n _).symm
  rw [he,div_neg]

/-- The printed kernel is integrable, including its square-root endpoint singularities. -/
theorem sourceLemma10_11RealKernel_intervalIntegrable
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p)
    (hreal : IsRealType (CoeffPair.toMax p ψ)) (n : ℤ) :
    IntervalIntegrable (sourceLemma10_11RealKernel hp ψ n) volume
      (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n).re
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n).re := by
  have hab := (realGapHalfDiscriminant_arcosh_gap_data hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ) (isRealType_periodOnePotential ψ hreal) n).1
  apply (intervalIntegrable_congr_uIoo ?_).mpr
    (sourceRealGap_sideQuotients_intervalIntegrable hp hp1 ψ hreal n).1.neg
  rw [uIoo_of_le hab]
  intro x hx
  exact sourceLemma10_11RealKernel_eq_neg_upper hp hp1 ψ hreal n x hx

/-- The printed factor -2 already holds for every partial gap integral. -/
theorem sourceLemma10_11RealKernel_twice_partialIntegral
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p)
    (hreal : IsRealType (CoeffPair.toMax p ψ)) (n : ℤ) (x : ℝ)
    (hx : x ∈ Icc
      (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n).re
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n).re) :
    2 * (∫ t in (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re..x, sourceLemma10_11RealKernel hp ψ n t) =
      -2 * (Real.arcosh ((-1 : ℝ)^n *
        (canonicalDiscriminant hp (periodOnePotential ψ) x).re / 2) : ℂ) := by
  have he : (∫ t in (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re..x, sourceLemma10_11RealKernel hp ψ n t) =
      -(sourceRealGapArcoshProfile hp ψ n x : ℂ) := by
    rw [← sourceRealGap_lowerIntegral_eq_neg_arcosh hp hp1 ψ hreal n x hx]
    apply intervalIntegral.integral_congr_uIoo
    rw [uIoo_of_le hx.1]
    intro t ht
    exact sourceLemma10_11RealKernel_eq_lower hp hp1 ψ hreal n t ⟨ht.1,ht.2.trans_le hx.2⟩
  rw [he,sourceRealGapArcoshProfile,realGapHalfDiscriminant_eq_signed]
  ring

/-- The complete displayed calculation on every original positively oriented circle.
The partial-integral theorem above fixes the coefficient before endpoint evaluation. -/
theorem SourceLemma10_11CircleData.originalCircle_realCalculation
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    (h : SourceLemma10_11CircleData hp hp1 W)
    {D : ℤ → Set ℂ} {c : ℝ} (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (ψ : CoeffPair p) (hψW : ψ ∈ W) (hψV : ψ ∈ V)
    (hreal : IsRealType (CoeffPair.toMax p ψ)) (n : ℤ)
    (o R : ℝ) (hR : 0 < R) (hDn : D n = Metric.ball (o : ℂ) R) :
    let a := (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n).re
    let b := (canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n).re
    let A := fun x : ℝ => Real.arcosh ((-1 : ℝ)^n *
      (canonicalDiscriminant hp (periodOnePotential ψ) x).re / 2)
    ((∮ z in C((o : ℂ),R), sourceCriticalRootRatioJoint hp hp1 (z,ψ)) =
      2 * (∫ t in a..b, sourceLemma10_11RealKernel hp ψ n t)) ∧
    (2 * (∫ t in a..b, sourceLemma10_11RealKernel hp ψ n t) =
      -2 * ((A b : ℂ)-(A a : ℂ))) ∧
    -2 * ((A b : ℂ)-(A a : ℂ)) = 0 := by
  let a := (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n).re
  let b := (canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n).re
  let A := fun x : ℝ => Real.arcosh ((-1 : ℝ)^n *
    (canonicalDiscriminant hp (periodOnePotential ψ) x).re / 2)
  have he (x : ℝ) : sourceRealGapArcoshProfile hp ψ n x = A x := by
    rw [sourceRealGapArcoshProfile,realGapHalfDiscriminant_eq_signed]
  have hs := sourceRealGapArcoshProfile_spec hp hp1 ψ hreal n
  have ha : A a = 0 := (he a).symm.trans hs.2.1
  have hb : A b = 0 := (he b).symm.trans hs.2.2.1
  have hab := (realGapHalfDiscriminant_arcosh_gap_data hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ) (isRealType_periodOnePotential ψ hreal) n).1
  have hi := sourceLemma10_11RealKernel_twice_partialIntegral hp hp1 ψ hreal n b ⟨hab,le_rfl⟩
  change 2 * (∫ t in a..b, sourceLemma10_11RealKernel hp ψ n t) = -2 * (A b : ℂ) at hi
  have hc : (∮ z in C((o : ℂ),R), sourceCriticalRootRatioJoint hp hp1 (z,ψ)) = 0 :=
    h.zero ψ hψW n (hD.periodCircle ψ hψV n o R hR hDn)
  refine ⟨?_,?_,?_⟩
  · rw [hc,hi,hb]
    simp
  · change 2 * (∫ t in a..b, sourceLemma10_11RealKernel hp ψ n t) =
      -2 * ((A b : ℂ)-(A a : ℂ))
    simpa only [ha,ofReal_zero,sub_zero] using hi
  · change -2 * ((A b : ℂ)-(A a : ℂ)) = 0
    simp only [ha,hb,ofReal_zero,sub_self,mul_zero]

end NLS.ZakharovShabat
