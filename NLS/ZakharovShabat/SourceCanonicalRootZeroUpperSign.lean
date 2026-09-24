import NLS.ZakharovShabat.SourceStandardRootOmittedZeroPositive
import NLS.ZakharovShabat.RealGapCanonicalRootValue
import NLS.ZakharovShabat.RealGapCanonicalRootRealAxis
import NLS.ZakharovShabat.SourceCriticalRootRatioGapSideIntegral

/-!
# Upper canonical-root orientation on the central real gap

The upper side of the selected standard root contributes a positive
real factor on an open real gap. The omitted product is positive for
index zero, so the upper boundary value of the full canonical root
is positive there.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The upper canonical-root boundary value is strictly positive on
the interior of an open central real-type gap. -/
theorem sourceCanonicalRootGapUpperValue_re_pos_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) 0).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) 0).re)
    {t : ℝ} (ht : t ∈ Ioo (-1) 1) :
    0 < (sourceCanonicalRootGapUpperValue hp hp1 ψ 0 t).re := by
  let a := (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) 0).re
  let b := (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) 0).re
  let d : ℝ := (b-a)/2
  let s : ℝ := Real.sqrt (1-t^2)
  let z := sourceCanonicalRootGapPoint hp hp1 ψ 0 t
  let P := sourceStandardRootOmittedProduct hp hp1 0 ψ z
  have hd : 0 < d := by
    dsimp [d,a,b]
    exact div_pos (sub_pos.mpr hopen) (by norm_num)
  have hrad : 0 < 1-t^2 := by nlinarith [ht.1,ht.2]
  have hs : 0 < s := Real.sqrt_pos.mpr hrad
  have hx : realGapAffinePoint hp hp1 ψ 0 t ∈ Ioo a b :=
    realGapAffinePoint_mem_Ioo hp hp1 ψ 0 hopen ht
  have hz : z = (realGapAffinePoint hp hp1 ψ 0 t : ℂ) :=
    sourceCanonicalRootGapPoint_eq_ofReal_realGapAffinePoint
      hp hp1 ψ hreal 0 t
  have hP : 0 < P.re := by
    dsimp [P]
    rw [hz]
    exact sourceStandardRootOmittedProduct_re_pos_on_zeroGap
      hp hp1 ψ hreal _ hx
  have hhalf : sourceStandardRootHalfGap hp hp1 ψ 0 = (d:ℂ) := by
    simpa only [d,a,b] using
      sourceStandardRootHalfGap_eq_ofReal_affineJacobian
        hp hp1 ψ hreal 0
  have hcoef : (2:ℂ)*I*(-(d:ℂ)*I*(s:ℂ)) = ((2*d*s:ℝ):ℂ) := by
    calc
      _ = -((2:ℂ)*(d:ℂ)*(s:ℂ))*(I*I) := by ring
      _ = ((2*d*s:ℝ):ℂ) := by simp [Complex.I_mul_I]
  change 0 < ((2:ℂ)*I*(-sourceStandardRootHalfGap hp hp1 ψ 0*I*(s:ℂ))*P).re
  rw [hhalf,hcoef]
  have hscale : 0 < 2*d*s := by positivity
  have hmul : 0 < (2*d*s)*P.re := mul_pos hscale hP
  simpa [Complex.mul_re] using hmul

/-- The positive branch of the arcosh square root is the actual upper
canonical-root boundary value on the open central gap. -/
theorem sourceCanonicalRootGapUpperValue_eq_two_sqrt_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) 0).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) 0).re)
    {t : ℝ} (ht : t ∈ Ioo (-1) 1) :
    sourceCanonicalRootGapUpperValue hp hp1 ψ 0 t =
      ((2*Real.sqrt ((realGapHalfDiscriminant hp
        (periodOnePotential ψ) 0 (realGapAffinePoint hp hp1 ψ 0 t))^2-1):ℝ):ℂ) := by
  have hpos := sourceCanonicalRootGapUpperValue_re_pos_zero
    hp hp1 ψ hreal hopen ht
  have hrad := realGapHalfDiscriminant_radicand_pos_at_affinePoint
    hp hp1 ψ hreal 0 hopen ht
  have hs : 0 < Real.sqrt
      ((realGapHalfDiscriminant hp (periodOnePotential ψ) 0
        (realGapAffinePoint hp hp1 ψ 0 t))^2-1) :=
    Real.sqrt_pos.mpr hrad
  rcases sourceCanonicalRootGapUpperValue_eq_or_eq_neg_two_sqrt
      hp hp1 ψ hreal 0 hopen with hplus | hminus
  · exact hplus t ht
  · have hneg : (sourceCanonicalRootGapUpperValue hp hp1 ψ 0 t).re < 0 := by
      rw [hminus t ht]
      simp only [Complex.neg_re,Complex.ofReal_re]
      linarith
    linarith

/-- In real spectral coordinates, the central upper root is the
positive arcosh denominator throughout the open gap. -/
theorem realGapCanonicalRootUpperValue_eq_two_sqrt_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) 0).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) 0).re)
    {x : ℝ}
    (hx : x ∈ Ioo
      (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) 0).re
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) 0).re) :
    realGapCanonicalRootUpperValue hp hp1 ψ 0 x =
      ((2*Real.sqrt ((realGapHalfDiscriminant hp
        (periodOnePotential ψ) 0 x)^2-1):ℝ):ℂ) := by
  have ht := realGapInverseCoordinate_mem_Ioo hp hp1 ψ 0 hx
  unfold realGapCanonicalRootUpperValue
  rw [sourceCanonicalRootGapUpperValue_eq_two_sqrt_zero
    hp hp1 ψ hreal hopen ht,
    realGapAffinePoint_inverse hp hp1 ψ 0 hopen x]

end NLS.ZakharovShabat
