import NLS.ZakharovShabat.SourceStandardRootOmittedParitySign
import NLS.ZakharovShabat.SourceCanonicalRootZeroUpperSign

/-!
# Upper canonical-root orientation on every real gap

The selected upper standard-root factor is positive. Consequently,
the full canonical root inherits the parity sign of the omitted
product, fixing its branch relative to the positive arcosh square root.
-/

noncomputable section
set_option maxHeartbeats 800000
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The upper canonical-root boundary value has real sign
`(-1)^|n|` on the interior of every open real-type gap. -/
theorem sourceCanonicalRootGapUpperValue_signed_re_pos
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re)
    {t : ℝ} (ht : t ∈ Ioo (-1) 1) :
    0 < (-1:ℝ)^n.natAbs *
      (sourceCanonicalRootGapUpperValue hp hp1 ψ n t).re := by
  let a := (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n).re
  let b := (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n).re
  let d : ℝ := (b-a)/2
  let s : ℝ := Real.sqrt (1-t^2)
  let z := sourceCanonicalRootGapPoint hp hp1 ψ n t
  let P := sourceStandardRootOmittedProduct hp hp1 n ψ z
  have hd : 0 < d := by
    dsimp [d,a,b]
    exact div_pos (sub_pos.mpr hopen) (by norm_num)
  have hrad : 0 < 1-t^2 := by nlinarith [ht.1,ht.2]
  have hs : 0 < s := Real.sqrt_pos.mpr hrad
  have hx : realGapAffinePoint hp hp1 ψ n t ∈ Ioo a b :=
    realGapAffinePoint_mem_Ioo hp hp1 ψ n hopen ht
  have hz : z = (realGapAffinePoint hp hp1 ψ n t : ℂ) :=
    sourceCanonicalRootGapPoint_eq_ofReal_realGapAffinePoint
      hp hp1 ψ hreal n t
  have hP : 0 < (-1:ℝ)^n.natAbs * P.re := by
    dsimp [P]
    rw [hz]
    exact sourceStandardRootOmittedProduct_signed_re_pos_on_realGap
      hp hp1 ψ hreal n _ hx
  have hhalf : sourceStandardRootHalfGap hp hp1 ψ n = (d:ℂ) := by
    simpa only [d,a,b] using
      sourceStandardRootHalfGap_eq_ofReal_affineJacobian
        hp hp1 ψ hreal n
  have hcoef : (2:ℂ)*I*(-(d:ℂ)*I*(s:ℂ)) = ((2*d*s:ℝ):ℂ) := by
    calc
      _ = -((2:ℂ)*(d:ℂ)*(s:ℂ))*(I*I) := by ring
      _ = ((2*d*s:ℝ):ℂ) := by simp [Complex.I_mul_I]
  change 0 < (-1:ℝ)^n.natAbs *
    ((2:ℂ)*I*(-sourceStandardRootHalfGap hp hp1 ψ n*I*(s:ℂ))*P).re
  rw [hhalf,hcoef]
  have hscale : 0 < 2*d*s := by positivity
  have hmul : 0 < (2*d*s)*((-1:ℝ)^n.natAbs*P.re) :=
    mul_pos hscale hP
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero]
  convert hmul using 1; ring

/-- The upper canonical-root value is the positive arcosh square
root multiplied by the parity sign of the selected gap. -/
theorem sourceCanonicalRootGapUpperValue_eq_signed_two_sqrt
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re)
    {t : ℝ} (ht : t ∈ Ioo (-1) 1) :
    sourceCanonicalRootGapUpperValue hp hp1 ψ n t =
      (((-1:ℝ)^n.natAbs *
        (2*Real.sqrt ((realGapHalfDiscriminant hp
          (periodOnePotential ψ) n (realGapAffinePoint hp hp1 ψ n t))^2-1)):ℝ):ℂ) := by
  let r : ℝ := 2*Real.sqrt ((realGapHalfDiscriminant hp
    (periodOnePotential ψ) n (realGapAffinePoint hp hp1 ψ n t))^2-1)
  have hrad := realGapHalfDiscriminant_radicand_pos_at_affinePoint
    hp hp1 ψ hreal n hopen ht
  have hr : 0 < r := by
    dsimp [r]
    exact mul_pos (by norm_num) (Real.sqrt_pos.mpr hrad)
  have hpos := sourceCanonicalRootGapUpperValue_signed_re_pos
    hp hp1 ψ hreal n hopen ht
  rcases sourceCanonicalRootGapUpperValue_eq_or_eq_neg_two_sqrt
      hp hp1 ψ hreal n hopen with hplus | hminus
  · have heq := hplus t ht
    have hs : (-1:ℝ)^n.natAbs = 1 := by
      rcases neg_one_pow_eq_or ℝ n.natAbs with hs | hs
      · exact hs
      · rw [heq, hs] at hpos
        change 0 < (-1:ℝ) * r at hpos
        linarith
    simpa only [r,hs,one_mul] using heq
  · have heq := hminus t ht
    have hs : (-1:ℝ)^n.natAbs = -1 := by
      rcases neg_one_pow_eq_or ℝ n.natAbs with hs | hs
      · rw [heq, hs] at hpos
        change 0 < (1:ℝ) * -r at hpos
        linarith
      · exact hs
    simpa only [r,hs,neg_mul,one_mul,Complex.ofReal_neg] using heq

/-- In real spectral coordinates, the upper canonical root equals
the positive arcosh square root with the gap's parity sign. -/
theorem realGapCanonicalRootUpperValue_eq_signed_two_sqrt
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re)
    {x : ℝ}
    (hx : x ∈ Ioo
      (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re) :
    realGapCanonicalRootUpperValue hp hp1 ψ n x =
      (((-1:ℝ)^n.natAbs *
        (2*Real.sqrt ((realGapHalfDiscriminant hp
          (periodOnePotential ψ) n x)^2-1)):ℝ):ℂ) := by
  have ht := realGapInverseCoordinate_mem_Ioo hp hp1 ψ n hx
  unfold realGapCanonicalRootUpperValue
  rw [sourceCanonicalRootGapUpperValue_eq_signed_two_sqrt
    hp hp1 ψ hreal n hopen ht,
    realGapAffinePoint_inverse hp hp1 ψ n hopen x]

end NLS.ZakharovShabat
