import NLS.ZakharovShabat.SourceDeletedPairOmittedSquare
import NLS.ZakharovShabat.SourceCanonicalRootGapIsolation

/-!
# Square of the canonical-root gap-side values

The two explicit boundary values of the full canonical root square to
the discriminant radicand even on the selected gap. This connects the
gap-side root to the real arcosh denominator without fixing a sign.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The upper gap-side value is a square root of the discriminant
radicand at every point of the selected gap that avoids the other
gap segments. -/
theorem sourceCanonicalRootGapUpperValue_sq_eq_discriminant_sq_sub_four
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p)
    (n : ℤ) (t : ℝ) (htl : -1 ≤ t) (htr : t ≤ 1)
    (hdom : sourceCanonicalRootGapPoint hp hp1 ψ n t ∈
      sourceStandardRootOmittedDomain hp hp1 ψ n) :
    (sourceCanonicalRootGapUpperValue hp hp1 ψ n t)^2 =
      (canonicalDiscriminant hp (periodOnePotential ψ)
        (sourceCanonicalRootGapPoint hp hp1 ψ n t))^2-4 := by
  let φ := periodOnePotential ψ
  let a := canonicalPeriodicLeft hp hp1 φ (periodOnePotential_mem ψ) n
  let b := canonicalPeriodicRight hp hp1 φ (periodOnePotential_mem ψ) n
  let δ := sourceStandardRootHalfGap hp hp1 ψ n
  let z := sourceCanonicalRootGapPoint hp hp1 ψ n t
  let P := sourceStandardRootOmittedProduct hp hp1 n ψ z
  let s := Real.sqrt (1-t^2)
  have hnonneg : 0 ≤ 1-t^2 := by
    have h₁ : 0 ≤ 1-t := by linarith
    have h₂ : 0 ≤ 1+t := by linarith
    nlinarith [mul_nonneg h₁ h₂]
  have hs : (s:ℂ)^2 = ((1-t^2:ℝ):ℂ) := by
    exact_mod_cast Real.sq_sqrt hnonneg
  have ha : a-z = -δ*(1+(t:ℂ)) := by
    dsimp [a,z,δ,φ,sourceCanonicalRootGapPoint,
      sourceStandardRootMidpoint,sourceStandardRootHalfGap,
      canonicalPeriodicMidpoint,canonicalPeriodicGap]
    ring
  have hb : b-z = δ*(1-(t:ℂ)) := by
    dsimp [b,z,δ,φ,sourceCanonicalRootGapPoint,
      sourceStandardRootMidpoint,sourceStandardRootHalfGap,
      canonicalPeriodicMidpoint,canonicalPeriodicGap]
    ring
  have hP : P^2 = canonicalDeletedPeriodicProduct hp hp1 φ
      (periodOnePotential_mem ψ) n z :=
    sourceStandardRootOmittedProduct_sq_eq_canonicalDeletedPeriodicProduct
      hp hp1 ψ n z hdom
  have hpair := canonicalDiscriminant_sq_sub_four_eq_pair_mul
    hp hp1 φ (periodOnePotential_mem ψ) n z
  change (canonicalDiscriminant hp φ z)^2-4 =
    (-4*(a-z)*(b-z))*
      canonicalDeletedPeriodicProduct hp hp1 φ
        (periodOnePotential_mem ψ) n z at hpair
  calc
    (sourceCanonicalRootGapUpperValue hp hp1 ψ n t)^2 =
        4*δ^2*(s:ℂ)^2*P^2 := by
      dsimp [sourceCanonicalRootGapUpperValue,P,s,δ,z]
      ring_nf
      simp
    _ = 4*δ^2*(1-(t:ℂ)^2)*P^2 := by rw [hs]; push_cast; ring
    _ = (-4*(a-z)*(b-z))*P^2 := by rw [ha,hb]; ring
    _ = (canonicalDiscriminant hp φ z)^2-4 := by rw [hP]; exact hpair.symm

/-- The lower gap-side value has the same square. -/
theorem sourceCanonicalRootGapLowerValue_sq_eq_discriminant_sq_sub_four
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p)
    (n : ℤ) (t : ℝ) (htl : -1 ≤ t) (htr : t ≤ 1)
    (hdom : sourceCanonicalRootGapPoint hp hp1 ψ n t ∈
      sourceStandardRootOmittedDomain hp hp1 ψ n) :
    (sourceCanonicalRootGapLowerValue hp hp1 ψ n t)^2 =
      (canonicalDiscriminant hp (periodOnePotential ψ)
        (sourceCanonicalRootGapPoint hp hp1 ψ n t))^2-4 := by
  rw [← neg_eq_iff_eq_neg.mpr
    (sourceCanonicalRootGapUpperValue_eq_neg_lower hp hp1 ψ n t)]
  simpa only [Even.neg_pow even_two] using
    sourceCanonicalRootGapUpperValue_sq_eq_discriminant_sq_sub_four
      hp hp1 ψ n t htl htr hdom

end NLS.ZakharovShabat
