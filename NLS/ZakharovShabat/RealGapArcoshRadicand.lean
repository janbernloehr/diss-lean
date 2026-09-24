import NLS.ZakharovShabat.RealGapArcoshIntegral
import NLS.ZakharovShabat.DiscriminantPairFactorization
import NLS.ZakharovShabat.RealDiscriminantValues

/-!
# The real-gap arcosh radicand

The radicand in the arcosh derivative factors into the two endpoint
distances and the real part of the deleted periodic-pair product.
This identifies the endpoint square-root weight in Lemma 10.11(ii).
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The signed half-discriminant radicand has the exact endpoint-pair
factorization on the real axis. -/
theorem realGapHalfDiscriminant_sq_sub_one_eq_deletedPair_re
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (heven : φ ∈ pairParitySubspace 0)
    (hreal : IsRealType φ) (n : ℤ) (x : ℝ) :
    (realGapHalfDiscriminant hp φ n x)^2 - 1 =
      (x-(canonicalPeriodicLeft hp hp1 φ heven n).re) *
        ((canonicalPeriodicRight hp hp1 φ heven n).re-x) *
          (canonicalDeletedPeriodicProduct hp hp1 φ heven n x).re := by
  let l := canonicalPeriodicLeft hp hp1 φ heven n
  let r := canonicalPeriodicRight hp hp1 φ heven n
  let D := canonicalDiscriminant hp φ (x : ℂ)
  let G := canonicalDeletedPeriodicProduct hp hp1 φ heven n (x : ℂ)
  have hLim : l.im = 0 :=
    (canonicalPeriodicEndpoints_im_eq_zero_of_realType hp hp1 φ heven hreal n).1
  have hRim : r.im = 0 :=
    (canonicalPeriodicEndpoints_im_eq_zero_of_realType hp hp1 φ heven hreal n).2
  have hDim : D.im = 0 := canonicalDiscriminant_im_eq_zero_of_realType
    hp hp1 φ heven hreal x
  have hpair := canonicalDiscriminant_sq_sub_four_eq_pair_mul hp hp1 φ heven n (x:ℂ)
  have hre := congrArg Complex.re hpair
  have hrealpair : D.re^2-4 = -4*(l.re-x)*(r.re-x)*G.re := by
    change (D^2-4).re = (-4*(l-(x:ℂ))*(r-(x:ℂ))*G).re at hre
    have hDsq : (D^2).re = D.re^2 := by
      rw [pow_two, Complex.mul_re, hDim]
      ring
    have hRHS : (-4*(l-(x:ℂ))*(r-(x:ℂ))*G).re =
        -4*(l.re-x)*(r.re-x)*G.re := by
      simp [Complex.mul_re,Complex.sub_re,hLim,hRim]
    rw [Complex.sub_re,hDsq,hRHS] at hre
    simpa using hre
  have hg : (realGapHalfDiscriminant hp φ n x)^2 = D.re^2/4 := by
    dsimp [realGapHalfDiscriminant,D]
    split_ifs <;> ring
  dsimp [l,r,G] at hrealpair
  rw [hg]
  nlinarith [hrealpair]

/-- The deleted periodic-pair product has positive real value in the
interior of every open real gap. -/
theorem canonicalDeletedPeriodicProduct_re_pos_on_realGap_interior
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (heven : φ ∈ pairParitySubspace 0)
    (hreal : IsRealType φ) (n : ℤ) (x : ℝ)
    (hx : x ∈ Ioo (canonicalPeriodicLeft hp hp1 φ heven n).re
      (canonicalPeriodicRight hp hp1 φ heven n).re) :
    0 < (canonicalDeletedPeriodicProduct hp hp1 φ heven n x).re := by
  let a := (canonicalPeriodicLeft hp hp1 φ heven n).re
  let b := (canonicalPeriodicRight hp hp1 φ heven n).re
  let g := realGapHalfDiscriminant hp φ n x
  let G := (canonicalDeletedPeriodicProduct hp hp1 φ heven n x).re
  have hgt : 1 < g := by
    have h := signed_discriminant_gt_two_on_canonicalGap_interior
      hp hp1 φ heven hreal n x hx
    rw [neg_one_zpow_eq_ite] at h
    by_cases hn : n % 2 = 0
    · simp only [Int.even_iff,hn,if_true,one_mul] at h
      simp only [g,realGapHalfDiscriminant,if_pos hn]
      linarith
    · simp only [Int.even_iff,hn,if_false,neg_one_mul] at h
      simp only [g,realGapHalfDiscriminant,if_neg hn]
      linarith
  have hrad : 0 < g^2-1 := by nlinarith
  have hfactor : g^2-1 = (x-a)*(b-x)*G :=
    realGapHalfDiscriminant_sq_sub_one_eq_deletedPair_re hp hp1 φ heven hreal n x
  have hweight : 0 ≤ (x-a)*(b-x) :=
    (mul_pos (by dsimp [a]; linarith [hx.1])
      (by dsimp [b]; linarith [hx.2])).le
  by_contra hG
  have hnonpos : G ≤ 0 := le_of_not_gt hG
  have hmul : (x-a)*(b-x)*G ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hweight hnonpos
  linarith

end NLS.ZakharovShabat
