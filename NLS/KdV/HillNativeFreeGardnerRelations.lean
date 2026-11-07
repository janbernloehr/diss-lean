import NLS.KdV.HillNativeGardnerCoordinates
import NLS.Poisson.GardnerModePairing

/-! The ACTUAL coordinate Gardner matrix at the free potential has the
article's exact sign and normalization. Relations away from zero remain
a separate theorem; no global canonicality is inferred here. -/
noncomputable section
open Complex
namespace NLS.KdV

theorem hillHminusNativeGardnerBracket_zero (k l : ℤ) (hk : k ≠ 0) :
    hillHminusNativeGardnerBracket k l 0=
      if l= -k then (2*Real.pi:ℂ)*I*k*WeightedCoeff.halfFourierSymbol k*WeightedCoeff.halfFourierSymbol l else 0 :=
  NLS.Poisson.gardnerBivector_of_nonzero_modes _ _ k l hk _ _
    (hillHminusNativeCoordinateGradient_zero_nonzero_mode k)
    (hillHminusNativeCoordinateGradient_zero_nonzero_mode l)

theorem halfFourierSymbol_Gardner_positive_normalization (n : ℕ+) :
    (2*Real.pi:ℂ)*I*(n:ℤ)*WeightedCoeff.halfFourierSymbol (n:ℤ)*
      WeightedCoeff.halfFourierSymbol (-(n:ℤ))=I := by
  have hn : (0:ℝ) < n := by exact_mod_cast n.pos
  have hs : (Real.sqrt (2*Real.pi*(n:ℕ)):ℂ)^2=(2*Real.pi:ℂ)*(n:ℕ) := by
    rw [← Complex.ofReal_pow,Real.sq_sqrt (by positivity)]
    push_cast
    rfl
  have hs0 : (Real.sqrt (2*Real.pi*(n:ℕ)):ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr (by positivity : (0:ℝ) < 2*Real.pi*(n:ℕ)))
  rw [WeightedCoeff.halfFourierSymbol_neg,WeightedCoeff.halfFourierSymbol_positive]
  field_simp [hs0]
  rw [hs]
  push_cast
  ring

theorem hillHminusNativeGardnerBracket_positive_negative_zero (n m : ℕ+) :
    hillHminusNativeGardnerBracket (n:ℤ) (-(m:ℤ)) 0=if n=m then I else 0 := by
  have hn : (n:ℤ) ≠ 0 := by exact_mod_cast n.ne_zero
  rw [hillHminusNativeGardnerBracket_zero _ _ hn]
  by_cases he : n=m
  · subst m
    rw [if_pos rfl,if_pos rfl]
    exact halfFourierSymbol_Gardner_positive_normalization n
  · have hm : -(m:ℤ) ≠ -(n:ℤ) := by
      intro h
      apply he
      apply PNat.coe_injective
      exact_mod_cast (neg_injective h).symm
    rw [if_neg hm,if_neg he]

theorem hillHminusNativeGardnerBracket_positive_positive_zero (n m : ℕ+) :
    hillHminusNativeGardnerBracket (n:ℤ) (m:ℤ) 0=0 := by
  have hn : (n:ℤ) ≠ 0 := by exact_mod_cast n.ne_zero
  have hp : (0:ℤ) < n := by exact_mod_cast n.pos
  have hq : (0:ℤ) < m := by exact_mod_cast m.pos
  rw [hillHminusNativeGardnerBracket_zero _ _ hn,if_neg (by omega : (m:ℤ) ≠ -(n:ℤ))]

theorem hillHminusNativeGardnerBracket_negative_negative_zero (n m : ℕ+) :
    hillHminusNativeGardnerBracket (-(n:ℤ)) (-(m:ℤ)) 0=0 := by
  have hn0 : (n:ℤ) ≠ 0 := by exact_mod_cast n.ne_zero
  have hn : -(n:ℤ) ≠ 0 := neg_ne_zero.mpr hn0
  have hp : (0:ℤ) < n := by exact_mod_cast n.pos
  have hq : (0:ℤ) < m := by exact_mod_cast m.pos
  rw [hillHminusNativeGardnerBracket_zero _ _ hn,if_neg (by omega : -(m:ℤ) ≠ -(-(n:ℤ)))]

end NLS.KdV
