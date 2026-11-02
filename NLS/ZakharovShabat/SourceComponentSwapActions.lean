import NLS.ZakharovShabat.SourceComponentSwapRoots
import NLS.ZakharovShabat.SourceRealHigherAction
import NLS.ZakharovShabat.SourceComplexAction

/-! # Actual action reflection under component exchange

The positive real gap profile reflects by theta -> pi-theta. This gives
all real higher-action parities and the exact original contour-defined
ordinary action identity, including zero gaps. No Birkhoff angle symmetry
or frequency identity is assumed.
-/
noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Reflection of the actual real affine gap parameter. -/
theorem realGapAffinePoint_componentSwap (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (n : ℤ) (t : ℝ) :
    realGapAffinePoint hp hp1 (sourceComponentSwap φ) n t =
      -realGapAffinePoint hp hp1 φ (-n) (-t) := by
  obtain ⟨hl,hr⟩ := sourceCanonicalPeriodicEndpoints_componentSwap hp hp1 φ n
  unfold realGapAffinePoint
  rw [hl,hr]
  simp only [neg_re]
  ring

/-- Signed gap half-discriminants have unchanged parity under reflection. -/
theorem realGapHalfDiscriminant_componentSwap (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (n : ℤ) (x : ℝ) :
    realGapHalfDiscriminant hp (periodOnePotential (sourceComponentSwap φ)) n (-x) =
      realGapHalfDiscriminant hp (periodOnePotential φ) (-n) x := by
  have hmod : (-n)%2 = n%2 := by omega
  simp only [realGapHalfDiscriminant,hmod,Complex.ofReal_neg,
    sourceDiscriminant_componentSwap hp hp1 φ (x:ℂ)]

/-- The exact real arcosh gap profile reflects without an extra sign. -/
theorem sourceRealGapArcoshProfile_componentSwap (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (n : ℤ) (x : ℝ) :
    sourceRealGapArcoshProfile hp (sourceComponentSwap φ) n (-x) =
      sourceRealGapArcoshProfile hp φ (-n) x := by
  unfold sourceRealGapArcoshProfile
  rw [realGapHalfDiscriminant_componentSwap hp hp1 φ n x]

/-- Reflection of the actual positive cosine profile, including endpoints. -/
theorem sourceRealGapCosineProfile_componentSwap (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (n : ℤ) (θ : ℝ) :
    sourceRealGapCosineProfile hp hp1 (sourceComponentSwap φ) n θ =
      sourceRealGapCosineProfile hp hp1 φ (-n) (Real.pi-θ) := by
  unfold sourceRealGapCosineProfile
  rw [realGapAffinePoint_componentSwap,sourceRealGapArcoshProfile_componentSwap hp hp1 φ n,
    Real.cos_pi_sub]

/-- Every original real higher action has its exact spectral-power parity.
Level zero is the ordinary action; collapsed gaps are included. -/
theorem sourceRealHigherAction_componentSwap (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (n : ℤ) (k : ℕ) :
    sourceRealHigherAction hp hp1 (realSourceComponentSwap φ) n k =
      (-1:ℝ)^k*sourceRealHigherAction hp hp1 φ (-n) k := by
  let f : ℝ → ℝ := fun θ => (realGapAffinePoint hp hp1 φ.val (-n) (Real.cos θ))^k*
    (Real.sin θ*sourceRealGapCosineProfile hp hp1 φ.val (-n) θ)
  have he (θ : ℝ) :
      (realGapAffinePoint hp hp1 (sourceComponentSwap φ.val) n (Real.cos θ))^k*
        (Real.sin θ*sourceRealGapCosineProfile hp hp1 (sourceComponentSwap φ.val) n θ) =
      (-1:ℝ)^k*f (Real.pi-θ) := by
    dsimp only [f]
    rw [realGapAffinePoint_componentSwap,sourceRealGapCosineProfile_componentSwap,
      Real.cos_pi_sub,Real.sin_pi_sub]
    rw [neg_pow]
    ring
  unfold sourceRealHigherAction
  change (canonicalPeriodicGap hp hp1 (periodOnePotential (sourceComponentSwap φ.val))
      (periodOnePotential_mem _) n).re/Real.pi * (∫ θ in (0:ℝ)..Real.pi,
      (realGapAffinePoint hp hp1 (sourceComponentSwap φ.val) n (Real.cos θ))^k*
        (Real.sin θ*sourceRealGapCosineProfile hp hp1 (sourceComponentSwap φ.val) n θ)) =
      (-1:ℝ)^k*((canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem _) (-n)).re/Real.pi*
        ∫ θ in (0:ℝ)..Real.pi, f θ)
  rw [sourcePeriodicGap_componentSwap hp hp1 φ.val n]
  have hefun := funext he
  rw [hefun]
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_comp_sub_left f Real.pi,sub_self,sub_zero]
  ring

/-- The contour-defined original ordinary actions reflect their signed
index exactly. This is an equality of the actual complex action values. -/
theorem sourceRealAction_componentSwap (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (n : ℤ) :
    sourceRealAction hp hp1 (sourceComponentSwap φ.val) (sourceComponentSwap_realType φ.val φ.property) n =
      sourceRealAction hp hp1 φ.val φ.property (-n) := by
  apply Complex.ext
  · have he := sourceRealHigherAction_componentSwap hp hp1 φ n 0
    simpa only [sourceRealHigherAction_zero,realSourceComponentSwap_val,pow_zero,one_mul] using he
  · exact (sourceRealAction_nonneg_and_eq_zero_iff_gap_zero hp hp1 _
      (sourceComponentSwap_realType φ.val φ.property) n).2.1.trans
      (sourceRealAction_nonneg_and_eq_zero_iff_gap_zero hp hp1 _ φ.property (-n)).2.1.symm

/-- The analytic complex action on the real form has the same original
signed-index reflection, independently of contour-radius choices. -/
theorem sourceComplexAction_componentSwap (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (n : ℤ) :
    sourceComplexAction hp hp1 n (sourceComponentSwap φ.val) = sourceComplexAction hp hp1 (-n) φ.val := by
  rw [sourceComplexAction_eq_sourceRealAction hp hp1 n _ (sourceComponentSwap_realType φ.val φ.property),
    sourceComplexAction_eq_sourceRealAction hp hp1 (-n) _ φ.property]
  exact sourceRealAction_componentSwap hp hp1 φ n

/-- All original mKdV diagonal actions are even in the actual signed index. -/
theorem sourceComplexAction_even_of_diagonal (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (hφ : φ.val.fst = φ.val.snd) (n : ℤ) :
    sourceComplexAction hp hp1 (-n) φ.val = sourceComplexAction hp hp1 n φ.val := by
  have he := sourceComplexAction_componentSwap hp hp1 φ n
  rw [(sourceComponentSwap_eq_self_iff φ.val).mpr hφ] at he
  exact he.symm

end NLS.ZakharovShabat
