import NLS.ZakharovShabat.SourceResonantAnalytic
import NLS.ZakharovShabat.ResonantRootGap

/-!
# The original determinant and its full-strip product supremum

The scalar function agrees with the actual source matrix in either basis
order. Its product supremum is taken over the whole closed, unbounded strip.
The source neighborhood retains the original component-sum norm.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The scalar determinant formed from the original analytic coefficients. -/
def sourceResonantDeterminantFunction (hp : p ≠ ⊤) (φ : CoeffPair p) (n : ℤ) (z : ℂ) : ℂ :=
  (z-(Real.pi : ℂ)*n-sourceResonantAFunction hp φ n z)^2 -
    sourceResonantBPlusFunction hp φ n z * sourceResonantBMinusFunction hp φ n z

/-- Unit weighting preserves the whole scalar function, including its zero orders. -/
theorem sourceResonantDeterminantFunction_unit (hp : p ≠ ⊤) (φ : CoeffPair p) (n : ℤ) :
    sourceResonantDeterminantFunction hp φ n =
      resonantDeterminantExtension hp SpectralWeight.one (unitWeightedPairEquiv φ) n := rfl

/-- Agreement with the actual reduced operator in the physical basis order. -/
theorem sourceResonantDeterminantFunction_eq_det (hp : p ≠ ⊤) (φ : CoeffPair p)
    (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp SpectralWeight.one (unitWeightedPairEquiv φ) n z hz‖ < 1) :
    sourceResonantDeterminantFunction hp φ n z = (sourceResonantMatrix hp φ n z hz h).det :=
  resonantDeterminantExtension_eq_det hp SpectralWeight.one (unitWeightedPairEquiv φ) n z hz h

/-- Agreement with the printed plus/minus basis order. -/
theorem sourceResonantDeterminantFunction_eq_printed_det (hp : p ≠ ⊤) (φ : CoeffPair p)
    (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp SpectralWeight.one (unitWeightedPairEquiv φ) n z hz‖ < 1) :
    sourceResonantDeterminantFunction hp φ n z = (sourcePrintedResonantMatrix hp φ n z hz h).det := by
  rw [sourcePrintedResonantMatrix_det]
  exact sourceResonantDeterminantFunction_eq_det hp φ n z hz h

/-- Its zeros detect noninvertibility of the actual original spectral pencil. -/
theorem sourceResonantDeterminantFunction_spectrum_iff (hp : p ≠ ⊤) (φ : CoeffPair p)
    (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp SpectralWeight.one (unitWeightedPairEquiv φ) n z hz‖ < 1) :
    z ∉ sourceResolventSet hp φ ↔ sourceResonantDeterminantFunction hp φ n z = 0 := by
  rw [sourceResonantDeterminantFunction_eq_det hp φ n z hz h]
  exact sourceLemma6_6 hp φ n z hz h

/-- Joint analyticity in the original potential and spectral parameter. -/
theorem analyticAt_sourceResonantDeterminantFunction (hp : p ≠ ⊤) (φ : CoeffPair p)
    (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp SpectralWeight.one (unitWeightedPairEquiv φ) n z hz‖ < 1) :
    AnalyticAt ℂ (fun s : CoeffPair p × ℂ => sourceResonantDeterminantFunction hp s.1 n s.2) (φ,z) := by
  exact (((analyticAt_snd.sub analyticAt_const).sub
    (analyticAt_sourceCorrectionEntryFunction hp φ n z hz h 0 0)).pow 2).sub
      ((analyticAt_sourceCorrectionEntryFunction hp φ n z hz h 1 0).mul
        (analyticAt_sourceCorrectionEntryFunction hp φ n z hz h 0 1))

@[simp] theorem sourceResonantDeterminantFunction_zero (hp : p ≠ ⊤) (n : ℤ) (z : ℂ) :
    sourceResonantDeterminantFunction (p := p) hp 0 n z = (z-(Real.pi : ℂ)*n)^2 := by
  rw [sourceResonantDeterminantFunction_unit, map_zero, resonantDeterminantExtension_zero]

/-- The supremum of the product of the original coefficients on the full strip. -/
def sourceResonantBProductSup (hp : p ≠ ⊤) (φ : CoeffPair p) (n : ℤ) : ℝ :=
  sSup ((fun z : ℂ => ‖sourceResonantBPlusFunction hp φ n z *
    sourceResonantBMinusFunction hp φ n z‖) '' resonantStrip n)

theorem sourceResonantBProductSup_unit (hp : p ≠ ⊤) (φ : CoeffPair p) (n : ℤ) :
    sourceResonantBProductSup hp φ n =
      resonantBProductSup hp SpectralWeight.one (unitWeightedPairEquiv φ) n := by
  simp only [sourceResonantBProductSup, resonantBProductSup, weightedStripSup,
    SpectralWeight.one_apply, one_mul]
  rfl

/-- Numerical bounds and a common correction domain on an entire source strip. -/
structure SourceResonantStripControl (hp : p ≠ ⊤) (φ : CoeffPair p) (n : ℤ) : Prop where
  small : ∀ z : ℂ, ∀ hz : z ∈ resonantStrip n,
    ‖weightedPotentialSquareInShift hp SpectralWeight.one (unitWeightedPairEquiv φ) n z hz‖ ≤ 1/2
  diagonal : ∀ z ∈ resonantStrip n, ‖sourceResonantAFunction hp φ n z‖ ≤ Real.pi/32
  negative : ∀ z ∈ resonantStrip n, ‖sourceResonantBMinusFunction hp φ n z‖ ≤ Real.pi/16
  positive : ∀ z ∈ resonantStrip n, ‖sourceResonantBPlusFunction hp φ n z‖ ≤ Real.pi/16

/-- A finite, nonnegative product supremum dominates each actual product value. -/
theorem SourceResonantStripControl.product_bounds {hp : p ≠ ⊤} {φ : CoeffPair p} {n : ℤ}
    (h : SourceResonantStripControl hp φ n) :
    BddAbove ((fun z : ℂ => ‖sourceResonantBPlusFunction hp φ n z *
      sourceResonantBMinusFunction hp φ n z‖) '' resonantStrip n) ∧
    0 ≤ sourceResonantBProductSup hp φ n ∧ sourceResonantBProductSup hp φ n ≤ (Real.pi/16)^2 ∧
    ∀ z ∈ resonantStrip n, ‖sourceResonantBPlusFunction hp φ n z *
      sourceResonantBMinusFunction hp φ n z‖ ≤ sourceResonantBProductSup hp φ n := by
  refine ⟨⟨(Real.pi/16)^2, ?_⟩, ?_⟩
  · rintro _ ⟨z,hz,rfl⟩
    change ‖sourceResonantBPlusFunction hp φ n z * sourceResonantBMinusFunction hp φ n z‖ ≤ _
    rw [norm_mul, pow_two]
    exact mul_le_mul (h.positive z hz) (h.negative z hz) (norm_nonneg _) (by positivity)
  · rw [sourceResonantBProductSup_unit]
    exact resonantBProductSup_bounds hp SpectralWeight.one (unitWeightedPairEquiv φ) n
      (fun z hz => ⟨h.negative z hz,h.positive z hz⟩)

/-- The source's Cauchy derivative bound on the refined disk. -/
theorem SourceResonantStripControl.deriv_bound {hp : p ≠ ⊤} {φ : CoeffPair p} {n : ℤ}
    (h : SourceResonantStripControl hp φ n) :
    ∀ z ∈ refinedResonantDisk n, ‖deriv (sourceResonantAFunction hp φ n) z‖ ≤ 1/8 := by
  apply norm_deriv_le_on_refined_disk n _ _ h.diagonal
  intro z hz
  exact (analyticAt_sourceCorrectionEntryFunction hp φ n z hz
    ((h.small z hz).trans_lt (by norm_num)) 0 0).comp (analyticAt_const.prod analyticAt_id)

/-- One original open convex neighborhood controls all distant full strips. -/
theorem exists_uniform_sourceResonantDeterminant_control (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) :
    ∃ N : ℕ, 2 ≤ N ∧ ∃ U : Set (CoeffPair p), IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ n : ℤ, N ≤ n.natAbs →
        AnalyticOnNhd ℂ (fun s : CoeffPair p × ℂ => sourceResonantDeterminantFunction hp s.1 n s.2)
          (U ×ˢ resonantStrip n) ∧ ∀ ψ ∈ U, SourceResonantStripControl hp ψ n := by
  have hw : ∃ N : ℕ, 2 ≤ N ∧ ∃ V : Set (WeightedCoeffPair SpectralWeight.one.toWeight p),
      IsOpen V ∧ Convex ℝ V ∧ unitWeightedPairEquiv φ ∈ V ∧ 0 ∈ V ∧
      ∀ ψ ∈ V, ∀ n : ℤ, N ≤ n.natAbs → ∀ z : ℂ, ∀ hz : z ∈ resonantStrip n,
        ‖weightedPotentialSquareInShift hp SpectralWeight.one ψ n z hz‖ ≤ 1/2 ∧
        ‖weightedResonantAExtension hp SpectralWeight.one ψ n z‖ ≤ Real.pi/32 ∧
        ‖weightedResonantBMinusExtension hp SpectralWeight.one ψ n z‖ ≤ Real.pi/16 ∧
        ‖weightedResonantBPlusExtension hp SpectralWeight.one ψ n z‖ ≤ Real.pi/16 := by
    obtain ⟨N,hN,V,ho,hc,hφ,h0,hb⟩ := exists_uniform_resonantDeterminant_control hp hp1
      SpectralWeight.one (unitWeightedPairEquiv φ)
    exact ⟨N,hN,V,ho,hc,hφ,h0,fun ψ hψ n hn => (hb n hn).2 ψ hψ⟩
  obtain ⟨N,hN,U,ho,hc,hφ,h0,hb⟩ := sourceUnitWeightedUniformPullback unitWeightedPairEquiv φ _ hw
  refine ⟨N,hN,U,ho,hc,hφ,h0,?_⟩
  intro n hn
  constructor
  · intro s hs
    exact analyticAt_sourceResonantDeterminantFunction hp s.1 n s.2 hs.2
      ((hb s.1 hs.1 n hn s.2 hs.2).1.trans_lt (by norm_num))
  · intro ψ hψ
    exact ⟨fun z hz => (hb ψ hψ n hn z hz).1,
      fun z hz => (hb ψ hψ n hn z hz).2.1,
      fun z hz => (hb ψ hψ n hn z hz).2.2.1,
      fun z hz => (hb ψ hψ n hn z hz).2.2.2⟩

end NLS.ZakharovShabat
