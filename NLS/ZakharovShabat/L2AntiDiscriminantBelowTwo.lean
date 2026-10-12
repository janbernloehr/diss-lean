import NLS.ZakharovShabat.L2GradientRestrictionFourier
import NLS.ZakharovShabat.L2GradientFourierRealization

/-! # Actual anti-discriminant gradients below the Hilbert exponent

The entire anti-discriminant cotangent restricts to every original source
direction. Its signed conjugate vector realizes i times the physical
Fourier gradient, including the actual zero-potential reference.
-/
noncomputable section
open Set Complex MeasureTheory
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The factor i converts the root-gradient Fourier convention to G.6's convention. -/
theorem L2RootGradientFourierRealizes.mul_I {q : ℝ≥0∞} [Fact (1 ≤ q)]
    {g : ℝ → ℂ × ℂ} {a : CoeffPair q} (ha : L2RootGradientFourierRealizes g a) :
    L2GradientFourierRealizes g (I • a) := by
  intro k
  constructor
  · change I*a.fst k = _
    rw [(ha k).1]
  · change I*a.snd k = _
    rw [(ha k).2]

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- No reality or root-simplicity assumption is needed for the physical anti-trace integral. -/
theorem sourceAntiDiscriminantCotangent_below_two_integral
    (hp : p ≠ ⊤) (hp1 : 1 < p) (hp2 : p ≤ 2) (φ h : CoeffPair p) (z : ℂ) :
    sourceAntiDiscriminantCotangent hp hp1 z φ h =
      ∫ s in (0 : ℝ)..1,
        (l2AntiDiscriminantGradient (sourcePhysicalL2 (CoeffPair.exponentInclusion hp2 φ)) z s).1*
          (physicalBase (periodOnePotential (CoeffPair.exponentInclusion hp2 h)) s).1+
        (l2AntiDiscriminantGradient (sourcePhysicalL2 (CoeffPair.exponentInclusion hp2 φ)) z s).2*
          (physicalBase (periodOnePotential (CoeffPair.exponentInclusion hp2 h)) s).2 := by
  rw [sourceAntiDiscriminantCotangent_exponent hp (by simp) hp1 (by norm_num) hp2,
    ContinuousLinearMap.comp_apply]
  exact sourceAntiDiscriminantCotangent_eq_physical_gradient_integral _ _ z

variable {q : ℝ≥0∞} [Fact (1 ≤ q)] [q.HolderConjugate p]

/-- The actual anti-discriminant error in G.6's signed coefficient convention. -/
def sourceG6AntiDiscriminantCotangentCoefficients
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) (z w : ℂ) : CoeffPair q :=
  I • sourceG7SignedCoordinates q (CoeffPair.conjugateGradient hp
    ((ENNReal.HolderConjugate.ne_top_iff_ne_one q p).mpr hp1.ne')
    (sourceAntiDiscriminantCotangent hp hp1 z φ-sourceAntiDiscriminantCotangent hp hp1 w 0))

/-- The phase and signed index reversal preserve the exact conjugate pair norm. -/
theorem norm_sourceG6AntiDiscriminantCotangentCoefficients
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) (z w : ℂ) :
    ‖sourceG6AntiDiscriminantCotangentCoefficients (q := q) hp hp1 φ z w‖ =
      ‖CoeffPair.conjugateGradient hp ((ENNReal.HolderConjugate.ne_top_iff_ne_one q p).mpr hp1.ne')
        (sourceAntiDiscriminantCotangent hp hp1 z φ-sourceAntiDiscriminantCotangent hp hp1 w 0)‖ := by
  simp only [sourceG6AntiDiscriminantCotangentCoefficients,norm_smul,norm_I,one_mul,
    norm_sourceG7SignedCoordinates]

/-- Every complex source below two has the actual physical Fourier remainder,
at arbitrary spectral and reference parameters. -/
theorem sourceG6AntiDiscriminantCotangentCoefficients_realizes_below_two
    (hp : p ≠ ⊤) (hp1 : 1 < p) (hp2 : p ≤ 2) (φ : CoeffPair p) (z w : ℂ) :
    L2GradientFourierRealizes
      (l2AntiDiscriminantGradientRemainder (sourcePhysicalL2 (CoeffPair.exponentInclusion hp2 φ)) z w)
      (sourceG6AntiDiscriminantCotangentCoefficients (q := q) hp hp1 φ z w) := by
  have hq : q ≠ ⊤ := (ENNReal.HolderConjugate.ne_top_iff_ne_one q p).mpr hp1.ne'
  have hactual := signedGradient_realizes_below_two_of_integral (q := q) hp hq hp2 _ _
    (fun h => sourceAntiDiscriminantCotangent_below_two_integral hp hp1 hp2 φ h z)
  have hfree := signedGradient_realizes_below_two_of_integral (q := q) hp hq hp2 _ _
    (fun h => sourceAntiDiscriminantCotangent_below_two_integral hp hp1 hp2 0 h w)
  simp only [map_zero] at hfree
  have hs := (hactual.sub hfree (continuous_l2AntiDiscriminantGradient _ _)
    (continuous_l2AntiDiscriminantGradient _ _)).mul_I
  change L2GradientFourierRealizes _ (I • sourceG7SignedCoordinates q
    (CoeffPair.conjugateGradientCLM hp hq (_-_)))
  rw [map_sub,map_sub]
  exact hs

end NLS.ZakharovShabat
