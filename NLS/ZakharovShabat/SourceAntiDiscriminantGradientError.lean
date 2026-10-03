import NLS.ZakharovShabat.ContinuousSourceAntiDiscriminantGradient
import NLS.ZakharovShabat.ClassicalCharacteristicGradientFourier
import NLS.SequenceSpaces.SourceCotangentNormBound
import NLS.ZakharovShabat.SourceFreePotentialCotangents

/-! # The actual source anti-discriminant error

The source differential minus its zero-potential reference has exactly the
physical Fourier remainder from G.6. Hölder duality bounds its operator norm.
No reality, root simplicity, or choice of spectral parameter is required.
-/

noncomputable section
open Set Complex MeasureTheory NLS.LinearVolterra NLS.Fourier
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The physical reference is the actual zero-potential gradient on the interval. -/
theorem classicalAntiDiscriminantGradientFourierCoefficients_eq_sub_zero
    {q : ℝ≥0∞} (hq : 1 < q) (Φ : Curve (ℂ × ℂ)) (z w : ℂ)
    (P : (ℂ × ℂ) →L[ℝ] ℂ) (k : ℤ) :
    classicalAntiDiscriminantGradientFourierCoefficients hq Φ z w P k =
      intervalFourierCoefficient 1 (fun t => P (classicalAntiDiscriminantGradient Φ z t)) k-
      intervalFourierCoefficient 1 (fun t => P (classicalAntiDiscriminantGradient 0 w t)) k := by
  rw [classicalAntiDiscriminantGradientFourierCoefficients_apply,
    ← intervalFourierCoefficient_sub 1
      (fun t => P (classicalAntiDiscriminantGradient Φ z t))
      (fun t => P (classicalAntiDiscriminantGradient 0 w t))
      (P.continuous.comp (continuous_classicalAntiDiscriminantGradient Φ z))
      (P.continuous.comp (continuous_classicalAntiDiscriminantGradient 0 w))]
  apply intervalFourierCoefficient_congr
  intro t ht
  have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa using ht
  change P (classicalAntiDiscriminantGradientRemainder Φ z w t) = _
  rw [classicalAntiDiscriminantGradientRemainder,map_sub]
  congr 1
  congr 1
  rw [classicalFreeAntiDiscriminantGradient,← classicalEndpointGradient_free w _ _ ⟨t,ht'⟩,
    ← classicalEndpointGradient_free w _ _ ⟨t,ht'⟩]
  rfl

/-- Both components of the actual source error equal the physical remainder
coefficients, at the reversed source frequency. -/
theorem sourceAntiDiscriminantCotangent_error_fourier
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    {q : ℝ≥0∞} (hq : 1 < q) (φ : CoeffPair 2) (Φ : Curve (ℂ × ℂ))
    (hΦ : physicalBase (periodOnePotential φ) =ᵐ[volume.restrict (Ioc 0 1)] extend Φ)
    (z w : ℂ) (k : ℤ) :
    let L := sourceAntiDiscriminantCotangent hp hp1 z (CoeffPair.exponentInclusion h2p φ)-
      sourceAntiDiscriminantCotangent hp hp1 w 0
    L (CoeffPair.inlCLM (lp.single p k 1)) =
      classicalAntiDiscriminantGradientFourierCoefficients hq Φ z w (ContinuousLinearMap.fst ℝ ℂ ℂ) (-k) ∧
    L (CoeffPair.inrCLM (lp.single p k 1)) =
      classicalAntiDiscriminantGradientFourierCoefficients hq Φ z w (ContinuousLinearMap.snd ℝ ℂ ℂ) (-k) := by
  have hzero : physicalBase (periodOnePotential (0 : CoeffPair 2))
      =ᵐ[volume.restrict (Ioc 0 1)] extend (0 : Curve (ℂ × ℂ)) := by
    have h := (finiteSource_physical_compatibility (0,0)).1
    simpa only [show CoeffPair.ofFinsupp (p := 2) (0,0) = 0 from map_zero _,
      show finiteSourceCurve (0,0) = 0 from finiteSourceCurveLinear.map_zero] using h
  have hcoeff (f : ℝ → ℂ) (j : ℤ) : intervalFourierCoefficient 1 f j = unitFourierCoefficient f j := by
    rw [intervalFourierCoefficient_eq_fourierCoeffOn (by norm_num),unitFourierCoefficient_eq_fourierCoeffOn]
  dsimp only
  constructor
  · have h0 := sourceAntiDiscriminantCotangent_continuous_single_fst hp hp1 h2p 0 0 hzero w k
    simp only [map_zero] at h0
    rw [sub_apply,sourceAntiDiscriminantCotangent_continuous_single_fst hp hp1 h2p φ Φ hΦ,h0,
      classicalAntiDiscriminantGradientFourierCoefficients_eq_sub_zero,hcoeff,hcoeff]
    rfl
  · have h0 := sourceAntiDiscriminantCotangent_continuous_single_snd hp hp1 h2p 0 0 hzero w k
    simp only [map_zero] at h0
    rw [sub_apply,sourceAntiDiscriminantCotangent_continuous_single_snd hp hp1 h2p φ Φ hΦ,h0,
      classicalAntiDiscriminantGradientFourierCoefficients_eq_sub_zero,hcoeff,hcoeff]
    rfl

/-- Conjugate Fourier norms control the genuine source operator error. -/
theorem norm_sourceAntiDiscriminantCotangent_error_le
    {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [q.HolderConjugate p]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p) (hq : 1 < q)
    (φ : CoeffPair 2) (Φ : Curve (ℂ × ℂ))
    (hΦ : physicalBase (periodOnePotential φ) =ᵐ[volume.restrict (Ioc 0 1)] extend Φ) (z w : ℂ) :
    ‖sourceAntiDiscriminantCotangent hp hp1 z (CoeffPair.exponentInclusion h2p φ)-
      sourceAntiDiscriminantCotangent hp hp1 w 0‖ ≤
      ‖classicalAntiDiscriminantGradientFourierCoefficients hq Φ z w (ContinuousLinearMap.fst ℝ ℂ ℂ)‖+
      ‖classicalAntiDiscriminantGradientFourierCoefficients hq Φ z w (ContinuousLinearMap.snd ℝ ℂ ℂ)‖ := by
  simpa only [LinearIsometryEquiv.norm_map] using CoeffPair.norm_cotangent_le_of_single hp _
    (Coeff.reflection (classicalAntiDiscriminantGradientFourierCoefficients hq Φ z w (ContinuousLinearMap.fst ℝ ℂ ℂ)))
    (Coeff.reflection (classicalAntiDiscriminantGradientFourierCoefficients hq Φ z w (ContinuousLinearMap.snd ℝ ℂ ℂ)))
    (fun k => (sourceAntiDiscriminantCotangent_error_fourier hp hp1 h2p hq φ Φ hΦ z w k).1)
    (fun k => (sourceAntiDiscriminantCotangent_error_fourier hp hp1 h2p hq φ Φ hΦ z w k).2)

/-- The exact reference functional, with opposite component signs, is valid
at every finite source exponent strictly above one. -/
theorem sourceAntiDiscriminantCotangent_zero_of_exponent
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (h : CoeffPair p) :
    sourceAntiDiscriminantCotangent hp hp1 ((Real.pi : ℂ)*n) 0 h =
      I*cos ((Real.pi : ℂ)*n)*(h.fst (-n)-h.snd n) := by
  have hfinite (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) :
      sourceAntiDiscriminantCotangent hp hp1 ((Real.pi : ℂ)*n) 0 (CoeffPair.ofFinsupp a) =
        I*cos ((Real.pi : ℂ)*n)*(a.1 (-n)-a.2 n) := by
    rcases le_total p 2 with hp2 | h2p
    · have he := congrArg (fun L : CoeffPair p →L[ℂ] ℂ => L (CoeffPair.ofFinsupp a))
        (sourceAntiDiscriminantCotangent_exponent hp (by simp) hp1 (by norm_num) hp2 0 ((Real.pi : ℂ)*n))
      simp only [ContinuousLinearMap.comp_apply,map_zero,CoeffPair.exponentInclusion_ofFinsupp] at he
      rw [he]
      exact sourceAntiDiscriminantCotangent_zero_finite n a
    · have he := congrArg (fun L : CoeffPair 2 →L[ℂ] ℂ => L (CoeffPair.ofFinsupp a))
        (sourceAntiDiscriminantCotangent_exponent (by simp) hp (by norm_num) hp1 h2p 0 ((Real.pi : ℂ)*n))
      simp only [ContinuousLinearMap.comp_apply,map_zero,CoeffPair.exponentInclusion_ofFinsupp] at he
      rw [← he]
      exact sourceAntiDiscriminantCotangent_zero_finite n a
  have heq := CoeffPair.eq_of_continuous_of_finsupp hp
    (sourceAntiDiscriminantCotangent hp hp1 ((Real.pi : ℂ)*n) 0)
    (fun h : CoeffPair p => I*cos ((Real.pi : ℂ)*n)*(h.fst (-n)-h.snd n))
    (ContinuousLinearMap.continuous _) (continuous_const.mul
      (((lp.evalCLM ℂ (fun _ : ℤ => ℂ) p (-n)).continuous.comp (CoeffPair.toMax p).continuous.fst).sub
        ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n).continuous.comp (CoeffPair.toMax p).continuous.snd))) hfinite
  exact congrFun heq h

end NLS.ZakharovShabat
