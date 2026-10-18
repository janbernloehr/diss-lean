import NLS.ZakharovShabat.PhysicalL2BilinearPairing
import NLS.Poisson.SourceBivector

/-! # Physical L2 gradients and the literal Poisson integral

Every continuous complex cotangent has a unique physical L2 gradient for
unconjugated integral duality. Its Fourier coefficients reverse frequency.
The literal cross-gradient integral equals the established source bivector,
including its factor minus i.
-/

noncomputable section
open Set MeasureTheory Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.ZakharovShabat
open NLS.Poisson NLS.Fourier

/-- The physical L2 gradient of a continuous complex cotangent, with the required Fourier reversal. -/
def physicalCotangentGradient (L : IntervalPairL2 →L[ℂ] ℂ) : IntervalPairL2 :=
  let a := CoeffPair.cotangentCoefficients le_rfl (L.comp sourcePhysicalL2)
  sourcePhysicalL2Equiv (WithLp.toLp 2 (Coeff.reflection a.1,Coeff.reflection a.2))

/-- This gradient represents the cotangent on every physical L2 direction. -/
theorem physicalCotangentGradient_pairing (L : IntervalPairL2 →L[ℂ] ℂ) (h : IntervalPairL2) :
    (∫ x in (0:ℝ)..1, (physicalCotangentGradient L).fst x*h.fst x+
      (physicalCotangentGradient L).snd x*h.snd x) = L h := by
  let a := CoeffPair.cotangentCoefficients le_rfl (L.comp sourcePhysicalL2)
  let b := sourcePhysicalL2Equiv.symm h
  have hb : h = sourcePhysicalL2Equiv b := (sourcePhysicalL2Equiv.apply_symm_apply h).symm
  rw [intervalIntegral.integral_add (physicalL2_intervalIntegrable_mul _ _) (physicalL2_intervalIntegrable_mul _ _)]
  rw [hb]
  change (∫ x in (0:ℝ)..1, unitL2SynthesisEquiv (Coeff.reflection a.1) x*unitL2SynthesisEquiv b.fst x)+
    (∫ x in (0:ℝ)..1, unitL2SynthesisEquiv (Coeff.reflection a.2) x*unitL2SynthesisEquiv b.snd x) = _
  rw [physicalL2_reflected_pairing,physicalL2_reflected_pairing]
  have hdual := CoeffPair.dualPairing_cotangentCoefficients le_rfl (L.comp sourcePhysicalL2) b
  have hb' : CoeffPair.exponentInclusion le_rfl b = b := by
    apply WithLp.ofLp_injective
    apply Prod.ext <;> ext n <;> rfl
  simpa only [hb',ContinuousLinearMap.comp_apply,sourcePhysicalL2Equiv_apply] using hdual

/-- The physical gradient is the unique L2 representative of the full cotangent. -/
theorem physicalCotangentGradient_unique (L : IntervalPairL2 →L[ℂ] ℂ) (g : IntervalPairL2)
    (hg : ∀ h : IntervalPairL2,
      (∫ x in (0:ℝ)..1, g.fst x*h.fst x+g.snd x*h.snd x) = L h) :
    g = physicalCotangentGradient L := by
  apply physicalL2_pairing_ext
  intro h
  exact (hg h).trans (physicalCotangentGradient_pairing L h).symm

/-- The literal physical Poisson pairing of two actual L2 gradients. -/
def physicalCotangentBivector (L M : IntervalPairL2 →L[ℂ] ℂ) : ℂ :=
  -Complex.I * ∫ x in (0:ℝ)..1,
    (physicalCotangentGradient L).fst x*(physicalCotangentGradient M).snd x-
    (physicalCotangentGradient L).snd x*(physicalCotangentGradient M).fst x

/-- The physical integral agrees exactly with the source bracket, with sign and frequency reversal retained. -/
theorem physicalCotangentBivector_eq_source (L M : IntervalPairL2 →L[ℂ] ℂ) :
    physicalCotangentBivector L M = sourceBivector le_rfl (L.comp sourcePhysicalL2) (M.comp sourcePhysicalL2) := by
  let a := CoeffPair.cotangentCoefficients le_rfl (L.comp sourcePhysicalL2)
  let b := CoeffPair.cotangentCoefficients le_rfl (M.comp sourcePhysicalL2)
  rw [physicalCotangentBivector,intervalIntegral.integral_sub
    (physicalL2_intervalIntegrable_mul _ _) (physicalL2_intervalIntegrable_mul _ _)]
  change -Complex.I*((∫ x in (0:ℝ)..1,
    unitL2SynthesisEquiv (Coeff.reflection a.1) x*unitL2SynthesisEquiv (Coeff.reflection b.2) x)-
    (∫ x in (0:ℝ)..1,unitL2SynthesisEquiv (Coeff.reflection a.2) x*unitL2SynthesisEquiv (Coeff.reflection b.1) x)) = _
  rw [physicalL2_reflected_pairing,physicalL2_reflected_pairing]
  rfl

end NLS.ZakharovShabat
