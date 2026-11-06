import NLS.KdV.HillUniformCenteredMeanFreePrimitives
import NLS.KdV.HillDeflatedCosineMean

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open MeasureTheory NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

/-- The actual centered cosine-mean subtraction recovers the original
physical mean-free differential, including its own-index subtraction one. -/
theorem centeredMeanFree_hillCenteredComplexRegularGapNumerator_eq_physical
    (G : ℂ × Coeff 2 → ℂ) (n k : ℕ) (hn : 1≤n) (hk : 1≤k)
    (q : RealPeriodOneHillPotential) (E : Set ℂ)
    (hG : ∀ z : ℂ, G (z,SpectralWeight.one.toCoeff q.val)=hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 n hn z)
    (hroot : ∀ z∈E, hillFilledFreeGapRoot h0q h0r k (z,SpectralWeight.one.toCoeff q.val)=
      hillDeflatedEnergyCanonicalRoot q.val q.property.1 q.property.2 k z)
    (hMid : hillLocalGapMidpoint 0 h0q h0r k (SpectralWeight.one.toCoeff q.val)=
      (hillRealGapCenter q.val q.property.1 q.property.2 k : ℂ))
    (hSq : hillLocalGapSquare 0 h0q h0r k (SpectralWeight.one.toCoeff q.val)=
      (2*(hillRealGapHalfLength q.val q.property.1 q.property.2 k : ℂ))^2)
    (hcos : ∀ θ∈Icc (0:ℝ) Real.pi,
      cosineGapPoint (hillRealGapCenter q.val q.property.1 q.property.2 k)
        (hillRealGapHalfLength q.val q.property.1 q.property.2 k) (θ : ℂ)∈E)
    (w : ℂ) (hw : (hillRealGapCenter q.val q.property.1 q.property.2 k : ℂ)+w∈E) :
    centeredMeanFree (hillCenteredComplexRegularGapNumerator h0q h0r G k)
      (fun p => hillLocalGapSquare 0 h0q h0r k p/4) (w,SpectralWeight.one.toCoeff q.val)=
        -I*hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 n hn
            ((hillRealGapCenter q.val q.property.1 q.property.2 k : ℂ)+w)/
          hillDeflatedEnergyCanonicalRoot q.val q.property.1 q.property.2 k
            ((hillRealGapCenter q.val q.property.1 q.property.2 k : ℂ)+w)-(if k=n then 1 else 0) := by
  let p := SpectralWeight.one.toCoeff q.val
  let g := hillComplexRegularGapNumerator h0q h0r G k
  have hraw (z : ℂ) (hz : z∈E) : g (z,p)=
      -I*hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 n hn z/
        hillDeflatedEnergyCanonicalRoot q.val q.property.1 q.property.2 k z := by
    dsimp only [g,hillComplexRegularGapNumerator,p]
    rw [hG z,hroot z hz]
  have hm := hillLocalGapCosineMean_eq_physical 0 h0q h0r g n k hn hk q E hMid hSq hcos hraw
  have he : parametricCosineMean (hillCenteredComplexRegularGapNumerator h0q h0r G k) (fun _ => 0)
      (sqrt (hillLocalGapSquare 0 h0q h0r k p/4),p)=hillLocalGapCosineMean 0 h0q h0r g k p := by
    unfold parametricCosineMean hillLocalGapCosineMean hillCenteredComplexRegularGapNumerator
    simp only [zero_add]
    rfl
  unfold centeredMeanFree
  change g (hillLocalGapMidpoint 0 h0q h0r k p+w,p)-
    parametricCosineMean (hillCenteredComplexRegularGapNumerator h0q h0r G k) (fun _ => 0)
      (sqrt (hillLocalGapSquare 0 h0q h0r k p/4),p)/(Real.pi : ℂ)=_
  rw [he,hm,hMid,hraw _ hw]
  have hpi : (Real.pi : ℂ)≠0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp

end NLS.KdV
