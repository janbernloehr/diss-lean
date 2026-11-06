import NLS.KdV.HillDeflatedCosineMean
import NLS.ComplexAnalysis.BoundedCenteredMeanFreeQuadratic

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

/-- Centering any actual physical deflated chart and subtracting its
cosine mean gives the source-normalized regular differential. -/
theorem centeredMeanFree_deflated_chart_eq_physical
    (H : ℂ × Coeff 2 → ℂ) (n k : ℕ) (hn : 1≤n) (hk : 1≤k)
    (p : RealPeriodOneHillPotential) (E : Set ℂ)
    (hMid : hillLocalGapMidpoint q hq hr k (SpectralWeight.one.toCoeff p.val)=
      (hillRealGapCenter p.val p.property.1 p.property.2 k : ℂ))
    (hSq : hillLocalGapSquare q hq hr k (SpectralWeight.one.toCoeff p.val)=
      (2*(hillRealGapHalfLength p.val p.property.1 p.property.2 k : ℂ))^2)
    (hcos : ∀ θ∈Icc (0 : ℝ) Real.pi, cosineGapPoint (hillRealGapCenter p.val p.property.1 p.property.2 k)
      (hillRealGapHalfLength p.val p.property.1 p.property.2 k) (θ : ℂ)∈E)
    (hH : ∀ z∈E, H (z,SpectralWeight.one.toCoeff p.val)=
      -I*hillAbelianSelectedGlobalPsi p.val p.property.1 p.property.2 n hn z/
        hillDeflatedEnergyCanonicalRoot p.val p.property.1 p.property.2 k z)
    (w : ℂ) (hw : (hillRealGapCenter p.val p.property.1 p.property.2 k : ℂ)+w∈E) :
    centeredMeanFree (fun t : ℂ × Coeff 2 => H (hillLocalGapMidpoint q hq hr k t.2+t.1,t.2))
      (fun p => hillLocalGapSquare q hq hr k p/4) (w,SpectralWeight.one.toCoeff p.val)=
        -I*hillAbelianSelectedGlobalPsi p.val p.property.1 p.property.2 n hn
          ((hillRealGapCenter p.val p.property.1 p.property.2 k : ℂ)+w)/
          hillDeflatedEnergyCanonicalRoot p.val p.property.1 p.property.2 k
            ((hillRealGapCenter p.val p.property.1 p.property.2 k : ℂ)+w)-(if k=n then 1 else 0) := by
  let f : ℂ × Coeff 2 → ℂ := fun t => H (hillLocalGapMidpoint q hq hr k t.2+t.1,t.2)
  have hm := hillLocalGapCosineMean_eq_physical q hq hr H n k hn hk p E hMid hSq hcos hH
  have he : parametricCosineMean f (fun _ => 0)
      (sqrt (hillLocalGapSquare q hq hr k (SpectralWeight.one.toCoeff p.val)/4),SpectralWeight.one.toCoeff p.val)=
      hillLocalGapCosineMean q hq hr H k (SpectralWeight.one.toCoeff p.val) := by
    unfold parametricCosineMean hillLocalGapCosineMean
    simp only [zero_add]
    rfl
  change H (hillLocalGapMidpoint q hq hr k (SpectralWeight.one.toCoeff p.val)+w,SpectralWeight.one.toCoeff p.val)-
    parametricCosineMean f (fun _ => 0)
      (sqrt (hillLocalGapSquare q hq hr k (SpectralWeight.one.toCoeff p.val)/4),SpectralWeight.one.toCoeff p.val)/(Real.pi : ℂ)=_
  rw [he,hm,hMid,hH _ hw]
  have hpi : (Real.pi : ℂ)≠0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp

end NLS.KdV
