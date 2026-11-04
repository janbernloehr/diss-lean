import NLS.KdV.HillLocalGapPhysicalMatching
import NLS.ComplexAnalysis.LocalAnalyticSquareRoot

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV



theorem continuous_hillRealGapHalfLength (k : ℕ) :
    Continuous (fun p : RealPeriodOneHillPotential => hillRealGapHalfLength p.val p.property.1 p.property.2 k) :=
  ((continuous_hillRealLabels (2*k)).sub (continuous_hillRealLabels (2*k-1))).div_const 2

theorem continuous_hillRealGapCenter (k : ℕ) :
    Continuous (fun p : RealPeriodOneHillPotential => hillRealGapCenter p.val p.property.1 p.property.2 k) :=
  ((continuous_hillRealLabels (2*k-1)).add (continuous_hillRealLabels (2*k))).div_const 2

variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

theorem exists_hillGapHalfLength_analytic_extension (k : ℕ) (hk : 1 ≤ k)
    (hgap : hillRealGapHalfLength q hq hr k ≠ 0) :
    ∃ d : Coeff 2 → ℂ, AnalyticAt ℂ d (SpectralWeight.one.toCoeff q) ∧
      d (SpectralWeight.one.toCoeff q) = (hillRealGapHalfLength q hq hr k : ℂ) ∧
      (∀ᶠ p : Coeff 2 in 𝓝 (SpectralWeight.one.toCoeff q),
        d p ≠ 0 ∧ (d p)^2 = hillLocalGapSquare q hq hr k p/4) ∧
      ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
        d (SpectralWeight.one.toCoeff p.val) = (hillRealGapHalfLength p.val p.property.1 p.property.2 k : ℂ) := by
  let p0 : RealPeriodOneHillPotential := ⟨q,hq,hr⟩
  let P : RealPeriodOneHillPotential → Coeff 2 := fun p => SpectralWeight.one.toCoeff p.val
  have hP : Continuous P := SpectralWeight.one.toCoeff.continuous.comp continuous_subtype_val
  obtain ⟨U,_,hqU,_,hS,_⟩ := exists_hillLocalGapSymmetricData_analytic_neighborhood q hq hr k hk
  have hbase : hillLocalGapSquare q hq hr k (SpectralWeight.one.toCoeff q)/4 =
      (hillRealGapHalfLength q hq hr k : ℂ)^2 := by
    rw [(hillLocalGapSymmetricData_eq_physical_of_geometry q hq hr q hq hr k hk
      (hillRealGapContour_band_bounds q hq hr k hk)
      (hillRealGapSegment_subset_intrinsic_contour_ball q hq hr k hk)).2]
    ring
  obtain ⟨V,hV,hqV,d,hd,hd0,hdprop⟩ := exists_local_analytic_squareRoot
    (fun p => hillLocalGapSquare q hq hr k p/4) (SpectralWeight.one.toCoeff q)
    (hillRealGapHalfLength q hq hr k : ℂ) ((hS _ hqU).div_const) (ofReal_ne_zero.mpr hgap) hbase
  have hcomplex : ∀ᶠ p in 𝓝 (SpectralWeight.one.toCoeff q),
      d p ≠ 0 ∧ (d p)^2 = hillLocalGapSquare q hq hr k p/4 :=
    Filter.mem_of_superset (hV.mem_nhds hqV) hdprop
  refine ⟨d,hd _ hqV,hd0,hcomplex,?_⟩
  obtain ⟨W,hW,hqW,hmatch⟩ := exists_hillLocalGapSymmetricData_physical_neighborhood q hq hr k hk
  have hdc : ContinuousAt (fun p : RealPeriodOneHillPotential => d (P p)) p0 :=
    ContinuousAt.comp (f := P) (hd _ hqV).continuousAt hP.continuousAt
  have hhc : ContinuousAt (fun p : RealPeriodOneHillPotential =>
      (hillRealGapHalfLength p.val p.property.1 p.property.2 k : ℂ)) p0 :=
    (continuous_ofReal.comp (continuous_hillRealGapHalfLength k)).continuousAt
  apply eventuallyEq_of_sq_eq_of_continuousAt _ _ p0 hdc hhc hd0 (ofReal_ne_zero.mpr hgap)
  filter_upwards [hP.continuousAt.tendsto.eventually hcomplex,hW.mem_nhds hqW] with p hp hpW
  rw [hp.2,(hmatch p hpW).2]
  ring

end NLS.KdV
