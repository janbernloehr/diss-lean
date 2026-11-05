import NLS.KdV.HillMovingContourSourceNeighborhood
import NLS.KdV.HillClosedCurveCoefficientContinuity
import NLS.KdV.HillContourHamiltonianSources
import NLS.KdV.HillDirichletHamiltonianSources
import NLS.ComplexAnalysis.CompactFiberIntegralContinuity
import NLS.ComplexAnalysis.NonrealCircleIntegralVectorComparison

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.ZakharovShabat NLS.FunctionalAnalysis NLS.LinearVolterra
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



private theorem continuous_spatial_contour_family {A : Type} [TopologicalSpace A]
    (P : A → Coeff 2) (hP : Continuous P) (c : A → ℂ) (R : A → ℝ)
    (hc : Continuous c) (hR : Continuous R) (w : A → ℂ → ℂ)
    (hw : Continuous (fun t : A × Icc (0 : ℝ) (2*Real.pi) =>
      w t.1 (circleMap (c t.1) (R t.1) t.2.val))) :
    Continuous (fun p => hillEnergyGradientSpatialContour (P p) (w p) (c p) (R p)) := by
  let Z : A × Icc (0 : ℝ) (2*Real.pi) → ℂ := fun t => circleMap (c t.1) (R t.1) t.2.val
  have hZ : Continuous Z := by
    dsimp only [Z,circleMap]
    fun_prop
  have hg : Continuous (fun t : A × Icc (0 : ℝ) (2*Real.pi) => hillEnergyDiscriminantGradientSpatialCurve (P t.1) (Z t)) :=
    Continuous.comp (f := fun t : A × Icc (0 : ℝ) (2*Real.pi) => (Z t,P t.1))
      continuous_hillEnergyDiscriminantGradientSpatialCurve_joint (hZ.prodMk (hP.comp continuous_fst))
  exact continuous_circleIntegral_of_continuous_moving_section
    (fun t : A × ℂ => w t.1 t.2 • hillEnergyDiscriminantGradientSpatialCurve (P t.1) t.2)
    c R hR (hw.smul hg)

private theorem continuous_recentered_weight_section {A : Type} [TopologicalSpace A]
    (q : RealPeriodOneHillPotential) (P : A → Coeff 2) (hP : Continuous P)
    (Z : A × Icc (0 : ℝ) (2*Real.pi) → ℂ) (hZ : Continuous Z) (m : ℕ)
    (hD : ∀ t, (Z t,P t.1-SpectralWeight.one.toCoeff q.val)∈
      hillRecenteredContinuationDomain q.val q.property.1 q.property.2) :
    Continuous (fun t : A × Icc (0 : ℝ) (2*Real.pi) => -(Real.pi : ℂ)⁻¹*(Z t)^m*
      (hillRecenteredRoot q.val q.property.1 q.property.2 (Z t,P t.1-SpectralWeight.one.toCoeff q.val))⁻¹) := by
  have hroot : Continuous (fun t : A × Icc (0 : ℝ) (2*Real.pi) =>
      hillRecenteredRoot q.val q.property.1 q.property.2 (Z t,P t.1-SpectralWeight.one.toCoeff q.val)) :=
    (analyticOnNhd_hillRecenteredRoot q.val q.property.1 q.property.2).continuousOn.comp_continuous
      (hZ.prodMk ((hP.comp continuous_fst).sub continuous_const)) hD
  have hinv := hroot.inv₀ (fun t => (hillRecenteredTraceFamily q.val q.property.1 q.property.2).root_ne_zero _ (hD t))
  exact (continuous_const.mul (hZ.pow m)).mul hinv

/-- The genuine Dirichlet Hamiltonian source depends continuously on every real rough source. -/
theorem continuous_hillDirichletHamiltonianSource (n : ℕ) (hn : 1≤n) :
    Continuous (fun q : RealPeriodOneHillPotential => hillDirichletHamiltonianSource q n hn) := by
  apply continuous_hillClosedCurveCoefficients_family
  exact (continuous_hillDirichletGradientSpatialCurve n hn).neg

private theorem continuous_physical_spatial_contour (n : ℕ) (hn : 1≤n) (m : ℕ) :
    Continuous (fun q : RealPeriodOneHillPotential => hillEnergyGradientSpatialContour (SpectralWeight.one.toCoeff q.val)
      (hillPhysicalMomentGradientWeight (SpectralWeight.one.toCoeff q.val) m)
      (hillRealGapCenter q.val q.property.1 q.property.2 n : ℂ)
      (hillRealGapHalfLength q.val q.property.1 q.property.2 n+hillRealGapCollar q.val q.property.1 q.property.2 n)) := by
  apply continuous_iff_continuousAt.mpr
  intro q
  obtain ⟨V,hV,hqV,hdom⟩ := exists_hillMovingIntrinsicContour_recentered_neighborhood q n hn
  let c : RealPeriodOneHillPotential → ℂ := fun p => hillRealGapCenter p.val p.property.1 p.property.2 n
  let R : RealPeriodOneHillPotential → ℝ := fun p => hillRealGapHalfLength p.val p.property.1 p.property.2 n+
    hillRealGapCollar p.val p.property.1 p.property.2 n
  have hc : Continuous c := Complex.continuous_ofReal.comp (continuous_hillRealGapCenter n)
  have hcollar : Continuous (fun p : RealPeriodOneHillPotential => hillRealGapCollar p.val p.property.1 p.property.2 n) := by
    unfold hillRealGapCollar
    exact (((continuous_hillRealLabels (2*n-1)).sub (continuous_hillRealLabels (2*n-2))).min
      ((continuous_hillRealLabels (2*n+1)).sub (continuous_hillRealLabels (2*n)))).div_const 4
  have hR : Continuous R := (continuous_hillRealGapHalfLength n).add hcollar
  let P : V → Coeff 2 := fun p => SpectralWeight.one.toCoeff p.val.val
  have hP : Continuous P := SpectralWeight.one.toCoeff.continuous.comp
    (continuous_subtype_val.comp continuous_subtype_val)
  let w : V → ℂ → ℂ := fun p z => -(Real.pi : ℂ)⁻¹*z^m*
    (hillRecenteredRoot q.val q.property.1 q.property.2 (z,P p-SpectralWeight.one.toCoeff q.val))⁻¹
  let L : V → Curve ℂ := fun p => hillEnergyGradientSpatialContour (P p) (w p) (c p.val) (R p.val)
  let K := Icc (0 : ℝ) (2*Real.pi)
  let Z : V × K → ℂ := fun t => circleMap (c t.1.val) (R t.1.val) t.2.val
  have hZ : Continuous Z := by
    dsimp only [Z,circleMap]
    fun_prop
  have hD (t : V × K) : (Z t,P t.1-SpectralWeight.one.toCoeff q.val)∈
      hillRecenteredContinuationDomain q.val q.property.1 q.property.2 :=
    hdom t.1.val t.1.property (Z t) (circleMap_mem_sphere (c t.1.val)
      (add_nonneg (hillRealGapContour_geometry t.1.val.val t.1.val.property.1 t.1.val.property.2 n hn).1
        (hillRealGapContour_geometry t.1.val.val t.1.val.property.1 t.1.val.property.2 n hn).2.1.le) t.2.val)
  have hw : Continuous (fun t : V × K => w t.1 (Z t)) :=
    continuous_recentered_weight_section q P hP Z hZ m hD
  have hL : Continuous L := continuous_spatial_contour_family P hP
    (fun p : V => c p.val) (fun p : V => R p.val) (hc.comp continuous_subtype_val)
    (hR.comp continuous_subtype_val) w hw
  have heq (p : V) : L p=hillEnergyGradientSpatialContour (P p)
      (hillPhysicalMomentGradientWeight (P p) m) (c p.val) (R p.val) := by
    apply circleIntegral_eq_of_eq_on_nonreal_vector _ _ (hillRealGapCenter p.val.val p.val.property.1 p.val.property.2 n)
      (R p.val) (add_pos_of_nonneg_of_pos
        (hillRealGapContour_geometry p.val.val p.val.property.1 p.val.property.2 n hn).1
        (hillRealGapContour_geometry p.val.val p.val.property.1 p.val.property.2 n hn).2.1)
    intro z _ him
    dsimp only [w]
    rw [hillRecenteredRoot_eq_physical_nonreal q p.val z him]
    rfl
  have hphys : Continuous (fun p : V => hillEnergyGradientSpatialContour (P p)
      (hillPhysicalMomentGradientWeight (P p) m) (c p.val) (R p.val)) := hL.congr heq
  have hOn : ContinuousOn (fun p : RealPeriodOneHillPotential =>
      hillEnergyGradientSpatialContour (SpectralWeight.one.toCoeff p.val)
        (hillPhysicalMomentGradientWeight (SpectralWeight.one.toCoeff p.val) m) (c p) (R p)) V :=
    continuousOn_iff_continuous_domRestrict.mpr hphys
  exact (hOn q hqV).continuousAt (hV.mem_nhds hqV)

/-- Every genuine physical moment Hamiltonian source is continuous in the original
weighted Hill space, including at collapsed gaps and terminal endpoints. -/
theorem continuous_hillPhysicalMomentHamiltonianSource (n : ℕ) (hn : 1≤n) (m : ℕ) :
    Continuous (fun q : RealPeriodOneHillPotential => hillPhysicalMomentHamiltonianSource q.val q.property.1 q.property.2 n hn m) := by
  apply continuous_hillClosedCurveCoefficients_family
  exact (continuous_physical_spatial_contour n hn m).neg

end NLS.KdV
