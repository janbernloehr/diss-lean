import NLS.ComplexAnalysis.TracePrimitivePowerContours
import NLS.KdV.HillWeightedTraceContourDirections
import NLS.KdV.HillRecenteredPhysicalMatching
import NLS.KdV.HillFreeQuarticContour
import NLS.ComplexAnalysis.NonrealCircleIntegralComparison

/-! # Actual quartic energy-contour cotangents and coordinate variation

The energy-contour normalization is -2/(pi*i). Its derivative therefore
has coefficient -8/(pi*i), and the coordinate phase coefficient is
4/(pi*i). These are actual physical primitive contours and Fourier
directions, with no presumed KdV frequency identity.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.ZakharovShabat NLS.LinearVolterra NLS.FunctionalAnalysis
namespace NLS.KdV
variable (q : RealPeriodOneHillPotential)

def hillRealSourceQuarticContour (c : ℂ) (r : ℝ) (p : Coeff 2) : ℂ :=
  (-4:ℂ)*(2*Real.pi*I:ℂ)⁻¹ *
    (hillRecenteredTraceFamily q.val q.property.1 q.property.2).primitivePowerContour
      c r 4 (p-SpectralWeight.one.toCoeff q.val)

theorem analyticAt_hillRealSourceQuarticContour (c : ℂ) (r : ℝ) (hr : 0≤r)
    (hc : sphere c r ⊆ hillL2RealCutDomain q.val q.property.1 q.property.2) :
    AnalyticAt ℂ (hillRealSourceQuarticContour q c r) (SpectralWeight.one.toCoeff q.val) := by
  obtain ⟨V,_,h0V,hA⟩ :=
    (hillRecenteredTraceFamily q.val q.property.1 q.property.2).exists_analytic_primitivePowerContour
      c r hr 0 (fun z hz => mem_hillRecenteredContinuationDomain_base
        q.val q.property.1 q.property.2 z (hc hz))
  have hbase : AnalyticAt ℂ
      ((hillRecenteredTraceFamily q.val q.property.1 q.property.2).primitivePowerContour c r 4)
      (SpectralWeight.one.toCoeff q.val-SpectralWeight.one.toCoeff q.val) := by
    simpa only [sub_self] using hA 4 0 h0V
  have ha : AnalyticAt ℂ (fun p : Coeff 2 =>
      (hillRecenteredTraceFamily q.val q.property.1 q.property.2).primitivePowerContour
        c r 4 (p-SpectralWeight.one.toCoeff q.val)) (SpectralWeight.one.toCoeff q.val) := by
    exact hbase.comp
      (f := fun p : Coeff 2 => p-SpectralWeight.one.toCoeff q.val)
      (analyticAt_id.sub analyticAt_const)
  exact analyticAt_const.mul ha

/-- Recentring preserves the physical primitive contour at every real
source, even when its two real crossings need different point values. -/
theorem hillRealSourceQuarticContour_eq_physical (c r : ℝ) (hr : 0<r)
    (p : RealPeriodOneHillPotential) :
    hillRealSourceQuarticContour q c r (SpectralWeight.one.toCoeff p.val) =
      (-4:ℂ)*(2*Real.pi*I:ℂ)⁻¹ *
        ∮ E in C((c:ℂ),r), hillL2RealCutPrimitive (SpectralWeight.one.toCoeff p.val) E^4 := by
  unfold hillRealSourceQuarticContour TracePrimitiveFamily.primitivePowerContour
  congr 1
  apply circleIntegral_eq_of_eq_on_nonreal _ _ c r hr
  intro E _ him
  exact congrArg (fun z : ℂ => z^4) (hillRecenteredPrimitive_eq_physical_nonreal q p E him)

def hillQuarticContourGradientWeight (p : Coeff 2) (E : ℂ) : ℂ :=
  (-8:ℂ)*(Real.pi*I:ℂ)⁻¹ * hillL2RealCutPrimitive p E^3 * (hillL2RealCutRoot p E)⁻¹

theorem continuousOn_hillQuarticContourGradientWeight (c : ℂ) (r : ℝ)
    (hc : sphere c r ⊆ hillL2RealCutDomain q.val q.property.1 q.property.2) :
    ContinuousOn (hillQuarticContourGradientWeight (SpectralWeight.one.toCoeff q.val)) (sphere c r) := by
  have hP := (analyticOnNhd_hillL2RealCutPrimitive q.val q.property.1 q.property.2).continuousOn.mono hc
  have hroot := (Complex.continuous_sinh.comp_continuousOn hP).const_mul 2
  exact (continuousOn_const.mul (hP.pow 3)).mul
    (hroot.inv₀ (fun E hE => hillL2RealCutRoot_ne_zero q.val q.property.1 q.property.2 E (hc hE)))

/-- The full coefficient Frechet derivative of the actual quartic germ. -/
theorem fderiv_hillRealSourceQuarticContour_apply (c : ℂ) (r : ℝ) (hr : 0≤r)
    (hc : sphere c r ⊆ hillL2RealCutDomain q.val q.property.1 q.property.2) (h : Coeff 2) :
    (fderiv ℂ (hillRealSourceQuarticContour q c r) (SpectralWeight.one.toCoeff q.val)) h =
      ∮ E in C(c,r), hillQuarticContourGradientWeight (SpectralWeight.one.toCoeff q.val) E *
        (fderiv ℂ (fun p : Coeff 2 => hillL2Discriminant p E) (SpectralWeight.one.toCoeff q.val)) h := by
  let p0 := SpectralWeight.one.toCoeff q.val
  let f := hillRecenteredTraceFamily q.val q.property.1 q.property.2
  let J := f.primitivePowerContour c r 4
  have hc0 (E : ℂ) (hE : E∈sphere c r) : (E,0)∈f.continuationDomain :=
    mem_hillRecenteredContinuationDomain_base q.val q.property.1 q.property.2 E (hc hE)
  obtain ⟨V,_,h0V,hA⟩ := f.exists_analytic_primitivePowerContour c r hr 0 hc0
  have hJ : AnalyticAt ℂ J 0 := hA 4 0 h0V
  have hJ' : AnalyticAt ℂ J (p0-p0) := by simpa only [sub_self] using hJ
  have hcomp := (hJ'.differentiableAt.hasFDerivAt.comp p0 (f := fun p : Coeff 2 => p-p0)
    ((hasFDerivAt_id p0).sub_const p0))
  have hdiff : DifferentiableAt ℂ (fun p : Coeff 2 => J (p-p0)) p0 := hcomp.differentiableAt
  have hd : (fderiv ℂ (fun p : Coeff 2 => J (p-p0)) p0) h = (fderiv ℂ J 0) h := by
    simpa only [sub_self,ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply,
      Function.comp_def] using congrArg (fun L : Coeff 2 →L[ℂ] ℂ => L h) hcomp.fderiv
  change (fderiv ℂ (fun p : Coeff 2 => (-4:ℂ)*(2*Real.pi*I:ℂ)⁻¹*J (p-p0)) p0) h = _
  rw [fderiv_const_mul hdiff]
  change (-4:ℂ)*(2*Real.pi*I:ℂ)⁻¹*((fderiv ℂ (fun p : Coeff 2 => J (p-p0)) p0) h) = _
  rw [hd,f.fderiv_primitivePowerContour_apply c r hr 4 0 h hc0,
    ← circleIntegral.integral_const_mul]
  apply circleIntegral.integral_congr hr
  intro E _
  dsimp only []
  have htrace : (fderiv ℂ (fun p : Coeff 2 => f.trace (E,p)) 0) h =
      (fderiv ℂ (fun p : Coeff 2 => hillL2Discriminant p E) p0) h := by
    have ha : AnalyticAt ℂ (fun p : Coeff 2 => hillL2Discriminant p E) p0 :=
      (analyticOnNhd_hillL2Discriminant_joint (E,p0) (mem_univ _)).comp
        (f := fun p : Coeff 2 => (E,p)) (analyticAt_const.prod analyticAt_id)
    have ha' : AnalyticAt ℂ (fun p : Coeff 2 => hillL2Discriminant p E) ((0:Coeff 2)+p0) := by
      simpa only [zero_add] using ha
    have hh := ha'.differentiableAt.hasFDerivAt.comp 0
      (f := fun p : Coeff 2 => p+p0) ((hasFDerivAt_id (0:Coeff 2)).add_const p0)
    simpa only [f,hillRecenteredTraceFamily,zero_add,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply,Function.comp_def] using
        congrArg (fun L : Coeff 2 →L[ℂ] ℂ => L h) hh.fderiv
  rw [htrace]
  change (-4:ℂ)*(2*Real.pi*I:ℂ)⁻¹*((4:ℂ)*hillRecenteredPrimitive q.val q.property.1 q.property.2 (E,0)^3 *
    (hillRecenteredRoot q.val q.property.1 q.property.2 (E,0))⁻¹ * _) = _
  rw [hillRecenteredPrimitive_base,hillRecenteredRoot_base]
  dsimp only [hillQuarticContourGradientWeight,p0]
  ring

def hillQuarticContourDirection (c : ℂ) (r : ℝ) : Coeff 2 :=
  hillL2WeightedTraceContourDirection (SpectralWeight.one.toCoeff q.val)
    (hillQuarticContourGradientWeight (SpectralWeight.one.toCoeff q.val)) c r

/-- The quartic tangent satisfies the genuine weak Hamiltonian identity
for its proved source cotangent, with the physical Gardner sign. -/
theorem hillQuarticContourDirection_hamiltonian_identity (c : ℂ) (r : ℝ) (hr : 0≤r)
    (hc : sphere c r ⊆ hillL2RealCutDomain q.val q.property.1 q.property.2)
    (f g : Curve ℂ) (hf : AbsolutelyContinuousOnInterval (extend f) 0 1)
    (hfg : deriv (extend f)=ᵐ[volume.restrict (Ioc (0:ℝ) 1)] extend g)
    (hfend : extend f 0=extend f 1) (hgend : extend g 0=extend g 1) :
    hillPhysicalCurvePairing f (hillQuarticContourDirection q c r) =
      -(fderiv ℂ (hillRealSourceQuarticContour q c r) (SpectralWeight.one.toCoeff q.val))
        (Coeff.periodDouble (NLS.Fourier.unitCurveCoefficientsCLM g)) := by
  rw [fderiv_hillRealSourceQuarticContour_apply q c r hr hc]
  exact hillPhysicalCurvePairing_weightedTraceContourDirection q _ c r hr
    (continuousOn_hillQuarticContourGradientWeight q c r hc) f g hf hfg hfend hgend

/-- The exact energy-contour phase coefficient, before identifying a
contour or its limit with the full physical KdV Hamiltonian. -/
theorem fderiv_hillDirichletAbelianCoordinate_extension_quarticContourDirection
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))
    (c : ℂ) (r : ℝ) (hr : 0≤r)
    (hc : sphere c r ⊆ hillL2RealCutDomain q.val q.property.1 q.property.2)
    (n : ℕ) (hn : 1≤n) (C : Coeff 2 → ℂ)
    (hC : DifferentiableAt ℂ C (SpectralWeight.one.toCoeff q.val))
    (hmatch : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      C (SpectralWeight.one.toCoeff p.val)=hillDirichletAbelianCoordinate p.val p.property.1 p.property.2 n hn) :
    (fderiv ℂ C (SpectralWeight.one.toCoeff q.val)) (hillQuarticContourDirection q c r) =
      I*((4:ℂ)*(Real.pi*I:ℂ)⁻¹ *
        ∮ E in C(c,r), hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q.val) E^3 *
          hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 n hn E /
            hillL2RealCutRoot (SpectralWeight.one.toCoeff q.val) E) *
              hillDirichletAbelianCoordinate q.val q.property.1 q.property.2 n hn := by
  rw [hillQuarticContourDirection,
    fderiv_hillDirichletAbelianCoordinate_extension_weightedTraceContourDirection q h0q h0r
      _ c r hr (continuousOn_hillQuarticContourGradientWeight q c r hc) n hn C hC hmatch]
  have he : (fun E => hillQuarticContourGradientWeight (SpectralWeight.one.toCoeff q.val) E *
      hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 n hn E) =
      (fun E => ((-8:ℂ)*(Real.pi*I:ℂ)⁻¹) *
        (hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q.val) E^3 *
          hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 n hn E /
            hillL2RealCutRoot (SpectralWeight.one.toCoeff q.val) E)) := by
    funext E
    dsimp only [hillQuarticContourGradientWeight]
    ring
  rw [he,circleIntegral.integral_const_mul]
  ring

end NLS.KdV
