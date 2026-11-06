import NLS.Articles.KdVKdV2Frequencies.NativeFiniteGapHamiltonianVariation
import NLS.Articles.KdVKdV2Frequencies.OriginalRoughActionGerms
import NLS.KdV.NativeHillPhysicalDirection
import NLS.KdV.HillLocalContourAction
import NLS.KdV.HillActionHamiltonianDirections

/-! # Exact physical contour differentials of the actual native actions

The actual source action Banach differential equals the differential of
ANY matching original physical L2 action germ. In particular it is the
literal original contour action differential at every gap, including closed gaps.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology MeasureTheory NLS.KdV NLS.LinearVolterra NLS.Fourier
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData

/-- The actual native Banach action differential is the restriction of the
SAME global rough signed action germ, with no assumed derivative matching. -/
theorem nativeSourceActionSequence_fderiv_eq_rough (D : GlobalRoughAbelianForwardData)
    (m : ℕ) (r : ℝ) (hrs : r=2*((m : ℝ)+1/2))
    (q h : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (m : ℝ))) (n : ℕ+) :
    ((fderiv ℝ (D.nativeSourceActionSequence m r hrs) q) h).val (n : ℤ) =
      (fderiv ℂ (D.roughActionCoordinate n) (nativeHillSource m q.val)) (nativeHillSource m h.val) := by
  let J := ((nativeHillSource m).restrictScalars ℝ).comp
    (physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (m : ℝ))).subtypeL
  let E := (WeightedCoeff.evalCLM (Weight.sobolev r) 1 (n : ℤ)).restrictScalars ℝ
  have hA := E.hasFDerivAt.comp q
    (D.nativeSourceActionSequence_analytic m r hrs q (mem_univ _)).differentiableAt.hasFDerivAt
  have hF := (D.roughActionCoordinate_analytic n _ (D.real_mem_domain _
    (nativeHillSource_real m q.val q.property.1))).differentiableAt.hasFDerivAt.restrictScalars ℝ
  have hFJ := hF.comp q J.hasFDerivAt
  have he (u : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (m : ℝ))) :
      (D.nativeSourceActionSequence m r hrs u).val (n : ℤ) = D.roughActionCoordinate n (J u) := by
    rw [D.nativeSourceActionSequence_apply,if_pos (by exact_mod_cast n.pos : (0 : ℤ)<n)]
    rfl
  have hA' : HasFDerivAt (fun u => (D.nativeSourceActionSequence m r hrs u).val (n : ℤ))
      (E.comp (fderiv ℝ (D.nativeSourceActionSequence m r hrs) q)) q := by
    simpa only [Function.comp_def] using! hA
  have hFJ' : HasFDerivAt (fun u => (D.nativeSourceActionSequence m r hrs u).val (n : ℤ))
      (((fderiv ℂ (D.roughActionCoordinate n) (nativeHillSource m q.val)).restrictScalars ℝ).comp J) q := by
    apply HasFDerivAt.congr_of_eventuallyEq hFJ
    exact Eventually.of_forall he
  have hd := congrArg (fun L => L h) (hA'.unique hFJ')
  simpa only [ContinuousLinearMap.comp_apply] using! hd

/-- Every actual matching physical contour germ gives the native source
first variation in the original even L2 direction, on the entire native source. -/
theorem nativeSourceActionSequence_fderiv_eq_physical_germ (D : GlobalRoughAbelianForwardData)
    (m : ℕ) (r : ℝ) (hrs : r=2*((m : ℝ)+1/2))
    (q h : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (m : ℝ))) (n : ℕ+)
    (G : Coeff 2 → ℂ)
    (hG : AnalyticAt ℂ G (SpectralWeight.one.toCoeff (nativeHillPhysicalSource m q.val q.property.1).val))
    (hmatch : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (nativeHillPhysicalSource m q.val q.property.1),
      G (SpectralWeight.one.toCoeff p.val) = (hillRealGapIntegral p.val p.property.1 p.property.2 n 0 : ℂ)) :
    ((fderiv ℝ (D.nativeSourceActionSequence m r hrs) q) h).val (n : ℤ) =
      (fderiv ℂ G (SpectralWeight.one.toCoeff (nativeHillPhysicalSource m q.val q.property.1).val))
        (SpectralWeight.one.toCoeff (nativeHillPhysicalDirection m h.val)) := by
  have hp : hillOriginalHminusSource (nativeHillPhysicalSource m q.val q.property.1).val = nativeHillSource m q.val := by
    rw [hillOriginalHminusSource_eq_physical]
    exact (nativeHillSource_eq_physical m q.val q.property.1).symm
  have hd := D.roughActionCoordinate_fderiv_original (nativeHillPhysicalSource m q.val q.property.1) n
    G hG hmatch (nativeHillPhysicalDirection m h.val) (nativeHillPhysicalDirection_even m h.val)
  rw [hp,nativeHillPhysicalDirection_rough] at hd
  exact (D.nativeSourceActionSequence_fderiv_eq_rough m r hrs q h n).trans hd

/-- The actual native action differential is the literal original contour
action differential, with the physical normalization and all closed gaps included. -/
theorem nativeSourceActionSequence_fderiv_eq_contour (D : GlobalRoughAbelianForwardData)
    (m : ℕ) (r : ℝ) (hrs : r=2*((m : ℝ)+1/2))
    (q h : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (m : ℝ))) (n : ℕ+) :
    ((fderiv ℝ (D.nativeSourceActionSequence m r hrs) q) h).val (n : ℤ) =
      (fderiv ℂ (hillLocalContourAction (nativeHillPhysicalSource m q.val q.property.1).val
        (nativeHillPhysicalSource m q.val q.property.1).property.1
        (nativeHillPhysicalSource m q.val q.property.1).property.2 n)
        (SpectralWeight.one.toCoeff (nativeHillPhysicalSource m q.val q.property.1).val))
      (SpectralWeight.one.toCoeff (nativeHillPhysicalDirection m h.val)) :=
  D.nativeSourceActionSequence_fderiv_eq_physical_germ m r hrs q h n _
    (analyticAt_hillLocalContourAction _ _ _ n n.pos)
    (hillLocalContourAction_eventually_eq_physical _ _ _ n n.pos)

/-- The actual physical native hierarchy first variation at a finite-gap
source is the FINITE intrinsic-frequency sum of original contour differentials. -/
theorem nativeSourceHierarchyHamiltonian_fderiv_finite_gap_contour
    (D : GlobalRoughAbelianForwardData) (m : ℕ) (r : ℝ) (hrs : r=2*((m : ℝ)+1/2))
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (m : ℝ))) (S : Finset ℕ+)
    (hq : ∀ n : ℕ+, n ∉ S → hillRealGapHalfLength
      (nativeHillPhysicalSource m q.val q.property.1).val
      (nativeHillPhysicalSource m q.val q.property.1).property.1
      (nativeHillPhysicalSource m q.val q.property.1).property.2 n = 0)
    (h : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (m : ℝ))) :
    (fderiv ℝ (D.nativeSourceHierarchyHamiltonian m) q) h = ∑ n ∈ S,
      (fderiv ℂ (hillLocalContourAction (nativeHillPhysicalSource m q.val q.property.1).val
        (nativeHillPhysicalSource m q.val q.property.1).property.1
        (nativeHillPhysicalSource m q.val q.property.1).property.2 n)
        (SpectralWeight.one.toCoeff (nativeHillPhysicalSource m q.val q.property.1).val))
      (SpectralWeight.one.toCoeff (nativeHillPhysicalDirection m h.val))*
        (D.originalHierarchyFrequency m r hrs
          (originalPositiveActions m r hrs (D.rawIntegerForwardHomeomorph m q)) n : ℂ) := by
  rw [D.nativeSourceHierarchyHamiltonian_fderiv_finite_gap m r hrs q S hq h]
  apply Finset.sum_congr rfl
  intro n _
  rw [D.nativeSourceActionSequence_fderiv_eq_contour]

/-- The verified physical action Hamiltonian direction gives the actual
native source action differential against every matching physical derivative test. -/
theorem nativeSourceActionSequence_weak_hamiltonian (D : GlobalRoughAbelianForwardData)
    (m : ℕ) (r : ℝ) (hrs : r=2*((m : ℝ)+1/2))
    (q h : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (m : ℝ))) (n : ℕ+)
    (f g : Curve ℂ) (hf : AbsolutelyContinuousOnInterval (extend f) 0 1)
    (hfg : deriv (extend f)=ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] extend g)
    (hfend : extend f 0=extend f 1) (hgend : extend g 0=extend g 1)
    (hg : ∀ j : ℤ, h.val.val j = unitCurveCoefficientsCLM g j) :
    hillPhysicalCurvePairing f (hillL2TracePeriodDirection (nativeHillPhysicalSource m q.val q.property.1).val
      (nativeHillPhysicalSource m q.val q.property.1).property.1
      (nativeHillPhysicalSource m q.val q.property.1).property.2 n) =
        -((fderiv ℝ (D.nativeSourceActionSequence m r hrs) q) h).val (n : ℤ) := by
  let p := nativeHillPhysicalSource m q.val q.property.1
  have hh : SpectralWeight.one.toCoeff (nativeHillPhysicalDirection m h.val) =
      Coeff.periodDouble (unitCurveCoefficientsCLM g) := by
    rw [nativeHillPhysicalDirection_toCoeff]
    congr 1
    ext j
    rw [WeightedCoeff.sobolevToL2_apply,hg j]
  rw [D.nativeSourceActionSequence_fderiv_eq_contour,hh]
  exact hillL2TracePeriodDirection_action_hamiltonian_identity p.val p.property.1 p.property.2
    n n.pos _ (analyticAt_hillLocalContourAction _ _ _ n n.pos).differentiableAt
    (hillLocalContourAction_eventually_eq_physical _ _ _ n n.pos) f g hf hfg hfend hgend

/-- Actual finite-gap Hamiltonian first variations equal the physical weak
pairings with the FINITE intrinsic-frequency-weighted action directions. -/
theorem nativeSourceHierarchyHamiltonian_finite_gap_weak
    (D : GlobalRoughAbelianForwardData) (m : ℕ) (r : ℝ) (hrs : r=2*((m : ℝ)+1/2))
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (m : ℝ))) (S : Finset ℕ+)
    (hq : ∀ n : ℕ+, n ∉ S → hillRealGapHalfLength
      (nativeHillPhysicalSource m q.val q.property.1).val
      (nativeHillPhysicalSource m q.val q.property.1).property.1
      (nativeHillPhysicalSource m q.val q.property.1).property.2 n = 0)
    (h : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (m : ℝ)))
    (f g : Curve ℂ) (hf : AbsolutelyContinuousOnInterval (extend f) 0 1)
    (hfg : deriv (extend f)=ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] extend g)
    (hfend : extend f 0=extend f 1) (hgend : extend g 0=extend g 1)
    (hg : ∀ j : ℤ, h.val.val j = unitCurveCoefficientsCLM g j) :
    (fderiv ℝ (D.nativeSourceHierarchyHamiltonian m) q) h =
      - ∑ n ∈ S, (D.originalHierarchyFrequency m r hrs
        (originalPositiveActions m r hrs (D.rawIntegerForwardHomeomorph m q)) n : ℂ)*
        hillPhysicalCurvePairing f (hillL2TracePeriodDirection (nativeHillPhysicalSource m q.val q.property.1).val
          (nativeHillPhysicalSource m q.val q.property.1).property.1
          (nativeHillPhysicalSource m q.val q.property.1).property.2 n) := by
  rw [D.nativeSourceHierarchyHamiltonian_fderiv_finite_gap m r hrs q S hq h,←Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro n _
  rw [D.nativeSourceActionSequence_weak_hamiltonian m r hrs q h n f g hf hfg hfend hgend hg]
  ring

end NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
