import NLS.MKdV.MiuraCartesianPlaneGardner
import NLS.MKdV.MiuraCartesianFreeDifferential
import NLS.ComplexAnalysis.AnalyticProductCancellation

/-! # The actual canonical bracket in each Cartesian plane

The coordinate X_n is not identically zero on the physical real H1
space, as detected by its actual free Fourier differential. Analytic
continuation cancels this factor in the radial bracket identity and
extends the value one through every collapsed selected gap.
Cross-mode Cartesian brackets remain a separate obligation.
-/
noncomputable section
open Set Complex NLS.Poisson NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

theorem exists_physicalH1_miuraCartesianX_ne_zero (m : ℕ) (hm : 1 ≤ m) :
    ∃ a : WeightedCoeff.physicalRealSubmodule (Weight.sobolev 1) 2,
      miuraCartesianX m (scalarInclusion a.val) ≠ 0 := by
  let V := WeightedCoeff.physicalRealSubmodule (Weight.sobolev 1) 2
  have hw : ∀ k : ℤ, Weight.sobolev 1 (-k) = Weight.sobolev 1 k := by intro k; simp
  have hspan (h : ScalarDomain 2) : ∃ x y : V, h = x.val+I • y.val :=
    ⟨WeightedCoeff.physicalRealPart (Weight.sobolev 1) hw h,
      WeightedCoeff.physicalRealPart (Weight.sobolev 1) hw ((-I) • h),
        WeightedCoeff.physicalRealPart_complex_decomp _ hw h⟩
  by_contra hzero
  push Not at hzero
  have hrealzero : ∀ a : V, miuraCartesianX m (scalarInclusion a.val) = 0 := hzero
  have hzeroReal : ∀ j : ℤ, (0 : Coeff 2) j = conj ((0 : Coeff 2) (-j)) := by intro j; simp
  have hf := analyticAt_miuraL2CartesianCoordinates 0 hzeroReal m hm
  have hx : AnalyticAt ℂ (miuraCartesianX m) 0 := analyticAt_fst.comp hf
  have hz := NLS.ComplexAnalysis.fderiv_comp_eq_zero_of_real_zero V hspan scalarInclusion
    (miuraCartesianX m) hx.differentiableAt hrealzero
  have he := congrArg (fun L : ScalarDomain 2 →L[ℂ] ℂ => L (scalarMode m 1)) hz
  have hd := ((ContinuousLinearMap.fst ℂ ℂ ℂ).hasFDerivAt.comp 0 hf.differentiableAt.hasFDerivAt).fderiv
  change fderiv ℂ (miuraCartesianX m) 0 = _ at hd
  change (fderiv ℂ (miuraCartesianX m) 0) (scalarInclusion (scalarMode m 1)) = 0 at he
  rw [hd,scalarInclusion_scalarMode] at he
  change ((fderiv ℂ (miuraL2CartesianCoordinates m) 0) (lp.single 2 (m : ℤ) 1)).1 = 0 at he
  rw [fderiv_miuraL2CartesianCoordinates_zero_explicit m hm] at he
  have hneg : -(m : ℤ) ≠ (m : ℤ) := by omega
  have hbad : (Real.sqrt ((2*Real.pi*(m : ℝ))⁻¹) : ℂ)*(-1/(Real.sqrt 2 : ℂ)) = 0 := by
    simpa only [lp.single_apply,Pi.single_apply,if_neg hneg,ite_true,zero_add,neg_mul,
      neg_add_rev] using he
  have hmp : 0 < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hr : (Real.sqrt ((2*Real.pi*(m : ℝ))⁻¹) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (by positivity)))
  have hs : (Real.sqrt 2 : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (by norm_num)))
  exact (mul_ne_zero hr (div_ne_zero (by norm_num) hs)) hbad

theorem miuraCartesianPlaneBracket_eq_one (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (m : ℕ) (hm : 1 ≤ m) :
    miuraCartesianPlaneBracket m a = 1 := by
  let V := WeightedCoeff.physicalRealSubmodule (Weight.sobolev 1) 2
  let f : V → ℂ := fun b => miuraCartesianX m (scalarInclusion b.val)
  let g : V → ℂ := fun b => miuraCartesianPlaneBracket m b.val-1
  have hg : AnalyticOnNhd ℝ g univ := by
    intro b _
    have hc : AnalyticAt ℂ (miuraCartesianPlaneBracket m) b.val :=
      analyticAt_miuraCartesianGardnerBracketExtension b.val b.property m m hm hm _ _
    exact ((hc.restrictScalars (𝕜 := ℝ)).comp (V.subtypeL.analyticAt b)).sub analyticAt_const
  have hfg (b : V) : f b*g b = 0 := miuraCartesianPlaneBracket_error_mul_X b.val b.property m hm
  obtain ⟨b,hb⟩ := exists_physicalH1_miuraCartesianX_ne_zero m hm
  have har : ∀ j, scalarInclusion b.val j = conj (scalarInclusion b.val (-j)) := by
    intro j
    simpa only [scalarInclusion_apply] using b.property j
  have hc : AnalyticAt ℂ (fun u : ScalarDomain 2 => miuraCartesianX m (scalarInclusion u)) b.val :=
    (analyticAt_fst.comp (analyticAt_miuraL2CartesianCoordinates _ har m hm)).comp (scalarInclusion.analyticAt b.val)
  have hfc : ContinuousAt f b :=
    (((hc.restrictScalars (𝕜 := ℝ)).comp (V.subtypeL.analyticAt b))).continuousAt
  have he := NLS.ComplexAnalysis.eq_zero_of_analytic_mul_eq_zero f g hg hfg b hfc hb ⟨a,ha⟩
  exact sub_eq_zero.mp he

/-- The literal scalar Gardner bracket of the actual Cartesian pair is
one at every original real H1 source, including a closed selected gap. -/
theorem miuraCartesianPlane_Gardner_canonical (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (m : ℕ) (hm : 1 ≤ m) :
    l2GardnerBracket (miuraCartesianX m) (miuraCartesianY m) (scalarInclusion a) = 1 := by
  rw [← miuraCartesianPlaneBracket_eq_actual a ha m hm]
  exact miuraCartesianPlaneBracket_eq_one a ha m hm

end NLS.MKdV
