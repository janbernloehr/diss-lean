import NLS.Poisson.SobolevSourceCompatibility
import Mathlib.Analysis.Calculus.FDeriv.Equiv

/-! # The full bracket algebra in order-zero signed Hilbert coordinates

The single-domain bracket below uses the recovered full Sobolev gradients.
Its exact equivalence with the physical source bracket transfers Jacobi.
This concerns order zero and exponent two; no claim of closure on arbitrary
reciprocal Sobolev intersections is made.
-/
noncomputable section
open scoped ENNReal
namespace NLS.Poisson

/-- Identify the syntactic orders -0 and 0 while keeping the signed coefficients. -/
def zeroOrderNormalization :
    WeightedCoeffPair (Weight.sobolev (-0)) 2 ≃L[ℂ] WeightedCoeffPair (Weight.sobolev 0) 2 :=
  (zeroOrderPhysicalEquiv (-0) neg_zero 2).trans (zeroOrderPhysicalEquiv 0 rfl 2).symm

/-- The full-gradient bivector on one order-zero signed Hilbert domain. -/
def zeroOrderBivector :
    (WeightedCoeffPair (Weight.sobolev 0) 2 →L[ℂ] ℂ) →L[ℂ]
      (WeightedCoeffPair (Weight.sobolev 0) 2 →L[ℂ] ℂ) →L[ℂ] ℂ :=
  (conjugateBivector (p := 2) (q := 2) 0 (by norm_num) (by norm_num)).bilinearComp
    ((ContinuousLinearMap.compL ℂ _ _ ℂ).flip zeroOrderNormalization.toContinuousLinearMap)
    (ContinuousLinearMap.id ℂ _)

@[simp] theorem zeroOrderBivector_apply (L M : WeightedCoeffPair (Weight.sobolev 0) 2 →L[ℂ] ℂ) :
    zeroOrderBivector L M = conjugateBivector 0 (by norm_num) (by norm_num)
      (L.comp zeroOrderNormalization.toContinuousLinearMap) M := rfl

theorem zeroOrderBivector_source (L M : WeightedCoeffPair (Weight.sobolev 0) 2 →L[ℂ] ℂ) :
    zeroOrderBivector L M = sourceBivector (p := 2) le_rfl
      (L.comp (zeroOrderPhysicalEquiv 0 rfl 2).symm.toContinuousLinearMap)
      (M.comp (zeroOrderPhysicalEquiv 0 rfl 2).symm.toContinuousLinearMap) := by
  have h := conjugateBivector_zero_source
    (L.comp (zeroOrderPhysicalEquiv 0 rfl 2).symm.toContinuousLinearMap)
    (M.comp (zeroOrderPhysicalEquiv 0 rfl 2).symm.toContinuousLinearMap)
  have hm : (M.comp (zeroOrderPhysicalEquiv 0 rfl 2).symm.toContinuousLinearMap).comp
      (zeroOrderPhysicalEquiv 0 rfl 2).toContinuousLinearMap = M := by
    rw [ContinuousLinearMap.comp_assoc,ContinuousLinearEquiv.coe_symm_comp_coe,
      ContinuousLinearMap.comp_id]
  have hl : (L.comp (zeroOrderPhysicalEquiv 0 rfl 2).symm.toContinuousLinearMap).comp
      (zeroOrderPhysicalEquiv (-0) neg_zero 2).toContinuousLinearMap =
        L.comp zeroOrderNormalization.toContinuousLinearMap := by
    rw [ContinuousLinearMap.comp_assoc,ContinuousLinearEquiv.comp_coe]
    rfl
  rw [hm,hl] at h
  rw [zeroOrderBivector_apply]
  exact h

/-- The actual full-gradient Sobolev bracket on a single Banach domain. -/
def zeroOrderBracket (F G : WeightedCoeffPair (Weight.sobolev 0) 2 → ℂ)
    (x : WeightedCoeffPair (Weight.sobolev 0) 2) : ℂ :=
  zeroOrderBivector (fderiv ℂ F x) (fderiv ℂ G x)

/-- Coordinate equivalence holds for the actual derivatives, even without differentiability. -/
theorem zeroOrderBracket_source (F G : WeightedCoeffPair (Weight.sobolev 0) 2 → ℂ)
    (x : WeightedCoeffPair (Weight.sobolev 0) 2) :
    zeroOrderBracket F G x = sourceBracket (p := 2) le_rfl
      (F ∘ (zeroOrderPhysicalEquiv 0 rfl 2).symm)
      (G ∘ (zeroOrderPhysicalEquiv 0 rfl 2).symm) (zeroOrderPhysicalEquiv 0 rfl 2 x) := by
  rw [zeroOrderBracket,zeroOrderBivector_source,sourceBracket,
    ContinuousLinearEquiv.comp_right_fderiv,ContinuousLinearEquiv.comp_right_fderiv]
  simp only [ContinuousLinearEquiv.symm_apply_apply]

/-- Every common-state representative recovers this same single-domain bracket. -/
theorem commonSobolevBracket_zeroOrderBracket
    (F G : WeightedCoeffPair (Weight.sobolev 0) 2 → ℂ) (x : SobolevCommonState 0 2 2) :
    commonSobolevBracket 0 (by norm_num) (by norm_num) (F ∘ zeroOrderNormalization) G x =
      zeroOrderBracket F G x.val.2 := by
  have hx := zeroOrderSourceMap_common (r := 2) le_rfl le_rfl x
  change zeroOrderPhysicalEquiv (-0) neg_zero 2 x.val.1 =
    zeroOrderPhysicalEquiv 0 rfl 2 x.val.2 at hx
  have hn : zeroOrderNormalization x.val.1 = x.val.2 := by
    change (zeroOrderPhysicalEquiv 0 rfl 2).symm
      (zeroOrderPhysicalEquiv (-0) neg_zero 2 x.val.1) = _
    rw [hx,ContinuousLinearEquiv.symm_apply_apply]
  rw [commonSobolevBracket,ContinuousLinearEquiv.comp_right_fderiv,hn]
  rfl

theorem zeroOrderBracket_antisymm (F G : WeightedCoeffPair (Weight.sobolev 0) 2 → ℂ)
    (x : WeightedCoeffPair (Weight.sobolev 0) 2) :
    zeroOrderBracket F G x = -zeroOrderBracket G F x := by
  rw [zeroOrderBracket_source,zeroOrderBracket_source]
  exact sourceBracket_antisymm _ _ _ _

theorem analyticOnNhd_zeroOrderBracket
    (F G : WeightedCoeffPair (Weight.sobolev 0) 2 → ℂ) {U : Set (WeightedCoeffPair (Weight.sobolev 0) 2)}
    (hF : AnalyticOnNhd ℂ F U) (hG : AnalyticOnNhd ℂ G U) :
    AnalyticOnNhd ℂ (zeroOrderBracket F G) U := by
  intro x hx
  exact (zeroOrderBivector.analyticAt_bilinear _).comp₂ (hF.fderiv x hx) (hG.fderiv x hx)

/-- The Jacobi identity for the full-gradient signed Sobolev bracket on the Hilbert overlap. -/
theorem zeroOrderBracket_jacobi (F G H : WeightedCoeffPair (Weight.sobolev 0) 2 → ℂ)
    (x : WeightedCoeffPair (Weight.sobolev 0) 2)
    (hF : AnalyticAt ℂ F x) (hG : AnalyticAt ℂ G x) (hH : AnalyticAt ℂ H x) :
    zeroOrderBracket (zeroOrderBracket F G) H x +
      zeroOrderBracket (zeroOrderBracket G H) F x +
      zeroOrderBracket (zeroOrderBracket H F) G x = 0 := by
  let e := zeroOrderPhysicalEquiv 0 rfl 2
  have hb (A B : WeightedCoeffPair (Weight.sobolev 0) 2 → ℂ) :
      zeroOrderBracket A B ∘ e.symm = sourceBracket (p := 2) le_rfl (A ∘ e.symm) (B ∘ e.symm) := by
    funext y
    simpa only [e,Function.comp_apply,ContinuousLinearEquiv.apply_symm_apply] using
      zeroOrderBracket_source A B (e.symm y)
  simp only [zeroOrderBracket_source]
  change sourceBracket (p := 2) le_rfl (zeroOrderBracket F G ∘ e.symm) (H ∘ e.symm) (e x) +
    sourceBracket (p := 2) le_rfl (zeroOrderBracket G H ∘ e.symm) (F ∘ e.symm) (e x) +
    sourceBracket (p := 2) le_rfl (zeroOrderBracket H F ∘ e.symm) (G ∘ e.symm) (e x) = 0
  rw [hb,hb,hb]
  apply sourceBracket_jacobi
  · simpa only [ContinuousLinearEquiv.symm_apply_apply] using
      (show AnalyticAt ℂ F (e.symm (e x)) by simpa using hF).comp (f := e.symm) (x := e x) (e.symm.analyticAt (e x))
  · simpa only [ContinuousLinearEquiv.symm_apply_apply] using
      (show AnalyticAt ℂ G (e.symm (e x)) by simpa using hG).comp (f := e.symm) (x := e x) (e.symm.analyticAt (e x))
  · simpa only [ContinuousLinearEquiv.symm_apply_apply] using
      (show AnalyticAt ℂ H (e.symm (e x)) by simpa using hH).comp (f := e.symm) (x := e x) (e.symm.analyticAt (e x))

/-- Left Leibniz rule for the same single-domain full-gradient bracket. -/
theorem zeroOrderBracket_mul_left (F H G : WeightedCoeffPair (Weight.sobolev 0) 2 → ℂ)
    (x : WeightedCoeffPair (Weight.sobolev 0) 2)
    (hF : DifferentiableAt ℂ F x) (hH : DifferentiableAt ℂ H x) :
    zeroOrderBracket (fun y => F y*H y) G x =
      F x*zeroOrderBracket H G x + H x*zeroOrderBracket F G x := by
  rw [zeroOrderBracket,fderiv_fun_mul hF hH]
  simp only [map_add,map_smul,add_apply,smul_apply,smul_eq_mul]
  rfl

theorem zeroOrderBracket_mul_right (F G H : WeightedCoeffPair (Weight.sobolev 0) 2 → ℂ)
    (x : WeightedCoeffPair (Weight.sobolev 0) 2)
    (hG : DifferentiableAt ℂ G x) (hH : DifferentiableAt ℂ H x) :
    zeroOrderBracket F (fun y => G y*H y) x =
      G x*zeroOrderBracket F H x + H x*zeroOrderBracket F G x := by
  rw [zeroOrderBracket,fderiv_fun_mul hG hH]
  simp only [map_add,map_smul,smul_eq_mul]
  rfl

theorem zeroOrderBracket_add_left (F H G : WeightedCoeffPair (Weight.sobolev 0) 2 → ℂ)
    (x : WeightedCoeffPair (Weight.sobolev 0) 2)
    (hF : DifferentiableAt ℂ F x) (hH : DifferentiableAt ℂ H x) :
    zeroOrderBracket (fun y => F y+H y) G x =
      zeroOrderBracket F G x + zeroOrderBracket H G x := by
  rw [zeroOrderBracket,fderiv_fun_add hF hH]
  simp only [map_add,add_apply]
  rfl

theorem zeroOrderBracket_smul_left (F G : WeightedCoeffPair (Weight.sobolev 0) 2 → ℂ)
    (c : ℂ) (x : WeightedCoeffPair (Weight.sobolev 0) 2) :
    zeroOrderBracket (fun y => c*F y) G x = c*zeroOrderBracket F G x := by
  rw [zeroOrderBracket]
  change zeroOrderBivector (fderiv ℂ (c • F) x) (fderiv ℂ G x) = _
  rw [fderiv_const_smul_field]
  change zeroOrderBivector (c • fderiv ℂ F x) (fderiv ℂ G x) = _
  simp only [map_smul,smul_apply,smul_eq_mul]
  rfl

end NLS.Poisson
