import NLS.ComplexAnalysis.AnalyticOpenInverse
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-! # Real analytic inverse charts between different Banach spaces

An actual derivative equal to a bounded linear equivalence gives an
analytic inverse on explicit open neighborhoods in the two native spaces.
No identification of source and target normed types is required.
-/
noncomputable section
open Set Filter Topology
namespace NLS.ComplexAnalysis
theorem analyticAt_real_linear_transport
    {A B C D : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℂ B] [NormedAddCommGroup C] [NormedSpace ℂ C]
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    (J : A →L[ℝ] B) (L : C →L[ℝ] D) (f : B → C) (a : A)
    (hf : AnalyticAt ℂ f (J a)) : AnalyticAt ℝ (fun b => L (f (J b))) a :=
  (L.analyticAt _).comp (f := fun b => f (J b))
    ((hf.restrictScalars (𝕜 := ℝ)).comp (J.analyticAt a))

theorem hasFDerivAt_real_linear_transport
    {A B C D : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℂ B] [NormedAddCommGroup C] [NormedSpace ℂ C]
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    (J : A →L[ℝ] B) (L : C →L[ℝ] D) (f : B → C) (a : A)
    (hf : DifferentiableAt ℂ f (J a)) :
    HasFDerivAt (fun b => L (f (J b)))
      (L.comp (((fderiv ℂ f (J a)).restrictScalars ℝ).comp J)) a :=
  L.hasFDerivAt.comp a ((hf.hasFDerivAt.restrictScalars ℝ).comp a J.hasFDerivAt)

/-- A complex inverse germ agrees locally with a real inverse germ on
embedded real targets, and therefore preserves the prescribed source form. -/
theorem inverse_germ_preserves_subspace
    {A B R S : Type*} [TopologicalSpace A] [TopologicalSpace R] [TopologicalSpace S]
    (J : R → A) (hJ : Continuous J) (K : S → B) (f : A → B) (fR : R → S)
    (a : R) (g : B → A) (gR : S → R)
    (hc : ContinuousAt gR (fR a)) (hbase : gR (fR a) = a)
    (hl : ∀ᶠ b in 𝓝 (J a), g (f b) = b)
    (hr : ∀ᶠ z in 𝓝 (fR a), fR (gR z) = z)
    (hcomp : ∀ b, K (fR b) = f (J b))
    (P : A → Prop) (hP : ∀ b, P (J b)) :
    ∀ᶠ z in 𝓝 (fR a), P (g (K z)) := by
  have ht : Tendsto (fun z => J (gR z)) (𝓝 (fR a)) (𝓝 (J a)) := by
    have h := hJ.continuousAt.tendsto.comp hc.tendsto
    simpa only [Function.comp_def,hbase] using h
  filter_upwards [ht.eventually hl,hr] with z hz hzr
  have he := hcomp (gR z)
  rw [hzr] at he
  rw [he,hz]
  exact hP (gR z)

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- A genuine analytic local chart with the prescribed native Banach target. -/
theorem exists_real_analytic_openPartialHomeomorph_of_fderiv_equiv
    {f : E → F} {x : E} (hf : AnalyticAt ℝ f x) (L : E ≃L[ℝ] F)
    (hder : fderiv ℝ f x = L.toContinuousLinearMap) :
    ∃ P : OpenPartialHomeomorph E F, (P : E → F) = f ∧ x ∈ P.source ∧
      AnalyticOnNhd ℝ f P.source ∧ AnalyticOnNhd ℝ P.symm P.target := by
  have hs : HasStrictFDerivAt f L.toContinuousLinearMap x := by
    rw [← hder]
    exact hf.contDiffAt.hasStrictFDerivAt (n := 1) one_ne_zero
  let P := hs.toOpenPartialHomeomorph f
  have hP : (P : E → F) = f := hs.toOpenPartialHomeomorph_coe
  have hxP : x ∈ P.source := hs.mem_toOpenPartialHomeomorph_source
  have hG : AnalyticAt ℝ P.symm (f x) := by
    have h := P.analyticAt_symm' hxP (by rw [hP]; exact hf) (i := L) (by rw [hP]; exact hder)
    rwa [hP] at h
  let A := {a | AnalyticAt ℝ f a}
  let B := {b | AnalyticAt ℝ P.symm b}
  have hA : IsOpen A := isOpen_analyticAt ℝ f
  have hB : IsOpen B := isOpen_analyticAt ℝ P.symm
  let U := A ∩ (P.source ∩ P ⁻¹' B)
  have hU : IsOpen U := hA.inter (P.continuousOn.isOpen_inter_preimage P.open_source hB)
  let R := P.restrOpen U hU
  have hR : (R : E → F) = f := hP
  have hxR : x ∈ R.source := ⟨hxP,hf,hxP,by simpa only [mem_preimage,mem_ofPred_eq,B,hP] using hG⟩
  refine ⟨R,hR,hxR,fun a ha => ha.2.1,?_⟩
  intro b hb
  have hr : R.symm b ∈ R.source := R.map_target hb
  have hw : P (R.symm b) ∈ B := hr.2.2.2
  have he : P (R.symm b) = b := R.right_inv hb
  rw [he] at hw
  exact hw

end NLS.ComplexAnalysis
