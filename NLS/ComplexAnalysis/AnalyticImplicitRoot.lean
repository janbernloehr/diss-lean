import NLS.ComplexAnalysis.JointSpectralDerivative
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic

/-!
# Analytic dependence of a continuously selected simple zero

For a jointly analytic scalar equation on a complex Banach space, a
continuous choice of a simple zero is analytic. The proof applies the
analytic inverse function theorem to the triangular map
`(z, x) ↦ (F(z, x), x)`.
-/

noncomputable section
open Set Filter
open scoped Topology
namespace NLS.ComplexAnalysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
private theorem bijective_triangular_derivative
    (A : (ℂ × E) →L[ℂ] ℂ) (hα : A (1, 0) ≠ 0) :
    Function.Bijective (A.prod (ContinuousLinearMap.snd ℂ ℂ E)) := by
  let α : ℂ := A (1, 0)
  have hA (z : ℂ) (x : E) : A (z, x) = z * α + A (0, x) := by
    have hdecomp : (z, x) = z • (1, (0 : E)) + (0, x) := by
      ext <;> simp
    rw [hdecomp, map_add, map_smul]
    simp [α, smul_eq_mul]
  constructor
  · intro u v huv
    change (A u, u.2) = (A v, v.2) at huv
    have hx : u.2 = v.2 := (Prod.mk.inj huv).2
    have hz : A u = A v := (Prod.mk.inj huv).1
    have hzero : u.1 * α = v.1 * α := by
      rw [hA u.1 u.2, hA v.1 v.2, hx] at hz
      exact add_right_cancel hz
    have hz' : u.1 = v.1 := mul_right_cancel₀ hα hzero
    exact Prod.ext hz' hx
  · intro y
    let z : ℂ := (y.1 - A (0, y.2)) / α
    refine ⟨(z, y.2), ?_⟩
    apply Prod.ext
    · change A (z, y.2) = y.1
      rw [hA]
      dsimp [z, α]
      rw [div_mul_cancel₀ _ hα]
      exact sub_add_cancel _ _
    · rfl

/-- A continuous selection of simple zeros of a jointly analytic
equation is analytic at the base parameter. The simplicity condition
is the nonvanishing derivative in the spectral direction. -/
theorem analyticAt_implicitRoot
    (F : ℂ × E → ℂ) (a : E → ℂ) (x : E)
    (hF : AnalyticAt ℂ F (a x, x))
    (ha : ContinuousAt a x)
    (hroot : ∀ᶠ y in 𝓝 x, F (a y, y) = 0)
    (hsimple : (fderiv ℂ F (a x, x)) (1, 0) ≠ 0) :
    AnalyticAt ℂ a x := by
  let H : ℂ × E → ℂ × E := fun t => (F t, t.2)
  let A : (ℂ × E) →L[ℂ] ℂ := fderiv ℂ F (a x, x)
  let T : (ℂ × E) →L[ℂ] (ℂ × E) :=
    A.prod (ContinuousLinearMap.snd ℂ ℂ E)
  have hH : AnalyticAt ℂ H (a x, x) := hF.prod analyticAt_snd
  have hTH : HasStrictFDerivAt H T (a x, x) := by
    have hderiv : fderiv ℂ H (a x, x) = T := by
      simpa only [H, T, A, fderiv_snd] using
        (hF.differentiableAt.fderiv_prodMk differentiableAt_snd)
    rw [← hderiv]
    exact hH.hasStrictFDerivAt
  have hbij : Function.Bijective T :=
    bijective_triangular_derivative A hsimple
  let i : (ℂ × E) ≃L[ℂ] (ℂ × E) :=
    ContinuousLinearEquiv.ofBijective T
      (LinearMap.ker_eq_bot.mpr hbij.1)
      (LinearMap.range_eq_top.mpr hbij.2)
  have hTHi : HasStrictFDerivAt H (i : (ℂ × E) →L[ℂ] (ℂ × E)) (a x, x) := by
    simpa only [i, ContinuousLinearEquiv.coe_ofBijective] using hTH
  let R : OpenPartialHomeomorph (ℂ × E) (ℂ × E) :=
    hTHi.toOpenPartialHomeomorph H
  have hReq : (R : ℂ × E → ℂ × E) = H :=
    hTHi.toOpenPartialHomeomorph_coe
  have hR : AnalyticAt ℂ R.symm (H (a x, x)) := by
    apply R.analyticAt_symm' (i := i)
      (hTHi.mem_toOpenPartialHomeomorph_source)
    · rw [hReq]
      exact hH
    · rw [hReq]
      exact hTHi.hasFDerivAt.fderiv
  have hmap : AnalyticAt ℂ (fun y : E => ((0:ℂ), y)) x :=
    analyticAt_const.prod analyticAt_id
  have hsection : AnalyticAt ℂ
      (fun y : E => (R.symm ((0:ℂ), y)).1) x := by
    have hHx : H (a x, x) = (0, x) := by
      simp [H, hroot.self_of_nhds]
    rw [hHx] at hR
    exact ((analyticAt_fst (𝕜 := ℂ) (p := R.symm (0, x))).comp hR).comp hmap
  have hcont : ContinuousAt (fun y : E => (a y, y)) x :=
    ha.prodMk continuousAt_id
  have hmem : ∀ᶠ y : E in 𝓝 x, (a y, y) ∈ R.source :=
    hcont.eventually (R.open_source.mem_nhds hTHi.mem_toOpenPartialHomeomorph_source)
  have heq : (fun y : E => (R.symm (0, y)).1) =ᶠ[𝓝 x] a := by
    filter_upwards [hroot, hmem] with y hy hysrc
    have hHy : H (a y, y) = (0, y) := by simp [H, hy]
    rw [← hHy, ← hReq, R.left_inv hysrc]
  exact hsection.congr heq

end NLS.ComplexAnalysis
