import NLS.ComplexAnalysis.ContinuousMapSuperposition
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-! # Analytic local inverses on compact trajectory spaces

If the original analytic derivative is invertible at every point of a
continuous path, its pointwise derivative is invertible on the whole
trajectory space. Continuity of operator inversion supplies a continuous
inverse path. The analytic inverse theorem then applies in the uniform norm.
-/
noncomputable section
open Set Filter Topology
open scoped ContDiff
namespace NLS.ComplexAnalysis
variable {K E F : Type} [TopologicalSpace K] [CompactSpace K]
variable [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- Pointwise invertibility gives invertibility of the derivative on complete trajectories. -/
theorem bijective_fderiv_superposition {f : E → F} {U : Set E}
    (hU : IsOpen U) (hf : AnalyticOnNhd ℂ f U) (g : C(K,E)) (hg : range g ⊆ U)
    (hi : ∀ k, (fderiv ℂ f (g k)).IsInvertible) :
    Function.Bijective (fderiv ℂ (superposition f) g) := by
  have hL : Continuous (fun k => fderiv ℂ f (g k)) :=
    hf.fderiv.continuousOn.comp_continuous g.continuous (fun k => hg ⟨k,rfl⟩)
  have hInv : Continuous (fun k => (fderiv ℂ f (g k)).inverse) := by
    apply continuous_iff_continuousAt.mpr
    intro k
    exact ((hi k).contDiffAt_map_inverse (n := 0)).continuousAt.comp
      (f := fun j : K => fderiv ℂ f (g j)) (hL.continuousAt (x := k))
  constructor
  · intro a b hab
    apply ContinuousMap.ext
    intro k
    have hh := congrArg (fun z : C(K,F) => z k) hab
    simp only [fderiv_superposition_apply hU hf g _ hg k] at hh
    obtain ⟨e,he⟩ := hi k
    rw [← he] at hh
    exact e.injective hh
  · intro v
    let b : C(K,E) := ⟨fun k => (fderiv ℂ f (g k)).inverse (v k),hInv.clm_apply v.continuous⟩
    refine ⟨b,?_⟩
    apply ContinuousMap.ext
    intro k
    rw [fderiv_superposition_apply hU hf g b hg k]
    change fderiv ℂ f (g k) ((fderiv ℂ f (g k)).inverse (v k)) = v k
    obtain ⟨e,he⟩ := hi k
    rw [← he,ContinuousLinearMap.inverse_equiv]
    exact e.apply_symm_apply _

/-- A path of invertible analytic derivatives gives an analytic local inverse in uniform norm. -/
theorem exists_analytic_superposition_inverse {f : E → F} {U : Set E}
    (hU : IsOpen U) (hf : AnalyticOnNhd ℂ f U) (g : C(K,E)) (hg : range g ⊆ U)
    (hi : ∀ k, (fderiv ℂ f (g k)).IsInvertible) :
    ∃ H : C(K,F) → C(K,E), AnalyticAt ℂ H (superposition f g) ∧
      H (superposition f g) = g ∧
      (∀ᶠ a in 𝓝 g, H (superposition f a) = a) ∧
      ∀ᶠ b in 𝓝 (superposition f g), superposition f (H b) = b := by
  have ha := analyticOnNhd_superposition hU hf g hg
  have hb := bijective_fderiv_superposition hU hf g hg hi
  let e : C(K,E) ≃L[ℂ] C(K,F) := ContinuousLinearEquiv.ofBijective
    (fderiv ℂ (superposition f) g) (LinearMap.ker_eq_bot.mpr hb.1) (LinearMap.range_eq_top.mpr hb.2)
  have hd : HasStrictFDerivAt (superposition f) e.toContinuousLinearMap g := by
    exact ha.contDiffAt.hasStrictFDerivAt (n := 1) one_ne_zero
  let M := hd.toOpenPartialHomeomorph (superposition f)
  have hM : (M : C(K,E) → C(K,F)) = superposition f := hd.toOpenPartialHomeomorph_coe
  have hsource : g ∈ M.source := hd.mem_toOpenPartialHomeomorph_source
  have hH : AnalyticAt ℂ M.symm (superposition f g) := by
    rw [← hM]
    exact M.analyticAt_symm' hsource (by rw [hM]; exact ha) (i := e) (by rw [hM]; exact hd.hasFDerivAt.fderiv)
  exact ⟨hd.localInverse _ _ _,hH,hd.localInverse_apply_image,
    hd.eventually_left_inverse,hd.eventually_right_inverse⟩

/-- A continuous real-parameter lift is analytic whenever its analytic image
passes through a path of invertible complex derivatives. -/
theorem analyticAt_real_lift_of_superposition
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {f : E → F} {U : Set E} (hU : IsOpen U) (hf : AnalyticOnNhd ℂ f U)
    (G : P → C(K,E)) (a : P) (hG : ContinuousAt G a) (hg : range (G a) ⊆ U)
    (hi : ∀ k, (fderiv ℂ f (G a k)).IsInvertible)
    (himage : AnalyticAt ℝ (fun x => superposition f (G x)) a) : AnalyticAt ℝ G a := by
  obtain ⟨H,hH,_,hl,_⟩ := exists_analytic_superposition_inverse hU hf (G a) hg hi
  have ha := (hH.restrictScalars (𝕜 := ℝ)).comp
    (f := fun x => superposition f (G x)) himage
  apply ha.congr
  exact hG.eventually hl

end NLS.ComplexAnalysis
