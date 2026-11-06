import NLS.ComplexAnalysis.ContinuousMapAnalyticInverse
import NLS.ComplexAnalysis.BoundaryAnalyticCoordinate

/-! # Analytic continuation of a compact family through a regular scalar coordinate

The inverse theorem in the uniform norm supplies one parameter neighborhood
for the entire compact family. It retains the given lift at the base parameter
and the exact coordinate equation at every point of the compact set.
-/
noncomputable section
set_option autoImplicit false
open Set Filter Topology Complex
namespace NLS.ComplexAnalysis
variable {K P : Type} [TopologicalSpace K] [CompactSpace K]
variable [NormedAddCommGroup P] [NormedSpace ℂ P]

/-- A nonzero scalar derivative is an invertible complex linear map. -/
theorem isInvertible_fderiv_of_deriv_ne_zero (φ : ℂ → ℂ) (z : ℂ)
    (hne : deriv φ z ≠ 0) : (fderiv ℂ φ z).IsInvertible := by
  have hb : Function.Bijective (fderiv ℂ φ z) := by
    constructor
    · intro a b h
      simp only [fderiv_eq_deriv_mul] at h
      exact mul_left_cancel₀ hne h
    · intro a
      refine ⟨a / deriv φ z, ?_⟩
      simp only [fderiv_eq_deriv_mul, mul_div_cancel₀ _ hne]
  let e := ContinuousLinearEquiv.ofBijective (fderiv ℂ φ z)
    (LinearMap.ker_eq_bot.mpr hb.1) (LinearMap.range_eq_top.mpr hb.2)
  exact ⟨e, rfl⟩

/-- One analytic parameter neighborhood for all points of a compact lift. -/
theorem exists_analytic_compact_coordinate_family
    (φ : ℂ → ℂ) (hφ : AnalyticOnNhd ℂ φ univ)
    (u : C(K,ℂ)) (hu : ∀ k, deriv φ (u k) ≠ 0)
    (D : P → C(K,ℂ)) (a : P) (hD : AnalyticAt ℂ D a)
    (hbase : ∀ k, D a k = φ (u k)) :
    ∃ V : Set P, IsOpen V ∧ a ∈ V ∧ ∃ H : P → C(K,ℂ),
      AnalyticOnNhd ℂ H V ∧ H a = u ∧
      ∀ b ∈ V, ∀ k, φ (H b k) = D b k ∧ deriv φ (H b k) ≠ 0 := by
  have hi : ∀ k, (fderiv ℂ φ (u k)).IsInvertible :=
    fun k => isInvertible_fderiv_of_deriv_ne_zero φ (u k) (hu k)
  obtain ⟨G,hG,hGu,_,hGr⟩ := exists_analytic_superposition_inverse isOpen_univ hφ u
    (subset_univ _) hi
  have hDa : D a = superposition φ u := by
    ext k
    rw [superposition_apply hφ.continuousOn (subset_univ _)]
    exact hbase k
  rw [← hDa] at hG hGu hGr
  let H : P → C(K,ℂ) := fun b => G (D b)
  have hH : AnalyticAt ℂ H a := hG.comp hD
  have hHa : H a = u := hGu
  have heq : ∀ᶠ b in 𝓝 a, ∀ k, φ (H b k) = D b k := by
    filter_upwards [hD.continuousAt.tendsto.eventually hGr] with b hb k
    have he := congrArg (fun f : C(K,ℂ) => f k) hb
    simpa only [superposition_apply hφ.continuousOn (subset_univ _)] using he
  let U : Set ℂ := {z | deriv φ z ≠ 0}
  have hU : IsOpen U := isOpen_ne_fun hφ.deriv.continuous continuous_const
  have huU : range u ⊆ U := by rintro _ ⟨k,rfl⟩; exact hu k
  have hnear : ∀ᶠ b in 𝓝 a, range (H b) ⊆ U :=
    hH.continuousAt.eventually ((ContinuousMap.isOpen_setOfPred_range_subset hU).mem_nhds
      (by rw [hHa]; exact huU))
  have hnearA : ∀ᶠ b in 𝓝 a, AnalyticAt ℂ H b :=
    (isOpen_analyticAt ℂ H).mem_nhds hH
  obtain ⟨V,hV,hVo,hVa⟩ := eventually_nhds_iff.mp (heq.and (hnear.and hnearA))
  refine ⟨V,hVo,hVa,H,fun b hb => (hV b hb).2.2,hHa,?_⟩
  intro b hb k
  exact ⟨(hV b hb).1 k,(hV b hb).2.1 ⟨k,rfl⟩⟩

/-- The inverse-coordinate criterion also applies to arbitrary normed domains. -/
theorem analyticAt_of_continuousAt_scalar_coordinate
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (φ : ℂ → ℂ) (H : E → ℂ) (x : E)
    (hφ : AnalyticAt ℂ φ (H x)) (hne : deriv φ (H x) ≠ 0)
    (hH : ContinuousAt H x) (hc : AnalyticAt ℂ (φ ∘ H) x) : AnalyticAt ℂ H x := by
  let r := hφ.hasStrictDerivAt.localInverse _ _ _ hne
  have hra : AnalyticAt ℂ r (φ (H x)) := hφ.analyticAt_localInverse hne
  have he : ∀ᶠ w in 𝓝 (H x), r (φ w) = w :=
    hφ.hasStrictDerivAt.eventually_left_inverse hne
  exact (hra.comp (f := φ ∘ H) hc).congr (hH.tendsto.eventually he)

end NLS.ComplexAnalysis
