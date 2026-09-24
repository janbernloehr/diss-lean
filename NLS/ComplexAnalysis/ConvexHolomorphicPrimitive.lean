import NLS.ComplexAnalysis.ConvexHolomorphicPathIntegral
import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare

/-!
# Primitive evaluation of holomorphic path integrals

A holomorphic function on an open convex domain has a primitive.
For a smooth path inside the domain, its curve integral is the
primitive's endpoint difference. This also applies piece by piece
when concatenations have corners.
-/

noncomputable section
open Set Filter Topology MeasureTheory Complex
open scoped unitInterval
namespace NLS.ComplexAnalysis

/-- Evaluate a holomorphic one-form integral using a primitive along
a `C¹` path whose image stays in the primitive's domain. -/
theorem curveIntegral_eq_sub_of_primitive
    (f F : ℂ → ℂ) (s : Set ℂ)
    (hF : ∀ z ∈ s, HasDerivAt F (f z) z)
    {a b : ℂ} (γ : Path a b)
    (hγ : ContDiffOn ℝ 1 γ.extend (Icc 0 1))
    (hγs : ∀ t ∈ Icc (0:ℝ) 1, γ.extend t ∈ s)
    (hint : CurveIntegrable (holomorphicOneForm f) γ) :
    (∫ᶜ z in γ, holomorphicOneForm f z) = F b - F a := by
  have hFcont : ContinuousOn F s := fun z hz =>
    (hF z hz).continuousAt.continuousWithinAt
  have hcomp : ContinuousOn (F ∘ γ.extend) (Icc (0:ℝ) 1) :=
    hFcont.comp hγ.continuousOn hγs
  have hderiv (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) :
      HasDerivAt (F ∘ γ.extend)
        (f (γ.extend t) * deriv γ.extend t) t := by
    have hγdiff : DifferentiableAt ℝ γ.extend t :=
      (hγ.differentiableOn (by norm_num) t (Ioo_subset_Icc_self ht)).differentiableAt
        (Filter.mem_of_superset (Ioo_mem_nhds ht.1 ht.2) Ioo_subset_Icc_self)
    simpa only [smul_eq_mul, mul_comm] using
      (hF (γ.extend t) (hγs t (Ioo_subset_Icc_self ht))).scomp t
        hγdiff.hasDerivAt
  have heq : EqOn (curveIntegralFun (holomorphicOneForm f) γ)
      (fun t : ℝ => f (γ.extend t) * deriv γ.extend t)
      (Ioo (0:ℝ) 1) := by
    intro t ht
    rw [curveIntegralFun_def]
    have htnhds : I ∈ 𝓝 t :=
      Filter.mem_of_superset (Ioo_mem_nhds ht.1 ht.2) Ioo_subset_Icc_self
    rw [derivWithin_of_mem_nhds htnhds]
    rfl
  have hint' : IntervalIntegrable
      (fun t : ℝ => f (γ.extend t) * deriv γ.extend t)
      volume 0 1 := hint.congr_uIoo (by simpa only [uIoo_of_le zero_le_one] using heq)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    zero_le_one hcomp hderiv hint'
  rw [curveIntegral_eq_intervalIntegral_deriv]
  convert hFTC using 1 <;> simp

/-- Holomorphic functions on an open convex complex domain have a
primitive with the prescribed complex derivative. -/
theorem exists_primitive_on_convex
    (f : ℂ → ℂ) (s : Set ℂ) (hconv : Convex ℝ s) (hopen : IsOpen s)
    (hf : DifferentiableOn ℂ f s) :
    ∃ F : ℂ → ℂ, ∀ z ∈ s, HasDerivAt F (f z) z := by
  obtain ⟨F,hF⟩ := hconv.exists_forall_hasDerivWithinAt hf
  exact ⟨F,fun z hz => (hF z hz).hasDerivAt (hopen.mem_nhds hz)⟩

/-- A holomorphic one-form on an open convex domain is path independent
for `C¹` paths, assuming their curve integrals are defined. -/
theorem curveIntegral_eq_of_convex_paths_one
    (f : ℂ → ℂ) (s : Set ℂ) (hconv : Convex ℝ s)
    (hopen : IsOpen s) (hf : DifferentiableOn ℂ f s)
    {a b : ℂ} (γ₁ γ₂ : Path a b)
    (hγ₁ : ContDiffOn ℝ 1 γ₁.extend (Icc 0 1))
    (hγ₂ : ContDiffOn ℝ 1 γ₂.extend (Icc 0 1))
    (hγ₁s : ∀ t ∈ Icc (0:ℝ) 1, γ₁.extend t ∈ s)
    (hγ₂s : ∀ t ∈ Icc (0:ℝ) 1, γ₂.extend t ∈ s)
    (hγ₁int : CurveIntegrable (holomorphicOneForm f) γ₁)
    (hγ₂int : CurveIntegrable (holomorphicOneForm f) γ₂) :
    (∫ᶜ z in γ₁, holomorphicOneForm f z) =
      ∫ᶜ z in γ₂, holomorphicOneForm f z := by
  obtain ⟨F,hF⟩ := exists_primitive_on_convex f s hconv hopen hf
  rw [curveIntegral_eq_sub_of_primitive f F s hF γ₁ hγ₁ hγ₁s hγ₁int,
    curveIntegral_eq_sub_of_primitive f F s hF γ₂ hγ₂ hγ₂s hγ₂int]

/-- Primitive evaluation makes curve integrals additive across a
corner, even though the concatenated path need not be globally `C¹`. -/
theorem curveIntegral_add_eq_of_primitive
    (f F : ℂ → ℂ) (s : Set ℂ)
    (hF : ∀ z ∈ s, HasDerivAt F (f z) z)
    {a b c : ℂ} (γ₁ : Path a b) (γ₂ : Path b c) (γ : Path a c)
    (hγ₁ : ContDiffOn ℝ 1 γ₁.extend (Icc 0 1))
    (hγ₂ : ContDiffOn ℝ 1 γ₂.extend (Icc 0 1))
    (hγ : ContDiffOn ℝ 1 γ.extend (Icc 0 1))
    (hγ₁s : ∀ t ∈ Icc (0:ℝ) 1, γ₁.extend t ∈ s)
    (hγ₂s : ∀ t ∈ Icc (0:ℝ) 1, γ₂.extend t ∈ s)
    (hγs : ∀ t ∈ Icc (0:ℝ) 1, γ.extend t ∈ s)
    (hγ₁int : CurveIntegrable (holomorphicOneForm f) γ₁)
    (hγ₂int : CurveIntegrable (holomorphicOneForm f) γ₂)
    (hγint : CurveIntegrable (holomorphicOneForm f) γ) :
    (∫ᶜ z in γ₁, holomorphicOneForm f z) +
      (∫ᶜ z in γ₂, holomorphicOneForm f z) =
        ∫ᶜ z in γ, holomorphicOneForm f z := by
  rw [curveIntegral_eq_sub_of_primitive f F s hF γ₁ hγ₁ hγ₁s hγ₁int,
    curveIntegral_eq_sub_of_primitive f F s hF γ₂ hγ₂ hγ₂s hγ₂int,
    curveIntegral_eq_sub_of_primitive f F s hF γ hγ hγs hγint]
  ring

end NLS.ComplexAnalysis
