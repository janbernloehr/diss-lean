import NLS.ComplexAnalysis.ConvexHolomorphicPrimitive

/-!
# Path integrals between primitive boundary values

An integrable C¹ path with interior in a primitive's domain has
integral equal to the difference of the relative boundary values
at its two ends. Thus paths with the same possibly singular ends
have the same integral.
-/

noncomputable section
open Set Filter Topology Complex
namespace NLS.ComplexAnalysis

theorem curveIntegral_eq_sub_of_primitive_boundary_ends
    (f F : ℂ → ℂ) (D : Set ℂ)
    (hF : ∀ z ∈ D, HasDerivAt F (f z) z)
    {a b : ℂ} (γ : Path a b)
    (hγ : ContDiffOn ℝ 1 γ.extend (Icc 0 1))
    (hγD : ∀ t ∈ Ioo (0:ℝ) 1, γ.extend t ∈ D)
    (hint : CurveIntegrable (holomorphicOneForm f) γ)
    {A B : ℂ}
    (ha : Tendsto F (𝓝[D] a) (𝓝 A))
    (hb : Tendsto F (𝓝[D] b) (𝓝 B)) :
    (∫ᶜ z in γ, holomorphicOneForm f z) = B-A := by
  have hstart : Tendsto γ.extend (𝓝[>] (0:ℝ)) (𝓝[D] a) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [Path.extend_zero] using
        (γ.continuous_extend.continuousAt (x := (0:ℝ))).tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ) < 1)] with t ht
      exact hγD t ht
  have hend : Tendsto γ.extend (𝓝[<] (1:ℝ)) (𝓝[D] b) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [Path.extend_one] using
        (γ.continuous_extend.continuousAt (x := (1:ℝ))).tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0:ℝ) < 1)] with t ht
      exact hγD t ht
  exact curveIntegral_eq_sub_of_primitive_with_limits f F D hF γ hγ hγD hint
    (ha.comp hstart) (hb.comp hend)

theorem curveIntegral_eq_of_primitive_boundary_ends
    (f F : ℂ → ℂ) (D : Set ℂ)
    (hF : ∀ z ∈ D, HasDerivAt F (f z) z)
    {a b : ℂ} (γ₁ γ₂ : Path a b)
    (hγ₁ : ContDiffOn ℝ 1 γ₁.extend (Icc 0 1))
    (hγ₂ : ContDiffOn ℝ 1 γ₂.extend (Icc 0 1))
    (hγ₁D : ∀ t ∈ Ioo (0:ℝ) 1, γ₁.extend t ∈ D)
    (hγ₂D : ∀ t ∈ Ioo (0:ℝ) 1, γ₂.extend t ∈ D)
    (hint₁ : CurveIntegrable (holomorphicOneForm f) γ₁)
    (hint₂ : CurveIntegrable (holomorphicOneForm f) γ₂)
    {A B : ℂ}
    (ha : Tendsto F (𝓝[D] a) (𝓝 A))
    (hb : Tendsto F (𝓝[D] b) (𝓝 B)) :
    (∫ᶜ z in γ₁, holomorphicOneForm f z) = ∫ᶜ z in γ₂, holomorphicOneForm f z := by
  rw [curveIntegral_eq_sub_of_primitive_boundary_ends f F D hF γ₁ hγ₁ hγ₁D hint₁ ha hb,
    curveIntegral_eq_sub_of_primitive_boundary_ends f F D hF γ₂ hγ₂ hγ₂D hint₂ ha hb]

end NLS.ComplexAnalysis
