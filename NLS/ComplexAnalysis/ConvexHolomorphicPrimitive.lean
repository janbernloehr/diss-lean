import NLS.ComplexAnalysis.ConvexHolomorphicPathIntegral
import NLS.ComplexAnalysis.IntegrableDerivativeBoundary
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

/-- Evaluate an integrable path with a singular starting endpoint by
taking the one-sided limits of a primitive along the path. No
derivative or domain condition is imposed at either endpoint. -/
theorem curveIntegral_eq_sub_of_primitive_with_limits
    (f F : ℂ → ℂ) (s : Set ℂ)
    (hF : ∀ z ∈ s, HasDerivAt F (f z) z)
    {a b : ℂ} (γ : Path a b)
    (hγ : ContDiffOn ℝ 1 γ.extend (Icc 0 1))
    (hγs : ∀ t ∈ Ioo (0:ℝ) 1, γ.extend t ∈ s)
    (hint : CurveIntegrable (holomorphicOneForm f) γ)
    {A B : ℂ}
    (hstart : Tendsto (F ∘ γ.extend) (𝓝[>] (0:ℝ)) (𝓝 A))
    (hend : Tendsto (F ∘ γ.extend) (𝓝[<] (1:ℝ)) (𝓝 B)) :
    (∫ᶜ z in γ, holomorphicOneForm f z) = B - A := by
  have hderiv (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) :
      HasDerivAt (F ∘ γ.extend)
        (f (γ.extend t) * deriv γ.extend t) t := by
    have hγdiff : DifferentiableAt ℝ γ.extend t :=
      (hγ.differentiableOn (by norm_num) t (Ioo_subset_Icc_self ht)).differentiableAt
        (Filter.mem_of_superset (Ioo_mem_nhds ht.1 ht.2) Ioo_subset_Icc_self)
    simpa only [smul_eq_mul, mul_comm] using
      (hF (γ.extend t) (hγs t ht)).scomp t hγdiff.hasDerivAt
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
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto
    (by norm_num : (0:ℝ) < 1) hderiv hint' hstart hend
  rw [curveIntegral_eq_intervalIntegral_deriv]
  convert hFTC using 1; simp

/-- A smooth integrable path between two boundary points has zero
one-form integral if the primitive approaches the same value at both
ends from within the domain. -/
theorem curveIntegral_eq_zero_of_primitive_boundary_ends
    (f F : ℂ → ℂ) (s : Set ℂ)
    (hF : ∀ z ∈ s, HasDerivAt F (f z) z)
    {a b : ℂ} (γ : Path a b)
    (hγ : ContDiffOn ℝ 1 γ.extend (Icc 0 1))
    (hγs : ∀ t ∈ Ioo (0:ℝ) 1, γ.extend t ∈ s)
    (hint : CurveIntegrable (holomorphicOneForm f) γ)
    {A : ℂ}
    (ha : Tendsto F (𝓝[s] a) (𝓝 A))
    (hb : Tendsto F (𝓝[s] b) (𝓝 A)) :
    (∫ᶜ z in γ, holomorphicOneForm f z) = 0 := by
  have hγstart : Tendsto γ.extend (𝓝[>] (0:ℝ)) (𝓝[s] a) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hγ0 : ContinuousAt γ.extend (0:ℝ) := γ.continuous_extend.continuousAt
      have hγ0' : Tendsto γ.extend (𝓝[>] (0:ℝ)) (𝓝 (γ.extend 0)) :=
        hγ0.tendsto.mono_left nhdsWithin_le_nhds
      simpa only [Path.extend_zero] using hγ0'
    · filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ) < 1)] with t ht
      exact hγs t ht
  have hγend : Tendsto γ.extend (𝓝[<] (1:ℝ)) (𝓝[s] b) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hγ1 : ContinuousAt γ.extend (1:ℝ) := γ.continuous_extend.continuousAt
      have hγ1' : Tendsto γ.extend (𝓝[<] (1:ℝ)) (𝓝 (γ.extend 1)) :=
        hγ1.tendsto.mono_left nhdsWithin_le_nhds
      simpa only [Path.extend_one] using hγ1'
    · filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0:ℝ) < 1)] with t ht
      exact hγs t ht
  have hstart : Tendsto (F ∘ γ.extend) (𝓝[>] (0:ℝ)) (𝓝 A) :=
    ha.comp hγstart
  have hend : Tendsto (F ∘ γ.extend) (𝓝[<] (1:ℝ)) (𝓝 A) :=
    hb.comp hγend
  rw [curveIntegral_eq_sub_of_primitive_with_limits
    f F s hF γ hγ hγs hint hstart hend,sub_self]

/-- An integrable singular connector inside the primitive's domain
determines a finite primitive limit along its parameter. Its integral
is the regular endpoint value minus that limit. -/
theorem exists_primitive_limit_along_integrable_path
    (f F : ℂ → ℂ) (s : Set ℂ)
    (hF : ∀ z ∈ s, HasDerivAt F (f z) z)
    {a b : ℂ} (γ : Path a b)
    (hγ : ContDiffOn ℝ 1 γ.extend (Icc 0 1))
    (hγs : ∀ t ∈ Ioo (0:ℝ) 1, γ.extend t ∈ s)
    (hb : b ∈ s)
    (hint : CurveIntegrable (holomorphicOneForm f) γ) :
    ∃ A : ℂ,
      Tendsto (F ∘ γ.extend) (𝓝[>] (0:ℝ)) (𝓝 A) ∧
      (∀ t ∈ Ioo (0:ℝ) (1/2),
        F (γ.extend t) = A +
          ∫ u in Ioc (0:ℝ) t,
            curveIntegralFun (holomorphicOneForm f) γ u) ∧
      (∫ᶜ z in γ, holomorphicOneForm f z) = F b - A := by
  let g : ℝ → ℂ := F ∘ γ.extend
  let q : ℝ → ℂ := curveIntegralFun (holomorphicOneForm f) γ
  have hq : IntegrableOn q (Ioo (0:ℝ) 1) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp hint
  have hg (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) : HasDerivAt g (q t) t := by
    have hγdiff : DifferentiableAt ℝ γ.extend t :=
      (hγ.differentiableOn (by norm_num) t (Ioo_subset_Icc_self ht)).differentiableAt
        (Filter.mem_of_superset (Ioo_mem_nhds ht.1 ht.2) Ioo_subset_Icc_self)
    have hqval : q t = f (γ.extend t) * deriv γ.extend t := by
      dsimp only [q]
      rw [curveIntegralFun_def]
      have htnhds : I ∈ 𝓝 t :=
        Filter.mem_of_superset (Ioo_mem_nhds ht.1 ht.2) Ioo_subset_Icc_self
      rw [derivWithin_of_mem_nhds htnhds]
      rfl
    rw [hqval]
    simpa only [g, Function.comp_def, smul_eq_mul, mul_comm] using
      (hF (γ.extend t) (hγs t ht)).scomp t hγdiff.hasDerivAt
  obtain ⟨A,hstart,hformula⟩ :=
    exists_tendsto_zero_of_integrable_derivative g q 1 (by norm_num) hq hg
  have hend : Tendsto (F ∘ γ.extend) (𝓝[<] (1:ℝ)) (𝓝 (F b)) := by
    have hγend : Tendsto γ.extend (𝓝[<] (1:ℝ)) (𝓝 b) := by
      have hγ1 : ContinuousAt γ.extend (1:ℝ) := γ.continuous_extend.continuousAt
      have hγ1' : Tendsto γ.extend (𝓝[<] (1:ℝ)) (𝓝 (γ.extend 1)) :=
        hγ1.tendsto.mono_left nhdsWithin_le_nhds
      simpa only [Path.extend_one] using hγ1'
    exact (hF b hb).continuousAt.tendsto.comp hγend
  refine ⟨A,hstart,?_,?_⟩
  · intro t ht
    exact hformula t ht
  · exact curveIntegral_eq_sub_of_primitive_with_limits
      f F s hF γ hγ hγs hint hstart hend

/-- If a primitive has a boundary limit at the singular starting
point, its integral along every smooth integrable connector is the
usual difference of endpoint values. -/
theorem curveIntegral_eq_sub_of_primitive_boundary_start
    (f F : ℂ → ℂ) (s : Set ℂ)
    (hF : ∀ z ∈ s, HasDerivAt F (f z) z)
    {a b : ℂ} (γ : Path a b)
    (hγ : ContDiffOn ℝ 1 γ.extend (Icc 0 1))
    (hγs : ∀ t ∈ Ioo (0:ℝ) 1, γ.extend t ∈ s)
    (hb : b ∈ s)
    (hint : CurveIntegrable (holomorphicOneForm f) γ)
    {A : ℂ} (hboundary : Tendsto F (𝓝[s] a) (𝓝 A)) :
    (∫ᶜ z in γ, holomorphicOneForm f z) = F b - A := by
  have hγstart : Tendsto γ.extend (𝓝[>] (0:ℝ)) (𝓝[s] a) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hγ0 : ContinuousAt γ.extend (0:ℝ) := γ.continuous_extend.continuousAt
      have hγ0' : Tendsto γ.extend (𝓝[>] (0:ℝ)) (𝓝 (γ.extend 0)) :=
        hγ0.tendsto.mono_left nhdsWithin_le_nhds
      simpa only [Path.extend_zero] using hγ0'
    · filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ) < 1)] with t ht
      exact hγs t ht
  have hstart : Tendsto (F ∘ γ.extend) (𝓝[>] (0:ℝ)) (𝓝 A) :=
    hboundary.comp hγstart
  have hend : Tendsto (F ∘ γ.extend) (𝓝[<] (1:ℝ)) (𝓝 (F b)) := by
    have hγend : Tendsto γ.extend (𝓝[<] (1:ℝ)) (𝓝 b) := by
      have hγ1 : ContinuousAt γ.extend (1:ℝ) := γ.continuous_extend.continuousAt
      have hγ1' : Tendsto γ.extend (𝓝[<] (1:ℝ)) (𝓝 (γ.extend 1)) :=
        hγ1.tendsto.mono_left nhdsWithin_le_nhds
      simpa only [Path.extend_one] using hγ1'
    exact (hF b hb).continuousAt.tendsto.comp hγend
  exact curveIntegral_eq_sub_of_primitive_with_limits f F s hF γ hγ hγs
    hint hstart hend

/-- Two integrable connectors with the same singular start and
regular endpoint have equal integrals when a primitive has the same
boundary limit along their domain. -/
theorem curveIntegral_eq_of_primitive_boundary_start
    (f F : ℂ → ℂ) (s : Set ℂ)
    (hF : ∀ z ∈ s, HasDerivAt F (f z) z)
    {a b : ℂ} (γ₁ γ₂ : Path a b)
    (hγ₁ : ContDiffOn ℝ 1 γ₁.extend (Icc 0 1))
    (hγ₂ : ContDiffOn ℝ 1 γ₂.extend (Icc 0 1))
    (hγ₁s : ∀ t ∈ Ioo (0:ℝ) 1, γ₁.extend t ∈ s)
    (hγ₂s : ∀ t ∈ Ioo (0:ℝ) 1, γ₂.extend t ∈ s)
    (hb : b ∈ s)
    (hγ₁int : CurveIntegrable (holomorphicOneForm f) γ₁)
    (hγ₂int : CurveIntegrable (holomorphicOneForm f) γ₂)
    {A : ℂ} (hboundary : Tendsto F (𝓝[s] a) (𝓝 A)) :
    (∫ᶜ z in γ₁, holomorphicOneForm f z) =
      ∫ᶜ z in γ₂, holomorphicOneForm f z := by
  rw [curveIntegral_eq_sub_of_primitive_boundary_start f F s hF γ₁
      hγ₁ hγ₁s hb hγ₁int hboundary,
    curveIntegral_eq_sub_of_primitive_boundary_start f F s hF γ₂
      hγ₂ hγ₂s hb hγ₂int hboundary]

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

/-- A `C¹` loop of a holomorphic one-form inside an open convex set
has zero integral. This needs only one derivative of the path. -/
theorem curveIntegral_eq_zero_of_convex_loop_one
    (f : ℂ → ℂ) (s : Set ℂ) (hconv : Convex ℝ s)
    (hopen : IsOpen s) (hf : DifferentiableOn ℂ f s)
    {a : ℂ} (γ : Path a a)
    (hγ : ContDiffOn ℝ 1 γ.extend (Icc 0 1))
    (hγs : ∀ t ∈ Icc (0:ℝ) 1, γ.extend t ∈ s)
    (hint : CurveIntegrable (holomorphicOneForm f) γ) :
    (∫ᶜ z in γ, holomorphicOneForm f z) = 0 := by
  obtain ⟨F,hF⟩ := exists_primitive_on_convex f s hconv hopen hf
  rw [curveIntegral_eq_sub_of_primitive f F s hF γ hγ hγs hint, sub_self]

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
