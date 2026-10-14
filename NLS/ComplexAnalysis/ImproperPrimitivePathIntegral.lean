import NLS.ComplexAnalysis.PrimitiveBoundaryPathIntegral
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Improper endpoint integrals of arbitrary interior C¹ paths

The integral is the two-sided limit of actual truncated parameter
integrals. A primitive with full relative boundary limits evaluates it
without assuming absolute integrability at the singular endpoints.
The two truncation parameters approach their endpoints independently.
-/

noncomputable section
open Set Filter Topology MeasureTheory Complex
namespace NLS.ComplexAnalysis

/-- An ordinary integral on a truncated portion of the actual path. -/
def truncatedPathIntegral (f : ℂ → ℂ) {a b : ℂ} (γ : Path a b) (u v : ℝ) : ℂ :=
  ∫ t in u..v, f (γ.extend t)*deriv γ.extend t

/-- The improper endpoint integral, defined from actual truncated integrals. -/
def improperPathIntegral (f : ℂ → ℂ) {a b : ℂ} (γ : Path a b) : ℂ :=
  limUnder ((𝓝[>] (0 : ℝ)) ×ˢ (𝓝[<] (1 : ℝ)))
    (fun t : ℝ × ℝ => truncatedPathIntegral f γ t.1 t.2)

/-- Every interior truncation is an integrable proper integral and equals
the corresponding primitive difference. -/
theorem truncatedPathIntegral_eq_sub (f F : ℂ → ℂ) (D : Set ℂ)
    (hf : ContinuousOn f D) (hF : ∀ z ∈ D, HasDerivAt F (f z) z)
    {a b : ℂ} (γ : Path a b) (hγ : ContDiffOn ℝ 1 γ.extend (Ioo 0 1))
    (hγD : ∀ t ∈ Ioo (0 : ℝ) 1, γ.extend t ∈ D)
    (u v : ℝ) (hu : 0 < u) (huv : u ≤ v) (hv : v < 1) :
    IntervalIntegrable (fun t => f (γ.extend t)*deriv γ.extend t) volume u v ∧
      truncatedPathIntegral f γ u v = F (γ.extend v)-F (γ.extend u) := by
  have hsub : uIcc u v ⊆ Ioo (0 : ℝ) 1 := by
    rw [uIcc_of_le huv]
    intro t ht
    exact ⟨hu.trans_le ht.1,ht.2.trans_lt hv⟩
  have hc : ContinuousOn (fun t => f (γ.extend t)*deriv γ.extend t) (Ioo (0 : ℝ) 1) :=
    (hf.comp hγ.continuousOn hγD).mul (hγ.continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl)
  have hint : IntervalIntegrable (fun t => f (γ.extend t)*deriv γ.extend t) volume u v :=
    (hc.mono hsub).intervalIntegrable
  refine ⟨hint,?_⟩
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ hint
  intro t ht
  have hi := hsub ht
  have hd := (hγ.differentiableOn (by norm_num) t hi).differentiableAt (isOpen_Ioo.mem_nhds hi)
  simpa only [smul_eq_mul,mul_comm,Function.comp_def] using! (hF _ (hγD t hi)).scomp t hd.hasDerivAt

/-- The improper integral exists for every interior C¹ path whose
primitive has relative limits at the two endpoints. -/
theorem tendsto_truncatedPathIntegral_of_primitive_boundary
    (f F : ℂ → ℂ) (D : Set ℂ)
    (hf : ContinuousOn f D) (hF : ∀ z ∈ D, HasDerivAt F (f z) z)
    {a b : ℂ} (γ : Path a b) (hγ : ContDiffOn ℝ 1 γ.extend (Ioo 0 1))
    (hγD : ∀ t ∈ Ioo (0 : ℝ) 1, γ.extend t ∈ D) {A B : ℂ}
    (ha : Tendsto F (𝓝[D] a) (𝓝 A)) (hb : Tendsto F (𝓝[D] b) (𝓝 B)) :
    Tendsto (fun t : ℝ × ℝ => truncatedPathIntegral f γ t.1 t.2)
      ((𝓝[>] (0 : ℝ)) ×ˢ (𝓝[<] (1 : ℝ))) (𝓝 (B-A)) := by
  have hstart : Tendsto γ.extend (𝓝[>] (0 : ℝ)) (𝓝[D] a) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_,?_⟩
    · simpa only [Path.extend_zero] using
        (γ.continuous_extend.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with t ht
      exact hγD t ht
  have hend : Tendsto γ.extend (𝓝[<] (1 : ℝ)) (𝓝[D] b) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_,?_⟩
    · simpa only [Path.extend_one] using
        (γ.continuous_extend.continuousAt (x := (1 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with t ht
      exact hγD t ht
  have hlim : Tendsto (fun t : ℝ × ℝ => F (γ.extend t.2)-F (γ.extend t.1))
      ((𝓝[>] (0 : ℝ)) ×ˢ (𝓝[<] (1 : ℝ))) (𝓝 (B-A)) :=
    ((hb.comp hend).comp tendsto_snd).sub ((ha.comp hstart).comp tendsto_fst)
  apply hlim.congr'
  have hu : ∀ᶠ u in 𝓝[>] (0 : ℝ), u ∈ Ioo (0 : ℝ) (1/2) := Ioo_mem_nhdsGT (by norm_num)
  have hv : ∀ᶠ v in 𝓝[<] (1 : ℝ), v ∈ Ioo (1/2 : ℝ) 1 := Ioo_mem_nhdsLT (by norm_num)
  filter_upwards [hu.prod_mk hv] with t ht
  exact (truncatedPathIntegral_eq_sub f F D hf hF γ hγ hγD t.1 t.2 ht.1.1
    (by linarith [ht.1.2,ht.2.1]) ht.2.2).2.symm

/-- The limit-defined integral equals the difference of boundary values. -/
theorem improperPathIntegral_eq_sub (f F : ℂ → ℂ) (D : Set ℂ)
    (hf : ContinuousOn f D) (hF : ∀ z ∈ D, HasDerivAt F (f z) z)
    {a b : ℂ} (γ : Path a b) (hγ : ContDiffOn ℝ 1 γ.extend (Ioo 0 1))
    (hγD : ∀ t ∈ Ioo (0 : ℝ) 1, γ.extend t ∈ D) {A B : ℂ}
    (ha : Tendsto F (𝓝[D] a) (𝓝 A)) (hb : Tendsto F (𝓝[D] b) (𝓝 B)) :
    improperPathIntegral f γ = B-A :=
  (tendsto_truncatedPathIntegral_of_primitive_boundary f F D hf hF γ hγ hγD ha hb).limUnder_eq

/-- When the full curve integral is integrable, the improper definition
agrees with the ordinary curve integral. -/
theorem improperPathIntegral_eq_curveIntegral (f F : ℂ → ℂ) (D : Set ℂ)
    (hf : ContinuousOn f D) (hF : ∀ z ∈ D, HasDerivAt F (f z) z)
    {a b : ℂ} (γ : Path a b) (hγ : ContDiffOn ℝ 1 γ.extend (Icc 0 1))
    (hγD : ∀ t ∈ Ioo (0 : ℝ) 1, γ.extend t ∈ D)
    (hint : CurveIntegrable (holomorphicOneForm f) γ) {A B : ℂ}
    (ha : Tendsto F (𝓝[D] a) (𝓝 A)) (hb : Tendsto F (𝓝[D] b) (𝓝 B)) :
    improperPathIntegral f γ = ∫ᶜ z in γ, holomorphicOneForm f z := by
  rw [improperPathIntegral_eq_sub f F D hf hF γ (hγ.mono Ioo_subset_Icc_self) hγD ha hb,
    curveIntegral_eq_sub_of_primitive_boundary_ends f F D hF γ hγ hγD hint ha hb]

end NLS.ComplexAnalysis
