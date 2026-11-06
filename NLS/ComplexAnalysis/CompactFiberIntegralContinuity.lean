import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Topology.UniformSpace.CompactConvergence

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open scoped ENNReal ComplexConjugate Classical

namespace NLS.ComplexAnalysis



/-- Integration of jointly continuous compact fibers is continuous for arbitrary
parameter spaces, including infinite-dimensional source domains. -/
theorem continuous_integral_of_continuous_compact_fibers
    {A K E : Type} [TopologicalSpace A] [TopologicalSpace K] [CompactSpace K] [SecondCountableTopology K]
    [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsFiniteMeasure μ]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : A × K → E) (hF : Continuous F) :
    Continuous (fun a => ∫ t, F (a,t) ∂μ) := by
  let G : A → C(K,E) := fun a => ⟨fun t => F (a,t),hF.comp (continuous_const.prodMk continuous_id)⟩
  have hG : Continuous G := ContinuousMap.continuous_of_continuous_uncurry G hF
  have hi := continuous_integral.comp ((ContinuousMap.toLp 1 μ ℝ).continuous.comp hG)
  apply hi.congr
  intro a
  exact integral_congr_ae (ContinuousMap.coeFn_toLp (p := 1) (𝕜 := ℝ) μ (G a))

/-- A fixed-circle integral of jointly continuous fibers is continuous without
local compactness of its source parameter space. -/
theorem continuous_circleIntegral_of_compact_spectral_fibers
    {A E : Type} [TopologicalSpace A]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (F : A × ℂ → E) (c : ℂ) (R : ℝ) (hR : 0≤R)
    (hF : ContinuousOn F (univ ×ˢ sphere c R)) :
    Continuous (fun a => ∮ z in C(c,R),F (a,z)) := by
  let K := Icc (0 : ℝ) (2*Real.pi)
  let G : A × K → E := fun p => deriv (circleMap c R) p.2.val • F (p.1,circleMap c R p.2.val)
  have hc : Continuous (fun p : A × K => (p.1,circleMap c R p.2.val)) :=
    continuous_fst.prodMk ((continuous_circleMap c R).comp (continuous_subtype_val.comp continuous_snd))
  have hsection : Continuous (fun p : A × K => F (p.1,circleMap c R p.2.val)) :=
    hF.comp_continuous hc (fun p => ⟨mem_univ _,circleMap_mem_sphere c hR p.2.val⟩)
  have hd : Continuous (fun p : A × K => deriv (circleMap c R) p.2.val) := by
    simp only [deriv_circleMap]
    fun_prop
  have hG : Continuous G := hd.smul hsection
  let μ : Measure K := (volume : Measure ℝ).comap ((↑) : K → ℝ)
  let : IsFiniteMeasure μ := ⟨by
    dsimp only [μ]
    rw [comap_subtype_coe_apply measurableSet_Icc]
    simpa only [image_univ,Subtype.range_coe] using
      (isCompact_Icc.measure_lt_top (μ := (volume : Measure ℝ)) : volume (Icc (0 : ℝ) (2*Real.pi))<⊤)⟩
  have hi := continuous_integral_of_continuous_compact_fibers μ G hG
  apply hi.congr
  intro a
  rw [circleIntegral_def_Icc]
  exact integral_subtype_comap (μ := (volume : Measure ℝ)) measurableSet_Icc
    (fun θ : ℝ => deriv (circleMap c R) θ • F (a,circleMap c R θ))

/-- Moving real-centered or complex-centered contours vary continuously when their
actual compact angular sections do, in arbitrary source parameter spaces. -/
theorem continuous_circleIntegral_of_continuous_moving_section
    {A E : Type} [TopologicalSpace A]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (F : A × ℂ → E) (c : A → ℂ) (R : A → ℝ)
    (hR : Continuous R)
    (hsection : Continuous (fun p : A × Icc (0 : ℝ) (2*Real.pi) =>
      F (p.1,circleMap (c p.1) (R p.1) p.2.val))) :
    Continuous (fun a => ∮ z in C(c a,R a),F (a,z)) := by
  let K := Icc (0 : ℝ) (2*Real.pi)
  let G : A × K → E := fun p => deriv (circleMap (c p.1) (R p.1)) p.2.val •
    F (p.1,circleMap (c p.1) (R p.1) p.2.val)
  have hd : Continuous (fun p : A × K => deriv (circleMap (c p.1) (R p.1)) p.2.val) := by
    simp only [deriv_circleMap,circleMap]
    fun_prop
  have hG : Continuous G := hd.smul hsection
  let μ : Measure K := (volume : Measure ℝ).comap ((↑) : K → ℝ)
  let : IsFiniteMeasure μ := ⟨by
    dsimp only [μ]
    rw [comap_subtype_coe_apply measurableSet_Icc]
    simpa only [image_univ,Subtype.range_coe] using
      (isCompact_Icc.measure_lt_top (μ := (volume : Measure ℝ)) : volume (Icc (0 : ℝ) (2*Real.pi))<⊤)⟩
  have hi := continuous_integral_of_continuous_compact_fibers μ G hG
  apply hi.congr
  intro a
  rw [circleIntegral_def_Icc]
  exact integral_subtype_comap (μ := (volume : Measure ℝ)) measurableSet_Icc
    (fun θ : ℝ => deriv (circleMap (c a) (R a)) θ • F (a,circleMap (c a) (R a) θ))

end NLS.ComplexAnalysis
