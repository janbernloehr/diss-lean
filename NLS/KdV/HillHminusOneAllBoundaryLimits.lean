import NLS.KdV.HillHminusOneRegularBoundary
import NLS.ComplexAnalysis.UpperLogarithmBoundary
import NLS.ComplexAnalysis.QuadraticRootPrimitive

/-! # Finite actual Hill boundary limits at every real energy

At any characteristic zero, including low endpoints and collisions,
the actual upper root tends to zero. The multiplier then tends to the
nonzero half-trace. A local logarithm retains the actual source period
and proves a finite primitive limit without a high-energy cutoff.
-/

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
namespace NLS.KdV
open NLS.ComplexAnalysis

theorem tendsto_hillHminusContinuedRoot_at_real_zero
    (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q)
    (x : ℝ) (hx : hillHminusRadicand q x = 0) :
    Tendsto (fun z => hillHminusContinuedRoot (z, q))
      (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) (𝓝 0) := by
  apply tendsto_zero_of_sq_tendsto_zero
  have hd : Tendsto (hillHminusRadicand q)
      (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ))
      (𝓝 (hillHminusRadicand q x)) :=
    ((analyticOnNhd_hillHminusRadicand q x
    (mem_univ _)).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds)
  rw [hx] at hd
  apply hd.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact (hillHminusContinuedRoot_sq (z, q)
    (mem_hillHminusContinuationDomain_of_im_ne_zero q hr z hz.ne')).symm

theorem exists_hillHminusContinuedPrimitive_upper_limit_at_zero
    (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q)
    (x : ℝ) (hx : hillHminusRadicand q x = 0) :
    ∃ A : ℂ,
      Tendsto (fun z => hillHminusContinuedPrimitive (z, q))
        (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) (𝓝 A) ∧
      exp A = hillHminusDiscriminant q x / 2 := by
  have hD : Tendsto (hillHminusDiscriminant q)
      (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ))
      (𝓝 (hillHminusDiscriminant q x)) :=
    (analyticOnNhd_hillHminusDiscriminant q x
    (mem_univ _)).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  have hM := (hD.add (tendsto_hillHminusContinuedRoot_at_real_zero q hr x hx)).div_const 2
  have hne : hillHminusDiscriminant q x / 2 ≠ 0 := by
    have hs : hillHminusDiscriminant q x ^ 2 = 4 := sub_eq_zero.mp hx
    apply div_ne_zero _ (by norm_num)
    intro he
    rw [he] at hs
    norm_num at hs
  apply exists_upper_logarithm_boundary_limit _ x _ hne
    ((analyticOnNhd_hillHminusContinuedPrimitive_off_real q hr).continuousOn.mono
      (fun _ hz => hz.ne'))
  simp only [add_zero] at hM
  apply hM.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact (exp_hillHminusContinuedPrimitive (z, q)
    (mem_hillHminusContinuationDomain_of_im_ne_zero q hr z hz.ne')).symm

/-- The upper boundary defined by `limUnder` is a genuine full upper
limit at every real energy, including all branch endpoints. -/
theorem tendsto_hillHminusUpperBoundaryPrimitive_all
    (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) (x : ℝ) :
    Tendsto (fun z => hillHminusContinuedPrimitive (z, q))
      (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ))
      (𝓝 (hillHminusUpperBoundaryPrimitive q x)) := by
  by_cases hx : hillHminusRadicand q x = 0
  · obtain ⟨A, hA, _⟩ := exists_hillHminusContinuedPrimitive_upper_limit_at_zero q hr x hx
    let := real_upper_nhds_neBot x
    simpa only [hillHminusUpperBoundaryPrimitive, hA.limUnder_eq] using hA
  · exact tendsto_hillHminusUpperBoundaryPrimitive q hr x hx

theorem hillHminusUpperBoundaryPrimitive_exp_at_zero
    (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q)
    (x : ℝ) (hx : hillHminusRadicand q x = 0) :
    exp (hillHminusUpperBoundaryPrimitive q x) =
      hillHminusDiscriminant q x / 2 := by
  obtain ⟨A, hA, he⟩ := exists_hillHminusContinuedPrimitive_upper_limit_at_zero q hr x hx
  let := real_upper_nhds_neBot x
  simpa only [hillHminusUpperBoundaryPrimitive, hA.limUnder_eq] using he

theorem tendsto_hillHminusUpperBoundaryRoot_all
    (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) (x : ℝ) :
    Tendsto (fun z => hillHminusContinuedRoot (z, q))
      (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ))
      (𝓝 (hillHminusUpperBoundaryRoot q x)) := by
  let := real_upper_nhds_neBot x
  by_cases hx : hillHminusRadicand q x = 0
  · have h := tendsto_hillHminusContinuedRoot_at_real_zero q hr x hx
    simpa only [hillHminusUpperBoundaryRoot, h.limUnder_eq] using h
  · obtain ⟨ρ, hρ, L, G, h⟩ := exists_hillHminusUpperRegularExtension q hr x hx
    have ht := h.root_tendsto x (mem_ball_self hρ)
    simpa only [hillHminusUpperBoundaryRoot, ht.limUnder_eq] using ht

theorem continuous_hillHminusUpperBoundaryPrimitive
    (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) :
    Continuous (hillHminusUpperBoundaryPrimitive q) :=
  continuous_real_boundary_of_upper_limits _ _ (tendsto_hillHminusUpperBoundaryPrimitive_all q hr)

theorem continuous_hillHminusUpperBoundaryRoot
    (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) :
    Continuous (hillHminusUpperBoundaryRoot q) :=
  continuous_real_boundary_of_upper_limits _ _ (tendsto_hillHminusUpperBoundaryRoot_all q hr)

theorem hillHminusUpperBoundary_trace_all
    (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) (x : ℝ) :
    2 * cosh (hillHminusUpperBoundaryPrimitive q x) =
        hillHminusDiscriminant q x ∧
      2 * sinh (hillHminusUpperBoundaryPrimitive q x) =
        hillHminusUpperBoundaryRoot q x := by
  let := real_upper_nhds_neBot x
  have hP := tendsto_hillHminusUpperBoundaryPrimitive_all q hr x
  have hR := tendsto_hillHminusUpperBoundaryRoot_all q hr x
  have hD : Tendsto (hillHminusDiscriminant q)
      (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ))
      (𝓝 (hillHminusDiscriminant q x)) :=
    (analyticOnNhd_hillHminusDiscriminant q x
      (mem_univ _)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hcosh : (fun z => 2 * cosh (hillHminusContinuedPrimitive (z, q)))
      =ᶠ[𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)] hillHminusDiscriminant q := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact (hillHminusContinuedPrimitive_trace _
      (mem_hillHminusContinuationDomain_of_im_ne_zero q hr z hz.ne')).1
  have hsinh : (fun z => 2 * sinh (hillHminusContinuedPrimitive (z, q)))
      =ᶠ[𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)]
        (fun z => hillHminusContinuedRoot (z, q)) := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact (hillHminusContinuedPrimitive_trace _
      (mem_hillHminusContinuationDomain_of_im_ne_zero q hr z hz.ne')).2
  exact ⟨tendsto_nhds_unique ((continuous_cosh.continuousAt.tendsto.comp hP).const_mul 2)
      (hD.congr' hcosh.symm),
    tendsto_nhds_unique ((continuous_sinh.continuousAt.tendsto.comp hP).const_mul 2)
      (hR.congr' hsinh.symm)⟩

end NLS.KdV
