import NLS.KdV.HillL2RegularBoundary
import NLS.ComplexAnalysis.UpperLogarithmBoundary
import NLS.ComplexAnalysis.QuadraticRootPrimitive

/-! # Finite actual Hill boundary limits at every real energy

At any characteristic zero, including low endpoints and collisions,
the actual upper root tends to zero. The multiplier then tends to the
nonzero half-trace. A local logarithm retains the actual source period
and proves a finite primitive limit without a high-energy cutoff.
-/

noncomputable section
open Set Metric Complex Filter Topology
namespace NLS.KdV
open NLS.ComplexAnalysis

theorem tendsto_hillL2ContinuedRoot_at_real_zero
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (x : ℝ) (hx : hillL2Radicand (SpectralWeight.one.toCoeff q) x = 0) :
    Tendsto (fun z => hillL2ContinuedRoot (z, SpectralWeight.one.toCoeff q))
      (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) (𝓝 0) := by
  apply tendsto_zero_of_sq_tendsto_zero
  have hd : Tendsto (hillL2Radicand (SpectralWeight.one.toCoeff q))
      (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ))
      (𝓝 (hillL2Radicand (SpectralWeight.one.toCoeff q) x)) :=
    ((analyticOnNhd_hillL2Radicand (SpectralWeight.one.toCoeff q) x
    (mem_univ _)).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds)
  rw [hx] at hd
  apply hd.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact (hillL2ContinuedRoot_sq (z, SpectralWeight.one.toCoeff q)
    (mem_hillL2ContinuationDomain_of_im_ne_zero q hq hr z hz.ne')).symm

theorem exists_hillL2ContinuedPrimitive_upper_limit_at_zero
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (x : ℝ) (hx : hillL2Radicand (SpectralWeight.one.toCoeff q) x = 0) :
    ∃ A : ℂ,
      Tendsto (fun z => hillL2ContinuedPrimitive (z, SpectralWeight.one.toCoeff q))
        (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) (𝓝 A) ∧
      exp A = hillL2Discriminant (SpectralWeight.one.toCoeff q) x / 2 := by
  have hD : Tendsto (hillL2Discriminant (SpectralWeight.one.toCoeff q))
      (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ))
      (𝓝 (hillL2Discriminant (SpectralWeight.one.toCoeff q) x)) :=
    (analyticOnNhd_hillL2Discriminant (SpectralWeight.one.toCoeff q) x
    (mem_univ _)).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  have hM := (hD.add (tendsto_hillL2ContinuedRoot_at_real_zero q hq hr x hx)).div_const 2
  have hne : hillL2Discriminant (SpectralWeight.one.toCoeff q) x / 2 ≠ 0 := by
    have hs : hillL2Discriminant (SpectralWeight.one.toCoeff q) x ^ 2 = 4 := sub_eq_zero.mp hx
    apply div_ne_zero _ (by norm_num)
    intro he
    rw [he] at hs
    norm_num at hs
  apply exists_upper_logarithm_boundary_limit _ x _ hne
    ((analyticOnNhd_hillL2ContinuedPrimitive_off_real q hq hr).continuousOn.mono
      (fun _ hz => hz.ne'))
  simp only [add_zero] at hM
  apply hM.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact (exp_hillL2ContinuedPrimitive (z, SpectralWeight.one.toCoeff q)
    (mem_hillL2ContinuationDomain_of_im_ne_zero q hq hr z hz.ne')).symm

/-- The upper boundary defined by `limUnder` is a genuine full upper
limit at every real energy, including all branch endpoints. -/
theorem tendsto_hillL2UpperBoundaryPrimitive_all
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (x : ℝ) :
    Tendsto (fun z => hillL2ContinuedPrimitive (z, SpectralWeight.one.toCoeff q))
      (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ))
      (𝓝 (hillL2UpperBoundaryPrimitive (SpectralWeight.one.toCoeff q) x)) := by
  by_cases hx : hillL2Radicand (SpectralWeight.one.toCoeff q) x = 0
  · obtain ⟨A, hA, _⟩ := exists_hillL2ContinuedPrimitive_upper_limit_at_zero q hq hr x hx
    let := real_upper_nhds_neBot x
    simpa only [hillL2UpperBoundaryPrimitive, hA.limUnder_eq] using hA
  · exact tendsto_hillL2UpperBoundaryPrimitive q hq hr x hx

theorem hillL2UpperBoundaryPrimitive_exp_at_zero
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (x : ℝ) (hx : hillL2Radicand (SpectralWeight.one.toCoeff q) x = 0) :
    exp (hillL2UpperBoundaryPrimitive (SpectralWeight.one.toCoeff q) x) =
      hillL2Discriminant (SpectralWeight.one.toCoeff q) x / 2 := by
  obtain ⟨A, hA, he⟩ := exists_hillL2ContinuedPrimitive_upper_limit_at_zero q hq hr x hx
  let := real_upper_nhds_neBot x
  simpa only [hillL2UpperBoundaryPrimitive, hA.limUnder_eq] using he

theorem tendsto_hillL2UpperBoundaryRoot_all
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (x : ℝ) :
    Tendsto (fun z => hillL2ContinuedRoot (z, SpectralWeight.one.toCoeff q))
      (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ))
      (𝓝 (hillL2UpperBoundaryRoot (SpectralWeight.one.toCoeff q) x)) := by
  let := real_upper_nhds_neBot x
  by_cases hx : hillL2Radicand (SpectralWeight.one.toCoeff q) x = 0
  · have h := tendsto_hillL2ContinuedRoot_at_real_zero q hq hr x hx
    simpa only [hillL2UpperBoundaryRoot, h.limUnder_eq] using h
  · obtain ⟨ρ, hρ, L, G, h⟩ := exists_hillL2UpperRegularExtension q hq hr x hx
    have ht := h.root_tendsto x (mem_ball_self hρ)
    simpa only [hillL2UpperBoundaryRoot, ht.limUnder_eq] using ht

theorem continuous_hillL2UpperBoundaryPrimitive
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) :
    Continuous (hillL2UpperBoundaryPrimitive (SpectralWeight.one.toCoeff q)) :=
  continuous_real_boundary_of_upper_limits _ _ (tendsto_hillL2UpperBoundaryPrimitive_all q hq hr)

theorem continuous_hillL2UpperBoundaryRoot
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) :
    Continuous (hillL2UpperBoundaryRoot (SpectralWeight.one.toCoeff q)) :=
  continuous_real_boundary_of_upper_limits _ _ (tendsto_hillL2UpperBoundaryRoot_all q hq hr)

theorem hillL2UpperBoundary_trace_all
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (x : ℝ) :
    2 * cosh (hillL2UpperBoundaryPrimitive (SpectralWeight.one.toCoeff q) x) =
        hillL2Discriminant (SpectralWeight.one.toCoeff q) x ∧
      2 * sinh (hillL2UpperBoundaryPrimitive (SpectralWeight.one.toCoeff q) x) =
        hillL2UpperBoundaryRoot (SpectralWeight.one.toCoeff q) x := by
  let := real_upper_nhds_neBot x
  have hP := tendsto_hillL2UpperBoundaryPrimitive_all q hq hr x
  have hR := tendsto_hillL2UpperBoundaryRoot_all q hq hr x
  have hD : Tendsto (hillL2Discriminant (SpectralWeight.one.toCoeff q))
      (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ))
      (𝓝 (hillL2Discriminant (SpectralWeight.one.toCoeff q) x)) :=
    (analyticOnNhd_hillL2Discriminant (SpectralWeight.one.toCoeff q) x
      (mem_univ _)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hcosh : (fun z => 2 * cosh (hillL2ContinuedPrimitive (z, SpectralWeight.one.toCoeff q)))
      =ᶠ[𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)] hillL2Discriminant (SpectralWeight.one.toCoeff q) := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact (hillL2ContinuedPrimitive_trace _
      (mem_hillL2ContinuationDomain_of_im_ne_zero q hq hr z hz.ne')).1
  have hsinh : (fun z => 2 * sinh (hillL2ContinuedPrimitive (z, SpectralWeight.one.toCoeff q)))
      =ᶠ[𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)]
        (fun z => hillL2ContinuedRoot (z, SpectralWeight.one.toCoeff q)) := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact (hillL2ContinuedPrimitive_trace _
      (mem_hillL2ContinuationDomain_of_im_ne_zero q hq hr z hz.ne')).2
  exact ⟨tendsto_nhds_unique ((continuous_cosh.continuousAt.tendsto.comp hP).const_mul 2)
      (hD.congr' hcosh.symm),
    tendsto_nhds_unique ((continuous_sinh.continuousAt.tendsto.comp hP).const_mul 2)
      (hR.congr' hsinh.symm)⟩

end NLS.KdV
