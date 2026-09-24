import NLS.ZakharovShabat.SourceCriticalRootRatioVerticalIntegrability

/-!
# One-sided critical-root quotient limits along vertical gap paths

For an open real-type gap, the oriented upper and lower sides agree
with positive and negative vertical displacements. This specializes
the established one-sided quotient limits to the paths used in the
transverse integral estimate.
-/

noncomputable section
open Set Filter Topology Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The oriented imaginary coordinate of a vertically shifted real
gap point is its displacement divided by the positive half-gap. -/
theorem sourceCanonicalRootGapPoint_vertical_side_coordinate_im
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ) (t y : ℝ) :
    let a := (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re
    let b := (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re
    ((sourceCanonicalRootGapPoint hp hp1 ψ n t + (y:ℂ)*I -
      sourceStandardRootMidpoint hp hp1 ψ n) /
      sourceStandardRootHalfGap hp hp1 ψ n).im = y / ((b-a)/2) := by
  let a := (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n).re
  let b := (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n).re
  let d : ℝ := (b-a)/2
  let τ := sourceStandardRootMidpoint hp hp1 ψ n
  let δ := sourceStandardRootHalfGap hp hp1 ψ n
  let q := sourceCanonicalRootGapPoint hp hp1 ψ n t
  have hδ : δ = (d:ℂ) :=
    sourceStandardRootHalfGap_eq_ofReal_affineJacobian hp hp1 ψ hreal n
  have hqτ : (q-τ).im = 0 := by
    have hq : q-τ = δ*(t:ℂ) := by
      dsimp [q, sourceCanonicalRootGapPoint]
      ring
    rw [hq,hδ]
    simp
  have hnum : (q+(y:ℂ)*I-τ).im = y := by
    calc
      (q+(y:ℂ)*I-τ).im = ((q-τ)+(y:ℂ)*I).im := by congr 1; ring
      _ = y := by simp [hqτ]
  change ((q+(y:ℂ)*I-τ)/δ).im = y/d
  rw [hδ, Complex.div_ofReal_im, hnum]

/-- Positive vertical displacements lie on the oriented upper side. -/
theorem sourceCanonicalRootGapPoint_vertical_mem_upperSide
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re)
    (t y : ℝ) (hy : 0 < y) :
    sourceCanonicalRootGapPoint hp hp1 ψ n t + (y:ℂ)*I ∈
      standardRootGapUpperSide
        (sourceStandardRootMidpoint hp hp1 ψ n)
        (sourceStandardRootHalfGap hp hp1 ψ n) := by
  have hd : 0 < ((canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re -
      (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re)/2 := by linarith
  change 0 < ((sourceCanonicalRootGapPoint hp hp1 ψ n t + (y:ℂ)*I -
    sourceStandardRootMidpoint hp hp1 ψ n) /
    sourceStandardRootHalfGap hp hp1 ψ n).im
  rw [sourceCanonicalRootGapPoint_vertical_side_coordinate_im
    hp hp1 ψ hreal n t y]
  exact div_pos hy hd

/-- Negative vertical displacements lie on the oriented lower side. -/
theorem sourceCanonicalRootGapPoint_vertical_mem_lowerSide
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re)
    (t y : ℝ) (hy : y < 0) :
    sourceCanonicalRootGapPoint hp hp1 ψ n t + (y:ℂ)*I ∈
      standardRootGapLowerSide
        (sourceStandardRootMidpoint hp hp1 ψ n)
        (sourceStandardRootHalfGap hp hp1 ψ n) := by
  have hd : 0 < ((canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re -
      (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re)/2 := by linarith
  change ((sourceCanonicalRootGapPoint hp hp1 ψ n t + (y:ℂ)*I -
    sourceStandardRootMidpoint hp hp1 ψ n) /
    sourceStandardRootHalfGap hp hp1 ψ n).im < 0
  rw [sourceCanonicalRootGapPoint_vertical_side_coordinate_im
    hp hp1 ψ hreal n t y]
  exact div_neg_of_neg_of_pos hy hd

/-- A positive vertical approach to a real open gap converges through
the oriented upper side. -/
theorem sourceCanonicalRootGapPoint_vertical_tendsto_upperSide
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re)
    (t : ℝ) :
    Tendsto (fun y : ℝ =>
      sourceCanonicalRootGapPoint hp hp1 ψ n t + (y:ℂ)*I)
      (𝓝[Set.Ioi 0] (0:ℝ))
      (𝓝[standardRootGapUpperSide
        (sourceStandardRootMidpoint hp hp1 ψ n)
        (sourceStandardRootHalfGap hp hp1 ψ n)]
        (sourceCanonicalRootGapPoint hp hp1 ψ n t)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have hc : ContinuousAt (fun y : ℝ =>
        sourceCanonicalRootGapPoint hp hp1 ψ n t + (y:ℂ)*I) 0 := by
      fun_prop
    convert hc.tendsto.mono_left nhdsWithin_le_nhds using 1; simp
  · filter_upwards [self_mem_nhdsWithin] with y hy
    exact sourceCanonicalRootGapPoint_vertical_mem_upperSide
      hp hp1 ψ hreal n hopen t y hy

/-- A negative vertical approach converges through the oriented lower
side of a real open gap. -/
theorem sourceCanonicalRootGapPoint_vertical_tendsto_lowerSide
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re)
    (t : ℝ) :
    Tendsto (fun y : ℝ =>
      sourceCanonicalRootGapPoint hp hp1 ψ n t + (y:ℂ)*I)
      (𝓝[Set.Iio 0] (0:ℝ))
      (𝓝[standardRootGapLowerSide
        (sourceStandardRootMidpoint hp hp1 ψ n)
        (sourceStandardRootHalfGap hp hp1 ψ n)]
        (sourceCanonicalRootGapPoint hp hp1 ψ n t)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have hc : ContinuousAt (fun y : ℝ =>
        sourceCanonicalRootGapPoint hp hp1 ψ n t + (y:ℂ)*I) 0 := by
      fun_prop
    convert hc.tendsto.mono_left nhdsWithin_le_nhds using 1; simp
  · filter_upwards [self_mem_nhdsWithin] with y hy
    exact sourceCanonicalRootGapPoint_vertical_mem_lowerSide
      hp hp1 ψ hreal n hopen t y hy

/-- An open real-type periodic gap has nonzero canonical gap length. -/
theorem sourceCanonicalPeriodicGap_ne_zero_of_openRealGap
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re) :
    canonicalPeriodicGap hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n ≠ 0 := by
  have hhalf := sourceStandardRootHalfGap_ne_zero_of_openRealGap
    hp hp1 ψ hreal n hopen
  intro h
  apply hhalf
  change canonicalPeriodicGap hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n / 2 = 0
  rw [h]
  simp

/-- The actual quotient tends to its upper boundary value along a
positive vertical approach to an interior gap point. -/
theorem sourceCriticalRootRatio_tendsto_vertical_upper
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re)
    (t : ℝ) (ht : t ∈ Ioo (-1) 1) :
    Tendsto (fun y : ℝ =>
      deriv (canonicalDiscriminant hp (periodOnePotential ψ))
          (sourceCanonicalRootGapPoint hp hp1 ψ n t + (y:ℂ)*I) /
        sourceCanonicalRoot hp hp1 ψ
          (sourceCanonicalRootGapPoint hp hp1 ψ n t + (y:ℂ)*I))
      (𝓝[Set.Ioi 0] (0:ℝ))
      (𝓝 (deriv (canonicalDiscriminant hp (periodOnePotential ψ))
          (sourceCanonicalRootGapPoint hp hp1 ψ n t) /
        sourceCanonicalRootGapUpperValue hp hp1 ψ n t)) := by
  obtain ⟨W,_,hWreal,hlimits⟩ :=
    exists_global_sourceCriticalRootRatio_gapSideLimits hp hp1
  have hψ : ψ ∈ W := hWreal hreal
  have hgap := sourceCanonicalPeriodicGap_ne_zero_of_openRealGap
    hp hp1 ψ hreal n hopen
  exact (hlimits ψ hψ n t ht hgap).1.comp
    (sourceCanonicalRootGapPoint_vertical_tendsto_upperSide
      hp hp1 ψ hreal n hopen t)

/-- The corresponding negative vertical approach tends to the lower
boundary quotient. -/
theorem sourceCriticalRootRatio_tendsto_vertical_lower
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re)
    (t : ℝ) (ht : t ∈ Ioo (-1) 1) :
    Tendsto (fun y : ℝ =>
      deriv (canonicalDiscriminant hp (periodOnePotential ψ))
          (sourceCanonicalRootGapPoint hp hp1 ψ n t + (y:ℂ)*I) /
        sourceCanonicalRoot hp hp1 ψ
          (sourceCanonicalRootGapPoint hp hp1 ψ n t + (y:ℂ)*I))
      (𝓝[Set.Iio 0] (0:ℝ))
      (𝓝 (deriv (canonicalDiscriminant hp (periodOnePotential ψ))
          (sourceCanonicalRootGapPoint hp hp1 ψ n t) /
        sourceCanonicalRootGapLowerValue hp hp1 ψ n t)) := by
  obtain ⟨W,_,hWreal,hlimits⟩ :=
    exists_global_sourceCriticalRootRatio_gapSideLimits hp hp1
  have hψ : ψ ∈ W := hWreal hreal
  have hgap := sourceCanonicalPeriodicGap_ne_zero_of_openRealGap
    hp hp1 ψ hreal n hopen
  exact (hlimits ψ hψ n t ht hgap).2.comp
    (sourceCanonicalRootGapPoint_vertical_tendsto_lowerSide
      hp hp1 ψ hreal n hopen t)

end NLS.ZakharovShabat
