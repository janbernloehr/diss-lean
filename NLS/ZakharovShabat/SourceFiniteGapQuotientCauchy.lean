import NLS.ZakharovShabat.SourceFilledGapQuotientInfinity
import NLS.ComplexAnalysis.CauchyFiniteHoles
import NLS.ComplexAnalysis.CauchyOuterLimit

/-! # The finite-gap quotient as exterior Cauchy contours

The selected gap is filled, the remaining open-gap discs form finitely
many holes, and normalization at infinity supplies the outer constant.
-/

noncomputable section
open Set Metric Filter Topology Complex MeasureTheory NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
variable (C : SourceFullAbelianUniformCauchyFamily hp hp1 W)

/-- The actual filled quotient is analytic outside the finitely many exterior open-gap discs. -/
theorem filledGapQuotient_analytic_finiteHoleDomain (n : ℤ)
    (φ : realTypeSourceSubmodule p) (hφ : φ.val ∈ ball C.discs.source.val C.discs.sourceRadius)
    (hf : φ ∈ sourceFiniteGapLocus hp hp1) (R : ℝ) :
    AnalyticOnNhd ℂ (C.filledGapQuotient n φ.val)
      (circleHoleDomain 0 R (hf.toFinset.erase n) C.discs.center C.discs.inner) := by
  intro z hz
  apply C.filledGapQuotient_analytic n φ hφ z
  by_cases hb : z ∈ ball (C.discs.center n) (C.discs.outer n)
  · exact Or.inr hb
  · refine Or.inl ⟨?_,fun hs => hb (C.segment_subset_outer n φ.val hφ hs)⟩
    intro m hm hzm
    by_cases hmn : m=n
    · subst m
      exact hb (C.segment_subset_outer n φ.val hφ hzm)
    · exact hz.2 m (Finset.mem_erase.mpr ⟨hmn,hf.mem_toFinset.mpr hm⟩)
        (C.discs.segment_subset φ.val hφ m hzm)

/-- The actual finite-gap quotient satisfies the finite-hole Cauchy value formula. -/
theorem filledGapQuotient_cauchy_finite_holes (n : ℤ)
    (φ : realTypeSourceSubmodule p) (hφ : φ.val ∈ ball C.discs.source.val C.discs.sourceRadius)
    (hf : φ ∈ sourceFiniteGapLocus hp hp1) (x : ℂ)
    (hx : x ∈ ball (C.discs.center n) (C.discs.outer n))
    (R : ℝ) (hR : 0 ≤ R) (hxR : x ∈ ball 0 R)
    (henclosed : ∀ m ∈ hf.toFinset.erase n,
      closedBall (C.discs.center m) ((C.discs.inner m+C.discs.outer m)/2) ⊆ ball 0 R) :
    (2*(Real.pi:ℂ)*I)*C.filledGapQuotient n φ.val x =
      (∮ z in C(0,R), C.filledGapQuotient n φ.val z/(z-x)) -
        ∑ m ∈ hf.toFinset.erase n, ∮ z in C(C.discs.center m,C.discs.inner m),
          C.filledGapQuotient n φ.val z/(z-x) := by
  let ρ : ℤ → ℝ := fun m => (C.discs.inner m+C.discs.outer m)/2
  have hi (m : ℤ) : C.discs.inner m < ρ m := by dsimp [ρ]; linarith [C.discs.inner_lt m]
  have ho (m : ℤ) : ρ m < C.discs.outer m := by dsimp [ρ]; linarith [C.discs.inner_lt m]
  apply circleIntegral_cauchy_value_of_finite_holes 0 R hR (hf.toFinset.erase n)
    C.discs.center C.discs.inner ρ (C.filledGapQuotient n φ.val)
    (fun m _ => C.discs.inner_pos m) (fun m _ => hi m) henclosed
    (fun m _ j _ hmj => (C.discs.disjoint m j hmj).mono
      (closedBall_subset_ball (ho m)) (closedBall_subset_ball (ho j)))
    (C.filledGapQuotient_analytic_finiteHoleDomain n φ hφ hf R) x hxR
  intro m hm hxm
  exact Set.disjoint_left.mp (C.discs.disjoint n m (Finset.mem_erase.mp hm).1.symm) hx
    (closedBall_subset_ball (C.discs.inner_lt m) hxm)

/-- The finite-gap quotient equals one minus the finite sum of its exterior Cauchy contours. -/
theorem filledGapQuotient_eq_one_sub_finite_contours (n : ℤ)
    (φ : realTypeSourceSubmodule p) (hφ : φ.val ∈ ball C.discs.source.val C.discs.sourceRadius)
    (hf : φ ∈ sourceFiniteGapLocus hp hp1) (x : ℂ)
    (hx : x ∈ ball (C.discs.center n) (C.discs.outer n)) :
    (2*(Real.pi:ℂ)*I)*C.filledGapQuotient n φ.val x =
      2*(Real.pi:ℂ)*I -
        ∑ m ∈ hf.toFinset.erase n, ∮ z in C(C.discs.center m,C.discs.inner m),
          C.filledGapQuotient n φ.val z/(z-x) := by
  classical
  let s := hf.toFinset.erase n
  let ρ : ℤ → ℝ := fun m => (C.discs.inner m+C.discs.outer m)/2
  have hi (m : ℤ) : C.discs.inner m < ρ m := by dsimp [ρ]; linarith [C.discs.inner_lt m]
  have hcompact : IsCompact (⋃ m ∈ s, closedBall (C.discs.center m) (ρ m)) :=
    s.finite_toSet.isCompact_biUnion fun m _ => isCompact_closedBall _ _
  obtain ⟨B,hB⟩ := hcompact.isBounded.exists_norm_le
  have henc (R : ℝ) (hR : B < R) (m : ℤ) (hm : m ∈ s) :
      closedBall (C.discs.center m) (ρ m) ⊆ ball 0 R := by
    intro z hz
    rw [mem_ball,dist_zero_right]
    exact (hB z (mem_iUnion₂.mpr ⟨m,hm,hz⟩)).trans_lt hR
  have hcont : ∀ᶠ R : ℝ in atTop, ContinuousOn (C.filledGapQuotient n φ.val) (sphere (0:ℂ) R) := by
    filter_upwards [eventually_gt_atTop B] with R hR
    apply (C.filledGapQuotient_analytic_finiteHoleDomain n φ hφ hf R).continuousOn.mono
    intro z hz
    refine ⟨sphere_subset_closedBall hz,?_⟩
    intro m hm hzm
    exact sphere_disjoint_ball.le_bot ⟨hz,henc R hR m hm
      ((closedBall_subset_closedBall (hi m).le) (ball_subset_closedBall hzm))⟩
  have hlim := (tendsto_outerCircle_cauchy_of_limit_one _ x
    (C.filledGapQuotient_tendsto_one_finiteGap n φ hφ hf) hcont).sub_const
      (∑ m ∈ s, ∮ z in C(C.discs.center m,C.discs.inner m), C.filledGapQuotient n φ.val z/(z-x))
  have hevent : ∀ᶠ R : ℝ in atTop,
      (∮ z in C(0,R), C.filledGapQuotient n φ.val z/(z-x)) -
        (∑ m ∈ s, ∮ z in C(C.discs.center m,C.discs.inner m), C.filledGapQuotient n φ.val z/(z-x)) =
        (2*(Real.pi:ℂ)*I)*C.filledGapQuotient n φ.val x := by
    filter_upwards [eventually_gt_atTop (max B (max ‖x‖ 0))] with R hR
    have hBR := (le_max_left B _).trans_lt hR
    have hxR := (le_max_left ‖x‖ 0).trans_lt ((le_max_right B _).trans_lt hR)
    have hR0 := (le_max_right ‖x‖ 0).trans_lt ((le_max_right B _).trans_lt hR)
    exact (C.filledGapQuotient_cauchy_finite_holes n φ hφ hf x hx R hR0.le
      (by simpa only [mem_ball,dist_zero_right] using hxR) (henc R hBR)).symm
  apply tendsto_nhds_unique _ hlim
  apply tendsto_const_nhds.congr'
  filter_upwards [hevent] with R hR
  exact hR.symm

end NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily
