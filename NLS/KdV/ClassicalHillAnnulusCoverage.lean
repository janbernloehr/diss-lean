import NLS.KdV.ClassicalHillSmallGapCoverage

/-! # High annuli belong to the actual source-continuation domain

Compactness makes the small-root confinement uniform along every source
segment of nearby complex potentials. Thus the actual normalized primitive
is defined on the whole high annulus, not only its outer circle.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex NLS.LinearVolterra NLS.ComplexAnalysis
namespace NLS.KdV

theorem exists_classicalHill_small_gap_coverage_near_compact
    (K : Set (Curve ℂ)) (hK : IsCompact K)
    (r : ℝ) (hr : 0 < r) (hrpi : r ≤ Real.pi/4) :
    ∃ N : ℕ, ∃ V : Set (Curve ℂ), 0 < N ∧ IsOpen V ∧ K ⊆ V ∧
      ∀ a ∈ V, ∀ n : ℤ, N ≤ n.natAbs →
        ∀ z ∈ closedBall ((Real.pi : ℂ)*n) (Real.pi/4),
          classicalHillRadicand (z^2,a) = 0 → z ∈ ball ((Real.pi : ℂ)*n) r := by
  classical
  have hl (q : K) := exists_classicalHill_small_gap_coverage q.val r hr hrpi
  choose N V hN hV hqV hd using hl
  obtain ⟨S,hS⟩ := hK.elim_finite_subcover V hV
    (fun q hq => mem_iUnion.mpr ⟨⟨q,hq⟩,hqV ⟨q,hq⟩⟩)
  refine ⟨1+∑ q ∈ S, N q,⋃ q ∈ S, V q,by omega,
    isOpen_iUnion (fun q => isOpen_iUnion (fun _ => hV q)),hS,?_⟩
  intro a ha n hn z hz hzero
  obtain ⟨q,hq⟩ := mem_iUnion.mp ha
  obtain ⟨hqS,haV⟩ := mem_iUnion.mp hq
  have hNq : N q ≤ ∑ b ∈ S, N b := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hqS
  exact hd q a haV n (by omega) z hz hzero

theorem exists_classicalHill_source_small_gap_coverage
    (q : Curve ℂ) (r : ℝ) (hr : 0 < r) (hrpi : r ≤ Real.pi/4) :
    ∃ N : ℕ, ∃ V : Set (Curve ℂ), 0 < N ∧ IsOpen V ∧ q ∈ V ∧
      ∀ a ∈ V, ∀ s ∈ Icc (0 : ℝ) 1, ∀ n : ℤ, N ≤ n.natAbs →
        ∀ z ∈ closedBall ((Real.pi : ℂ)*n) (Real.pi/4),
          classicalHillRadicand (z^2,(s : ℂ) • a) = 0 → z ∈ ball ((Real.pi : ℂ)*n) r := by
  let K : Set (Curve ℂ) := (fun s : ℝ => (s : ℂ) • q) '' Icc (0 : ℝ) 1
  have hK : IsCompact K := isCompact_Icc.image (by fun_prop)
  obtain ⟨N,U,hN,hU,hKU,hd⟩ :=
    exists_classicalHill_small_gap_coverage_near_compact K hK r hr hrpi
  let D : Set (ℂ × Curve ℂ) := univ ×ˢ U
  let V : Set (Curve ℂ) := (fun a => ((0 : ℂ),a)) ⁻¹' sourceSegmentDomain 0 D
  have hV : IsOpen V := (isOpen_sourceSegmentDomain 0 D (isOpen_univ.prod hU)).preimage
    (continuous_const.prodMk continuous_id)
  have hqV : q ∈ V := by
    intro s hs
    exact ⟨mem_univ _,by simpa only [sourceSegmentMap,zero_add,sub_zero] using hKU ⟨s,hs,rfl⟩⟩
  refine ⟨N,V,hN,hV,hqV,?_⟩
  intro a ha s hs n hn z hz hzero
  have haU : (s : ℂ) • a ∈ U := by
    simpa only [sourceSegmentMap,zero_add,sub_zero] using (ha s hs).2
  exact hd _ haU n hn z hz hzero

/-- An arbitrary prescribed positive inner radius works, with one
complex neighborhood and cutoff before all potentials, indices and points. -/
theorem exists_classicalHill_high_annulus_neighborhood
    (q : Curve ℂ) (r : ℝ) (hr : 0 < r) (hrpi : r ≤ Real.pi/4) :
    ∃ N : ℕ, ∃ V : Set (Curve ℂ), 0 < N ∧ IsOpen V ∧ q ∈ V ∧
      ∀ a ∈ V, ∀ n : ℕ+, N ≤ (n : ℕ) →
        ∀ z ∈ closedBall ((Real.pi : ℂ)*(n : ℕ)) (Real.pi/4),
          r ≤ ‖z-(Real.pi : ℂ)*(n : ℕ)‖ → (z^2,a) ∈ classicalHillContinuationDomain := by
  obtain ⟨N,V,hN,hV,hq,hsmall⟩ := exists_classicalHill_source_small_gap_coverage q r hr hrpi
  refine ⟨N,V,hN,hV,hq,?_⟩
  intro a ha n hn z hz hfar s hs
  have hne : classicalHillRadicand (z^2,(s : ℂ) • a) ≠ 0 := by
    intro he
    have hh := hsmall a ha s hs (n : ℤ) (by simpa only [Int.natAbs_natCast] using hn) z
      (by simpa only [Int.cast_natCast] using hz) he
    have hh' : ‖z-(Real.pi : ℂ)*(n : ℕ)‖ < r := by
      simpa only [mem_ball,dist_eq_norm,Int.cast_natCast] using hh
    linarith
  simp only [sourceSegmentMap,zero_add,sub_zero]
  exact ⟨sq_mem_slitPlane_of_high_closedBall n n.property z hz,hne⟩

end NLS.KdV
