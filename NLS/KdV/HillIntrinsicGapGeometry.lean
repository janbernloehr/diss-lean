import NLS.KdV.HillCubicKernelExterior
import NLS.ComplexAnalysis.FiniteCircleHoleDecomposition

/-! # Disjoint intrinsic Hill gap discs and actual finite-hole coverage -/

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV
variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

def hillIntrinsicGapRadius (k : ℕ) : ℝ :=
  hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k

def hillIntrinsicGapOuterRadius (k : ℕ) : ℝ :=
  hillRealGapHalfLength q hq hr k+(3/2:ℝ)*hillRealGapCollar q hq hr k

theorem hillIntrinsicGapRadii_bounds (k : ℕ) (hk : 1≤k) :
    0<hillIntrinsicGapRadius q hq hr k ∧
      hillIntrinsicGapRadius q hq hr k<hillIntrinsicGapOuterRadius q hq hr k ∧
      hillIntrinsicGapOuterRadius q hq hr k<hillRealGapHalfLength q hq hr k+2*hillRealGapCollar q hq hr k := by
  obtain ⟨hd,hη,_⟩ := hillRealGapContour_geometry q hq hr k hk
  dsimp only [hillIntrinsicGapRadius,hillIntrinsicGapOuterRadius]
  exact ⟨by linarith,by linarith,by linarith⟩

theorem hillGapSegment_subset_intrinsicBall (k : ℕ) (hk : 1≤k) :
    segment ℝ (hillRealLabels q hq hr (2*k-1):ℂ) (hillRealLabels q hq hr (2*k):ℂ)⊆
      ball (hillRealGapCenter q hq hr k : ℂ) (hillIntrinsicGapRadius q hq hr k) := by
  obtain ⟨hd,hη,hl,hu,_⟩ := hillRealGapContour_geometry q hq hr k hk
  apply (convex_ball _ _).segment_subset
  · rw [← hl]
    simp only [mem_ball,dist_eq_norm,← ofReal_sub,norm_real,Real.norm_eq_abs]
    rw [show hillRealGapCenter q hq hr k-hillRealGapHalfLength q hq hr k-hillRealGapCenter q hq hr k=
      -hillRealGapHalfLength q hq hr k by ring,abs_neg,abs_of_nonneg hd]
    exact lt_add_of_pos_right _ hη
  · rw [← hu]
    simp only [mem_ball,dist_eq_norm,← ofReal_sub,norm_real,Real.norm_eq_abs]
    rw [show hillRealGapCenter q hq hr k+hillRealGapHalfLength q hq hr k-hillRealGapCenter q hq hr k=
      hillRealGapHalfLength q hq hr k by ring,abs_of_nonneg hd]
    exact lt_add_of_pos_right _ hη

private theorem intrinsic_outer_disjoint_of_lt (k j : ℕ) (_hk : 1≤k) (hj : 1≤j) (hkj : k<j) :
    Disjoint (closedBall (hillRealGapCenter q hq hr k : ℂ) (hillIntrinsicGapOuterRadius q hq hr k))
      (closedBall (hillRealGapCenter q hq hr j : ℂ) (hillIntrinsicGapOuterRadius q hq hr j)) := by
  have hnext := hillRealLabels_band_strict q hq hr k
  have hnextj := monotone_hillRealLabels q hq hr (by omega : 2*k+1≤2*j-1)
  have hprev := monotone_hillRealLabels q hq hr (by omega : 2*k≤2*j-2)
  have hηk : hillRealGapCollar q hq hr k≤
      (hillRealLabels q hq hr (2*j-1)-hillRealLabels q hq hr (2*k))/4 := by
    have hm := min_le_right (hillRealLabels q hq hr (2*k-1)-hillRealLabels q hq hr (2*k-2))
      (hillRealLabels q hq hr (2*k+1)-hillRealLabels q hq hr (2*k))
    dsimp only [hillRealGapCollar]
    linarith
  have hηj : hillRealGapCollar q hq hr j≤
      (hillRealLabels q hq hr (2*j-1)-hillRealLabels q hq hr (2*k))/4 := by
    have hm := min_le_left (hillRealLabels q hq hr (2*j-1)-hillRealLabels q hq hr (2*j-2))
      (hillRealLabels q hq hr (2*j+1)-hillRealLabels q hq hr (2*j))
    dsimp only [hillRealGapCollar]
    linarith
  have hsep : hillRealGapCenter q hq hr k+hillIntrinsicGapOuterRadius q hq hr k<
      hillRealGapCenter q hq hr j-hillIntrinsicGapOuterRadius q hq hr j := by
    dsimp only [hillRealGapCenter,hillIntrinsicGapOuterRadius,hillRealGapHalfLength]
    linarith
  apply Set.disjoint_left.mpr
  intro E hEk hEj
  have hkN : ‖E-(hillRealGapCenter q hq hr k : ℂ)‖≤hillIntrinsicGapOuterRadius q hq hr k := by
    simpa only [mem_closedBall,dist_eq_norm] using hEk
  have hjN : ‖E-(hillRealGapCenter q hq hr j : ℂ)‖≤hillIntrinsicGapOuterRadius q hq hr j := by
    simpa only [mem_closedBall,dist_eq_norm] using hEj
  have hek := abs_le.mp ((abs_re_le_norm (E-(hillRealGapCenter q hq hr k : ℂ))).trans hkN)
  have hej := abs_le.mp ((abs_re_le_norm (E-(hillRealGapCenter q hq hr j : ℂ))).trans hjN)
  simp only [sub_re,ofReal_re] at hek hej
  linarith [hek.2,hej.1]

theorem hillIntrinsicGapOuterBalls_disjoint (k j : ℕ) (hk : 1≤k) (hj : 1≤j) (hne : k≠j) :
    Disjoint (closedBall (hillRealGapCenter q hq hr k : ℂ) (hillIntrinsicGapOuterRadius q hq hr k))
      (closedBall (hillRealGapCenter q hq hr j : ℂ) (hillIntrinsicGapOuterRadius q hq hr j)) := by
  rcases lt_or_gt_of_ne hne with hkj | hjk
  · exact intrinsic_outer_disjoint_of_lt q hq hr k j hk hj hkj
  · exact (intrinsic_outer_disjoint_of_lt q hq hr j k hj hk hjk).symm


/-- Avoiding a finite head of intrinsic gap balls leaves only the ground
cut, bands and closed tail points in the filled cubic domain. -/
theorem hillCubicFilledDomain_of_avoids_intrinsicBalls
    (n N : ℕ) (hn : 1≤n) (hnN : n≤N)
    (hclosed : ∀ (k : ℕ) (_hk : 1≤k), N<k → hillRealGapHalfLength q hq hr k=0)
    (E : ℂ) (havoid : ∀ k∈Finset.Icc 1 N,
      E∉ball (hillRealGapCenter q hq hr k : ℂ) (hillIntrinsicGapRadius q hq hr k)) :
    E∈hillCubicFilledDomain q hq hr n := by
  have hnot : E∉segment ℝ (hillRealLabels q hq hr (2*n-1):ℂ) (hillRealLabels q hq hr (2*n):ℂ) := by
    intro hs
    exact havoid n (Finset.mem_Icc.mpr ⟨hn,hnN⟩) (hillGapSegment_subset_intrinsicBall q hq hr n hn hs)
  refine ⟨?_,hnot⟩
  by_cases hi : E.im≠0
  · exact Or.inl (Or.inl hi)
  have hEC : E=(E.re:ℂ) := by apply Complex.ext <;> simp [not_ne_iff.mp hi]
  by_cases hground : E.re≤hillLowestEnergy q hq hr
  · exact Or.inr (Or.inl hground)
  have hx0 : hillLowestEnergy q hq hr<E.re := lt_of_not_ge hground
  by_cases hgap : ∃ k : ℕ, 1≤k ∧ E.re∈Icc (hillRealLabels q hq hr (2*k-1)) (hillRealLabels q hq hr (2*k))
  · obtain ⟨k,hk,hx⟩ := hgap
    by_cases hkN : k≤N
    · have hs : E∈segment ℝ (hillRealLabels q hq hr (2*k-1):ℂ) (hillRealLabels q hq hr (2*k):ℂ) := by
        rw [hEC]
        exact ofReal_mem_ordered_segment _ _ _ (monotone_hillRealLabels q hq hr (by omega)) hx
      exact False.elim (havoid k (Finset.mem_Icc.mpr ⟨hk,hkN⟩)
        (hillGapSegment_subset_intrinsicBall q hq hr k hk hs))
    have hh := hclosed k hk (lt_of_not_ge hkN)
    have hc : hillRealLabels q hq hr (2*k-1)=hillRealLabels q hq hr (2*k) := by
      dsimp only [hillRealGapHalfLength] at hh
      linarith
    exact Or.inr (Or.inr ⟨k,hk,hc,by linarith [hx.1,hx.2]⟩)
  · obtain ⟨M,hM⟩ := exists_hillRealLabels_band_upper_gt q hq hr E.re
    obtain ⟨k,_hk,hband⟩ := hillRealLabels_finite_band_cover q hq hr M E.re hx0 hM
      (fun k hk _hMk hx => hgap ⟨k,hk,hx⟩)
    exact Or.inl (Or.inr ⟨k,hband⟩)

/-- A finite head of the enlarged, pairwise disjoint intrinsic discs lies
inside every sufficiently large centered outer circle. -/
theorem exists_intrinsicOuterBalls_enclosed (N : ℕ) :
    ∃ R : ℝ, 0<R ∧ ∀ S : ℝ, R<S → ∀ k∈Finset.Icc 1 N,
      closedBall (hillRealGapCenter q hq hr k : ℂ) (hillIntrinsicGapOuterRadius q hq hr k)⊆ball (0:ℂ) S := by
  let f : ℕ → ℝ := fun k => ‖(hillRealGapCenter q hq hr k : ℂ)‖+|hillIntrinsicGapOuterRadius q hq hr k|+1
  let B := ∑ k∈Finset.Icc 1 N, f k
  have hB : 0≤B := Finset.sum_nonneg (fun _ _ => by dsimp only [f];positivity)
  refine ⟨B+1,by linarith,?_⟩
  intro S hS k hk E hE
  have hs : f k≤B := Finset.single_le_sum (fun _ _ => by dsimp only [f];positivity) hk
  have hnorm : ‖E-(hillRealGapCenter q hq hr k : ℂ)‖≤hillIntrinsicGapOuterRadius q hq hr k := by
    simpa only [mem_closedBall,dist_eq_norm] using hE
  have ht := norm_add_le (E-(hillRealGapCenter q hq hr k : ℂ)) (hillRealGapCenter q hq hr k : ℂ)
  rw [sub_add_cancel] at ht
  rw [mem_ball_zero_iff]
  dsimp only [f] at hs
  linarith [le_abs_self (hillIntrinsicGapOuterRadius q hq hr k)]

end NLS.KdV
