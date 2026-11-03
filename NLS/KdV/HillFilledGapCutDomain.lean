import NLS.KdV.HillRealGapContourDiscs

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate unitInterval

namespace NLS.KdV



theorem mem_hillL2RealCutDomain_of_filled_not_gap
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (k : ℕ) (hk : 1 ≤ k)
    (z : ℂ) (hz : z ∈ hillGapFilledDomain q hq hr k)
    (hgap : z ∉ segment ℝ (hillRealLabels q hq hr (2*k-1) : ℂ)
      (hillRealLabels q hq hr (2*k) : ℂ)) : z ∈ hillL2RealCutDomain q hq hr := by
  by_cases hi : z.im ≠ 0
  · exact Or.inl hi
  · have hre : z = (z.re:ℂ) := by apply Complex.ext <;> simp [not_ne_iff.mp hi]
    have hbound := hz.resolve_left hi
    have hxnot : z.re ∉ Icc (hillRealLabels q hq hr (2*k-1)) (hillRealLabels q hq hr (2*k)) := by
      intro hx
      apply hgap
      rw [hre]
      exact ofReal_mem_ordered_segment _ _ _ (monotone_hillRealLabels q hq hr (by omega)) hx
    rcases lt_or_ge z.re (hillRealLabels q hq hr (2*k-1)) with hl | hl
    · refine Or.inr ⟨k-1,?_⟩
      rw [show 2*(k-1)+1 = 2*k-1 by omega,show 2*(k-1) = 2*k-2 by omega]
      exact ⟨hbound.1,hl⟩
    · exact Or.inr ⟨k,lt_of_not_ge (fun hu => hxnot ⟨hl,hu⟩),hbound.2⟩

theorem hillRealGapSegment_subset_intrinsic_contour_ball
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (k : ℕ) (hk : 1 ≤ k) :
    segment ℝ (hillRealLabels q hq hr (2*k-1) : ℂ) (hillRealLabels q hq hr (2*k) : ℂ) ⊆
      ball (hillRealGapCenter q hq hr k : ℂ)
        (hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k) := by
  obtain ⟨hd,hη,hl,hu,_⟩ := hillRealGapContour_geometry q hq hr k hk
  apply (convex_ball _ _).segment_subset
  · rw [← hl]
    simp only [mem_ball,dist_eq_norm,← ofReal_sub,norm_real,Real.norm_eq_abs]
    rw [show hillRealGapCenter q hq hr k-hillRealGapHalfLength q hq hr k-
      hillRealGapCenter q hq hr k = -hillRealGapHalfLength q hq hr k by ring,
      abs_neg,abs_of_nonneg hd]
    linarith
  · rw [← hu]
    simp only [mem_ball,dist_eq_norm,← ofReal_sub,norm_real,Real.norm_eq_abs,
      add_sub_cancel_left,abs_of_nonneg hd]
    linarith

end NLS.KdV
