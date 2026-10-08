import NLS.ZakharovShabat.LinearWeightSpectralLocalization
import NLS.ZakharovShabat.DiskMultiplicity
import NLS.ZakharovShabat.PeriodicEndpointLabeling

/-! # Algebraic multiplicity at the quadratic localization threshold

A closed weighted norm ball connects the potential to zero while keeping
the quarter-spacing circle in the original resolvent set. Constancy of
contour rank gives algebraic count two, including collapsed root pairs.
-/
noncomputable section
open scoped Classical
namespace NLS.ZakharovShabat

/-- The quarter-spacing circle lies in the original resolvent set at the exact threshold. -/
theorem linearWeight_circle_subset_resolvent (w : SpectralWeight) (hw : w.HasLinearFactor)
    (C : ℝ) (hu : ∀ k : ℤ, w k ≤ C*(1+|(k:ℝ)|))
    (φ : WeightedCoeffPair w.toWeight 2) (n : ℤ) (hn : 8*‖φ‖^2 ≤ 1+|(n:ℝ)|) :
    Metric.sphere ((Real.pi:ℂ)*n) (Real.pi/4) ⊆
      resolventSet (by simp) (weightedBaseToPair w φ) := by
  intro z hz
  have hs : z ∈ resonantStrip n := closedBall_subset_resonantStrip n
    (by linarith [Real.pi_pos]) (Metric.sphere_subset_closedBall hz)
  have hnonzero := (linearWeight_determinant_zeroCount w hw φ n hn).2.1 z hz
  have hnot : z ∉ periodicSpectrum (by simp) (weightedBaseToPair w φ) := by
    intro hspec
    exact hnonzero ((mem_periodicSpectrum_iff_linearWeight_determinant_zero w hw C hu φ n hn z hs).mp hspec)
  exact not_not.mp hnot

/-- The original algebraic count is two, with no enlargement of the quadratic threshold. -/
theorem linearWeight_sum_enclosed_multiplicity_two (w : SpectralWeight) (hw : w.HasLinearFactor)
    (C : ℝ) (hu : ∀ k : ℤ, w k ≤ C*(1+|(k:ℝ)|))
    (φ : WeightedCoeffPair w.toWeight 2) (n : ℤ) (hn : 8*‖φ‖^2 ≤ 1+|(n:ℝ)|) :
    (∑ z ∈ enclosedPeriodicSpectrum (by simp) (weightedBaseToPair w φ) ((Real.pi:ℂ)*n) (Real.pi/4),
      periodicAlgebraicMultiplicity (by simp) (weightedBaseToPair w φ) z) = 2 := by
  let B : Set (WeightedCoeffPair w.toWeight 2) := Metric.closedBall 0 ‖φ‖
  let U : Set (PairSpace 2) := weightedBaseToPair w '' B
  have hU : IsPreconnected U :=
    (convex_closedBall (0 : WeightedCoeffPair w.toWeight 2) ‖φ‖).isPreconnected.image
      (weightedBaseToPair w) (weightedBaseToPair w).continuous.continuousOn
  have hφ : weightedBaseToPair w φ ∈ U := ⟨φ, by simp [B], rfl⟩
  have h0 : (0 : PairSpace 2) ∈ U := ⟨0, by simp [B], map_zero _⟩
  have hc : ∀ ψ ∈ U, Metric.sphere ((Real.pi:ℂ)*n) (Real.pi/4) ⊆ resolventSet (by simp) ψ := by
    rintro _ ⟨ψ,hψ,rfl⟩
    have hnorm : ‖ψ‖ ≤ ‖φ‖ := by simpa [B] using hψ
    have hψn : 8*‖ψ‖^2 ≤ 1+|(n:ℝ)| := by nlinarith [norm_nonneg ψ, norm_nonneg φ]
    exact linearWeight_circle_subset_resolvent w hw C hu ψ n hψn
  exact (sum_enclosed_multiplicity_eq_on_preconnected (by simp) _ _ (by positivity)
    hU hc hφ h0).trans (sum_enclosed_multiplicity_zero (by simp) n (by positivity)
      (by linarith [Real.pi_pos]))

/-- The original contour projection has rank two at the same explicit threshold. -/
theorem linearWeight_contour_rank_two (w : SpectralWeight) (hw : w.HasLinearFactor)
    (C : ℝ) (hu : ∀ k : ℤ, w k ≤ C*(1+|(k:ℝ)|))
    (φ : WeightedCoeffPair w.toWeight 2) (n : ℤ) (hn : 8*‖φ‖^2 ≤ 1+|(n:ℝ)|) :
    Module.finrank ℂ (resolventCircleIntegral (by simp) (weightedBaseToPair w φ)
      ((Real.pi:ℂ)*n) (Real.pi/4)).range = 2 := by
  rw [finrank_range_resolventCircleIntegral (by simp) _ _ _ (by positivity)
    (linearWeight_circle_subset_resolvent w hw C hu φ n hn)]
  exact linearWeight_sum_enclosed_multiplicity_two w hw C hu φ n hn

/-- The localized pair has the original algebraic multiplicities and exact determinant orders. -/
theorem linearWeight_exists_counted_periodicPair (w : SpectralWeight) (hw : w.HasLinearFactor)
    (C : ℝ) (hu : ∀ k : ℤ, w k ≤ C*(1+|(k:ℝ)|))
    (φ : WeightedCoeffPair w.toWeight 2) (n : ℤ) (hn : 8*‖φ‖^2 ≤ 1+|(n:ℝ)|) :
    ∃ x y : ℂ, PeriodicEndpointPair (by simp) (weightedBaseToPair w φ) n x y ∧
      (∀ z ∈ resonantStrip n,
        analyticOrderNatAt (resonantDeterminantExtension (by simp) w φ n) z =
          periodicAlgebraicMultiplicity (by simp) (weightedBaseToPair w φ) z) ∧
      ‖x-(Real.pi:ℂ)*n‖ ≤ quadraticLocalizationRadius ‖φ‖ n ∧
      ‖y-(Real.pi:ℂ)*n‖ ≤ quadraticLocalizationRadius ‖φ‖ n ∧
      ‖x-y‖^2 ≤ 6*resonantBProductSup (by simp) w φ n := by
  obtain ⟨x,hx,y,hy,_,_,hs,ha,hxl,hyl,hgap⟩ := linearWeight_exists_periodicRoots w hw C hu φ n hn
  have hc := linearWeight_sum_enclosed_multiplicity_two w hw C hu φ n hn
  exact ⟨x,y,⟨hx,hy,hs,periodicAlgebraicMultiplicity_eq_rootPair_count (by simp) _ n x y hx hy hs hc⟩,
    analyticOrderNatAt_eq_periodicAlgebraicMultiplicity_of_pair (by simp) w φ n x y hx hy hs hc ha,
    hxl,hyl,hgap⟩

/-- On the full strip, determinant analytic order equals original algebraic spectral multiplicity. -/
theorem linearWeight_analyticOrder_eq_periodicMultiplicity (w : SpectralWeight) (hw : w.HasLinearFactor)
    (C : ℝ) (hu : ∀ k : ℤ, w k ≤ C*(1+|(k:ℝ)|))
    (φ : WeightedCoeffPair w.toWeight 2) (n : ℤ) (hn : 8*‖φ‖^2 ≤ 1+|(n:ℝ)|)
    (z : ℂ) (hz : z ∈ resonantStrip n) :
    analyticOrderNatAt (resonantDeterminantExtension (by simp) w φ n) z =
      periodicAlgebraicMultiplicity (by simp) (weightedBaseToPair w φ) z := by
  obtain ⟨_,_,_,h,_,_,_⟩ := linearWeight_exists_counted_periodicPair w hw C hu φ n hn
  exact h z hz

end NLS.ZakharovShabat
