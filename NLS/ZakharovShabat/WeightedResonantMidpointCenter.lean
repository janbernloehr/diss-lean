import NLS.ZakharovShabat.ResonantMidpointCenter
import NLS.ZakharovShabat.WeightedResonantDiagonalCenter
import NLS.ZakharovShabat.PeriodicRootSequence

/-!
# Midpoint-center comparison for the actual periodic spectrum

The original algebraic multiplicities identify each counted pair with
zeros of the actual resonant determinant. A repeated endpoint has order
two and hence vanishing determinant derivative. The resulting product
bound applies to the intrinsic trace midpoint on one source neighborhood.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual counted pair supplies the zero and double-root hypotheses. -/
theorem PeriodicResonantPair.midpoint_center_bound {hp : p ≠ ⊤} {w : SpectralWeight}
    {φ : WeightedCoeffPair w.toWeight p} {n : ℤ} {x y : ℂ}
    (hpair : PeriodicResonantPair hp w φ n x y)
    (hdom : ∀ z ∈ resonantStrip n, (φ,z) ∈ weightedCorrectionDomain hp w n)
    (hb : ∀ z ∈ resonantStrip n,
      ‖weightedResonantAExtension hp w φ n z‖ ≤ Real.pi/32 ∧
      ‖weightedResonantBMinusExtension hp w φ n z‖ ≤ Real.pi/16 ∧
      ‖weightedResonantBPlusExtension hp w φ n z‖ ≤ Real.pi/16) :
    ‖(x+y)/2-weightedResonantDiagonalCenter hp w φ n‖ ≤
      (8*Real.pi⁻¹)*resonantBProductSup hp w φ n := by
  let a := weightedResonantAExtension hp w φ n
  let b := fun z => weightedResonantBPlusExtension hp w φ n z*weightedResonantBMinusExtension hp w φ n z
  have ha : AnalyticOnNhd ℂ a (resonantStrip n) := fun z hz =>
    (analyticAt_weightedResonantAExtension hp w n (φ,z) (hdom z hz)).comp
      (analyticAt_const.prod analyticAt_id)
  have hbp : AnalyticOnNhd ℂ (weightedResonantBPlusExtension hp w φ n) (resonantStrip n) := fun z hz =>
    (analyticAt_weightedResonantBPlusExtension hp w n (φ,z) (hdom z hz)).comp
      (analyticAt_const.prod analyticAt_id)
  have hbm : AnalyticOnNhd ℂ (weightedResonantBMinusExtension hp w φ n) (resonantStrip n) := fun z hz =>
    (analyticAt_weightedResonantBMinusExtension hp w n (φ,z) (hdom z hz)).comp
      (analyticAt_const.prod analyticAt_id)
  have hb' : AnalyticOnNhd ℂ b (resonantStrip n) := fun z hz => (hbp z hz).mul (hbm z hz)
  have hsup := resonantBProductSup_bounds hp w φ n (fun z hz => (hb z hz).2)
  have hc := weightedResonantDiagonalCenter_spec hp w φ n ha (fun z hz => (hb z hz).1)
  have hx := refinedResonantDisk_subset_strip n hpair.left_mem
  have hy := refinedResonantDisk_subset_strip n hpair.right_mem
  have horder (z : ℂ) (hz : z ∈ resonantStrip n) :
      analyticOrderNatAt (resonantDeterminantExtension hp w φ n) z = ({x,y}:Multiset ℂ).count z :=
    (hpair.analyticOrder_eq_multiplicity z hz).trans (hpair.multiplicity_eq_count z hz)
  have hx0 : resonantDeterminantExtension hp w φ n x = 0 :=
    apply_eq_zero_of_analyticOrderNatAt_ne_zero (by rw [horder x hx]; simp)
  have hy0 : resonantDeterminantExtension hp w φ n y = 0 :=
    apply_eq_zero_of_analyticOrderNatAt_ne_zero (by rw [horder y hy]; simp)
  have hdouble : x = y → deriv (resonantDeterminantExtension hp w φ n) x = 0 := by
    intro hxy
    by_contra hne
    have hsimple := (analyticAt_resonantDeterminantExtension_spectral hp w φ n x (hdom x hx)).analyticOrderAt_eq_one_of_zero_deriv_ne_zero hx0 hne
    have hone : analyticOrderNatAt (resonantDeterminantExtension hp w φ n) x = 1 := by
      simp [analyticOrderNatAt,hsimple]
    have htwo : analyticOrderNatAt (resonantDeterminantExtension hp w φ n) x = 2 := by
      rw [horder x hx]
      simp [← hxy]
    omega
  exact norm_resonant_midpoint_sub_center_le n a b _ ha (fun z hz => (hb z hz).1) hb'
    hsup.2.2 x y _ hpair.left_mem hpair.right_mem hc.1 hc.2.2.1
    (sub_eq_zero.mp hx0) (sub_eq_zero.mp hy0) hdouble

/-- One weighted neighborhood supplies an actual counted pair and the midpoint-center estimate. -/
theorem exists_uniform_weightedMidpointCenterBound (hp : p ≠ ⊤) (hp1 : 1 < p)
    (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight p) :
    ∃ N : ℕ, 2 ≤ N ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p), IsOpen U ∧ φ ∈ U ∧
      ∀ ψ ∈ U, ∀ n : ℤ, N ≤ n.natAbs →
        ∃ x y : ℂ, PeriodicResonantPair hp w ψ n x y ∧
          ‖(x+y)/2-weightedResonantDiagonalCenter hp w ψ n‖ ≤
            (8*Real.pi⁻¹)*resonantBProductSup hp w ψ n := by
  obtain ⟨N₁,hN₁,U₁,ho₁,_,hφ₁,_,h₁⟩ := exists_uniform_resonantDeterminant_control hp hp1 w φ
  obtain ⟨N₂,_,U₂,ho₂,_,hφ₂,_,h₂⟩ := exists_uniform_periodicRoots_with_power_sums hp hp1 w φ
  refine ⟨max N₁ N₂,hN₁.trans (le_max_left _ _),U₁ ∩ U₂,ho₁.inter ho₂,⟨hφ₁,hφ₂⟩,?_⟩
  intro ψ hψ n hn
  obtain ⟨ξ,η,hpair,_⟩ := h₂ ψ hψ.2
  have hp' := hpair n (by omega)
  exact ⟨ξ n,η n,hp',hp'.midpoint_center_bound
    (fun z hz => (h₁ n (by omega)).1 ⟨hψ.1,hz⟩)
    (fun z hz => ((h₁ n (by omega)).2 ψ hψ.1 z hz).2)⟩

/-- The intrinsic trace midpoint obeys the same bound at all distant indices. -/
theorem exists_uniform_periodicMidpoint_center_bound (hp : p ≠ ⊤) (hp1 : 1 < p)
    (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight p) :
    ∃ N : ℕ, 2 ≤ N ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p), IsOpen U ∧ φ ∈ U ∧
      ∀ ψ ∈ U, ∀ n : ℤ, N ≤ n.natAbs →
        ‖periodicMidpoint hp (weightedBaseToPair w ψ) n-weightedResonantDiagonalCenter hp w ψ n‖ ≤
          (8*Real.pi⁻¹)*resonantBProductSup hp w ψ n := by
  obtain ⟨N,hN,U,ho,hφ,h⟩ := exists_uniform_weightedMidpointCenterBound hp hp1 w φ
  refine ⟨N,hN,U,ho,hφ,?_⟩
  intro ψ hψ n hn
  obtain ⟨x,y,hpair,hb⟩ := h ψ hψ n hn
  simpa only [hpair.midpoint_eq] using hb

end NLS.ZakharovShabat
