import NLS.ZakharovShabat.SmallCompleteDisplacements
import NLS.ZakharovShabat.UniformExteriorResolvent

/-!
# Locally small absolute relative-displacement sums

For each tolerance and separation radius, one potential neighborhood and one
spectral threshold control both complete actual spectral sequences. The bound
holds at every exterior spectral parameter and does not require continuous
choices of root labels.
-/

noncomputable section
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The absolute relative-displacement sum is the scalar resolvent's lp-one norm. -/
theorem tsum_norm_relativeDisplacement_eq_resolvent_norm (hp : p ≠ ⊤) (ξ : ℤ → ℂ)
    (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p) (z : ℂ) (hz : z ∉ freeLattice) :
    (∑' n : ℤ, ‖(ξ n-(Real.pi : ℂ)*n)/(z-(Real.pi : ℂ)*n)‖) =
      ‖scalarResolventToL1 hp z hz (⟨_,hξ⟩ : Coeff p)‖ := by
  simp only [lp.norm_eq_tsum_rpow (by norm_num : (0 : ℝ) < (1 : ℝ≥0∞).toReal),
    ENNReal.toReal_one, one_div, inv_one, Real.rpow_one, scalarResolventToL1_apply]

/-- Both actual relative-displacement sums are uniformly small near a fixed potential at exterior infinity. -/
theorem exists_uniform_small_exteriorDisplacements (hp : p ≠ ⊤) (hp1 : 1 < p)
    (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight p)
    {r : ℝ} (hr : 0 < r) (hrπ : r ≤ Real.pi/4) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, 2 ≤ N ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧ ∃ R : ℝ, ∀ ψ ∈ U,
        weightedBaseToPair w ψ ∈ pairParitySubspace 0 →
        ∃ ξ η : ℤ → ℂ, CompletePeriodicParityPairs hp w ψ N ξ η ∧
          ∀ z : ℂ, R ≤ ‖z‖ → (∀ n : ℤ, r ≤ ‖z-(Real.pi : ℂ)*n‖) →
            (∑' n : ℤ, ‖(ξ n-(Real.pi : ℂ)*n)/(z-(Real.pi : ℂ)*n)‖) ≤ ε ∧
            (∑' n : ℤ, ‖(η n-(Real.pi : ℂ)*n)/(z-(Real.pi : ℂ)*n)‖) ≤ ε := by
  let C := max 1 (WeightedCoeff.sobolevEmbeddingConstant p hp/r)
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  let δ := ε/(2*C)
  have hδ : 0 < δ := div_pos hε (mul_pos (by norm_num) hC)
  obtain ⟨N, hN, U, ho, hconv, hφ, h0, B, _, hdata⟩ :=
    exists_uniform_small_completeDisplacements hp hp1 w φ hδ
  obtain ⟨R, hR⟩ := exists_threshold_scalarResolvent_small_tail hp (Finset.Icc (-(N : ℤ)) N) B
    (half_pos hε) hr hrπ
  refine ⟨N, hN, U, ho, hconv, hφ, h0, R, ?_⟩
  intro ψ hψ heven
  obtain ⟨ξ, η, h, hbξ, hbη, ht⟩ := hdata ψ hψ heven
  refine ⟨ξ, η, h, ?_⟩
  intro z hz hsep
  have hzfree := notMem_freeLattice_of_separated hr hsep
  have bound (a : Coeff p) (ha : ‖a‖ ≤ B)
      (ht : ‖a-Coeff.truncate (Finset.Icc (-(N : ℤ)) N) a‖ ≤ δ) :
      ‖scalarResolventToL1 hp z hzfree a‖ ≤ ε := by
    apply (hR z hz hsep a ha).trans
    calc
      _ ≤ ε/2+C*‖a-Coeff.truncate (Finset.Icc (-(N : ℤ)) N) a‖ := by
        gcongr
        exact le_max_right _ _
      _ ≤ ε/2+C*δ := add_le_add le_rfl (mul_le_mul_of_nonneg_left ht hC.le)
      _ = ε := by dsimp [δ]; field_simp; ring
  rw [tsum_norm_relativeDisplacement_eq_resolvent_norm hp ξ h.left_displacement z hzfree,
    tsum_norm_relativeDisplacement_eq_resolvent_norm hp η h.right_displacement z hzfree]
  exact ⟨bound _ hbξ (ht N le_rfl).1, bound _ hbη (ht N le_rfl).2⟩

end NLS.ZakharovShabat
