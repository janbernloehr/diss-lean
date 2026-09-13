import NLS.ZakharovShabat.UniformGapMajorant
import NLS.ZakharovShabat.RootDisplacementSequence

/-!
# Simultaneous displacement and weighted gap summability

The same two root sequences realize the exact analytic multiplicities and
both quantitative tails, on a common open convex neighborhood. Gap estimates
are invariant under exchanging the two roots; no continuous labeling or
identification with spectral algebraic multiplicities is assumed.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Weighted root-gap powers on the full signed high-frequency tail. -/
def rootGapPowerTail (p : ℝ≥0∞) (w : SpectralWeight) (N : ℕ) (ξ η : ℤ → ℂ) (n : ℤ) : ℝ :=
  if N ≤ n.natAbs then (w (2*n)*‖ξ n-η n‖)^p.toReal else 0

/-- The weighted norm power agrees with the source's product of powers. -/
theorem rootGapPowerTail_eq (p : ℝ≥0∞) (w : SpectralWeight) (N : ℕ) (ξ η : ℤ → ℂ) (n : ℤ) :
    rootGapPowerTail p w N ξ η n =
      if N ≤ n.natAbs then (w (2*n))^p.toReal * ‖ξ n-η n‖^p.toReal else 0 := by
  unfold rootGapPowerTail
  rw [Real.mul_rpow (zero_le_one.trans (w.one_le _)) (norm_nonneg _)]

/-- Interchanging the roots at every mode preserves the gap tail. -/
theorem rootGapPowerTail_swap (p : ℝ≥0∞) (w : SpectralWeight) (N : ℕ) (ξ η : ℤ → ℂ) :
    rootGapPowerTail p w N ξ η = rootGapPowerTail p w N η ξ := by
  funext n
  simp only [rootGapPowerTail, norm_sub_rev]

/-- A summable common majorant bounds the actual weighted gap series. -/
theorem rootGapPowerTail_summable_and_le (p : ℝ≥0∞) (w : SpectralWeight) (N : ℕ) (ξ η : ℤ → ℂ)
    (M : ℤ → ℝ) (hs : Summable (fun n : ℤ => if N ≤ n.natAbs then M n else 0))
    (hb : ∀ n : ℤ, N ≤ n.natAbs → (w (2*n)*‖ξ n-η n‖)^p.toReal ≤ M n) :
    Summable (rootGapPowerTail p w N ξ η) ∧
      (∑' n : ℤ, rootGapPowerTail p w N ξ η n) ≤ ∑' n : ℤ, if N ≤ n.natAbs then M n else 0 := by
  have hw (n : ℤ) : 0 ≤ w (2*n) := zero_le_one.trans (w.one_le _)
  have hn (n : ℤ) : 0 ≤ rootGapPowerTail p w N ξ η n := by
    unfold rootGapPowerTail
    split_ifs
    · exact Real.rpow_nonneg (mul_nonneg (hw n) (norm_nonneg _)) _
    · exact le_rfl
  have hh (n : ℤ) : rootGapPowerTail p w N ξ η n ≤ (if N ≤ n.natAbs then M n else 0) := by
    unfold rootGapPowerTail
    split_ifs with h
    · exact hb n h
    · exact le_rfl
  have hactual := hs.of_nonneg_of_le hn hh
  exact ⟨hactual,hactual.tsum_le_tsum hh hs⟩

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The same two roots have exact analytic multiplicities and both corrected convergent power tails. -/
theorem exists_uniform_resonantRoots_with_power_sums (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧ ∀ ψ ∈ U,
        ∃ ξ η : ℤ → ℂ,
          (∀ n : ℤ, N₀ ≤ n.natAbs →
            ξ n ∈ refinedResonantDisk n ∧ η n ∈ refinedResonantDisk n ∧
            resonantDeterminantExtension hp w ψ n (ξ n) = 0 ∧
            resonantDeterminantExtension hp w ψ n (η n) = 0 ∧
            (∀ z ∈ resonantStrip n, resonantDeterminantExtension hp w ψ n z = 0 ↔ z = ξ n ∨ z = η n) ∧
            (∀ z ∈ resonantStrip n, analyticOrderNatAt (resonantDeterminantExtension hp w ψ n) z =
              ({ξ n,η n} : Multiset ℂ).count z) ∧
            ‖ξ n-(Real.pi : ℂ)*n‖ ≤ 3*Real.pi/32 ∧ ‖η n-(Real.pi : ℂ)*n‖ ≤ 3*Real.pi/32 ∧
            ‖ξ n-η n‖^2 ≤ 6*resonantBProductSup hp w ψ n) ∧
          ∀ N : ℕ, N₀ ≤ N → Summable (rootDisplacementPowerTail p N ξ η) ∧
            (∑' n : ℤ, rootDisplacementPowerTail p N ξ η n) ≤ rootDisplacementBudget w ψ N ∧
            Summable (rootGapPowerTail p w N ξ η) ∧
            (∑' n : ℤ, rootGapPowerTail p w N ξ η n) ≤ rootGapBudget w ψ N := by
  obtain ⟨N₁,hN₁,U₁,ho₁,hc₁,hφ₁,h0₁,hroots⟩ := exists_uniform_resonantRoots_with_displacement_sum hp hp1 w φ
  obtain ⟨N₂,_,U₂,ho₂,hc₂,hφ₂,h0₂,hmajorant⟩ := exists_uniform_resonantGapMajorant hp hp1 w φ
  refine ⟨max N₁ N₂,hN₁.trans (le_max_left _ _),U₁ ∩ U₂,ho₁.inter ho₂,hc₁.inter hc₂,
    ⟨hφ₁,hφ₂⟩,⟨h0₁,h0₂⟩,?_⟩
  intro ψ hψ
  obtain ⟨ξ,η,hdata,hdisp⟩ := hroots ψ hψ.1
  refine ⟨ξ,η,(fun n hn => hdata n (by omega)),?_⟩
  intro N hN
  have hmaj := hmajorant ψ hψ.2 N (by omega)
  have hbound (n : ℤ) (hn : N ≤ n.natAbs) :
      (w (2*n)*‖ξ n-η n‖)^p.toReal ≤ resonantGapMajorant hp w ψ n := by
    have hr := hdata n (by omega)
    exact hmaj.2.2 n hn (ξ n) (refinedResonantDisk_subset_strip n hr.1)
      (η n) (refinedResonantDisk_subset_strip n hr.2.1) hr.2.2.1 hr.2.2.2.1
  obtain ⟨hs,hb⟩ := rootGapPowerTail_summable_and_le p w N ξ η
    (resonantGapMajorant hp w ψ) hmaj.1 hbound
  exact ⟨(hdisp N (by omega)).1,(hdisp N (by omega)).2,hs,hb.trans hmaj.2.1⟩

end NLS.ZakharovShabat
