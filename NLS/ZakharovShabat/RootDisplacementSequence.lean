import NLS.ZakharovShabat.UniformDisplacementMajorant
import NLS.ZakharovShabat.ResonantRoots

/-!
# Corrected locally uniform root-displacement summability

The two roots are selected with their actual analytic multiplicities.
Their displacement power tails are genuine convergent sums and obey the
corrected quantitative bound for every larger cutoff. No continuous root
labeling, distinctness, or reality assumption is imposed.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Both root displacement powers on the full signed high-frequency tail. -/
def rootDisplacementPowerTail (p : ℝ≥0∞) (N : ℕ) (ξ η : ℤ → ℂ) (n : ℤ) : ℝ :=
  if N ≤ n.natAbs then ‖ξ n-(Real.pi : ℂ)*n‖^p.toReal + ‖η n-(Real.pi : ℂ)*n‖^p.toReal else 0

/-- A summable common majorant controls every pair of root selections. -/
theorem rootDisplacementPowerTail_summable_and_le (p : ℝ≥0∞) (N : ℕ) (ξ η : ℤ → ℂ)
    (M : ℤ → ℝ) (hs : Summable (fun n : ℤ => if N ≤ n.natAbs then M n else 0))
    (hb : ∀ n : ℤ, N ≤ n.natAbs →
      ‖ξ n-(Real.pi : ℂ)*n‖^p.toReal + ‖η n-(Real.pi : ℂ)*n‖^p.toReal ≤ M n) :
    Summable (rootDisplacementPowerTail p N ξ η) ∧
      (∑' n : ℤ, rootDisplacementPowerTail p N ξ η n) ≤ ∑' n : ℤ, if N ≤ n.natAbs then M n else 0 := by
  have hnonneg (n : ℤ) : 0 ≤ rootDisplacementPowerTail p N ξ η n := by
    unfold rootDisplacementPowerTail
    split_ifs <;> positivity
  have hpoint (n : ℤ) : rootDisplacementPowerTail p N ξ η n ≤ (if N ≤ n.natAbs then M n else 0) := by
    unfold rootDisplacementPowerTail
    split_ifs with hn
    · exact hb n hn
    · exact le_rfl
  have hactual := hs.of_nonneg_of_le hnonneg hpoint
  exact ⟨hactual,hactual.tsum_le_tsum hpoint hs⟩

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Corrected Lemma 6.9: two roots with exact multiplicity, localization, gap control, and all larger displacement power tails. -/
theorem exists_uniform_resonantRoots_with_displacement_sum (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
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
            (∑' n : ℤ, rootDisplacementPowerTail p N ξ η n) ≤ rootDisplacementBudget w ψ N := by
  obtain ⟨N₁,hN₁,U₁,ho₁,hc₁,hφ₁,h0₁,hroots⟩ := exists_uniform_resonantRoots hp hp1 w φ
  obtain ⟨N₂,_,U₂,ho₂,hc₂,hφ₂,h0₂,hmajorant⟩ := exists_uniform_resonantDisplacementMajorant hp hp1 w φ
  let N₀ := max N₁ N₂
  refine ⟨N₀,hN₁.trans (le_max_left _ _),U₁ ∩ U₂,ho₁.inter ho₂,hc₁.inter hc₂,⟨hφ₁,hφ₂⟩,⟨h0₁,h0₂⟩,?_⟩
  intro ψ hψ
  have he : ∀ n : ℤ, ∃ x y : ℂ, N₀ ≤ n.natAbs →
      x ∈ refinedResonantDisk n ∧ y ∈ refinedResonantDisk n ∧
      resonantDeterminantExtension hp w ψ n x = 0 ∧ resonantDeterminantExtension hp w ψ n y = 0 ∧
      (∀ z ∈ resonantStrip n, resonantDeterminantExtension hp w ψ n z = 0 ↔ z = x ∨ z = y) ∧
      (∀ z ∈ resonantStrip n, analyticOrderNatAt (resonantDeterminantExtension hp w ψ n) z = ({x,y} : Multiset ℂ).count z) ∧
      ‖x-(Real.pi : ℂ)*n‖ ≤ 3*Real.pi/32 ∧ ‖y-(Real.pi : ℂ)*n‖ ≤ 3*Real.pi/32 ∧
      ‖x-y‖^2 ≤ 6*resonantBProductSup hp w ψ n := by
    intro n
    by_cases hn : N₀ ≤ n.natAbs
    · obtain ⟨x,hx,y,hy,hdata⟩ := hroots ψ hψ.1 n ((le_max_left _ _).trans hn)
      exact ⟨x,y,fun _ => ⟨hx,hy,hdata⟩⟩
    · exact ⟨(Real.pi : ℂ)*n,(Real.pi : ℂ)*n,fun h => (hn h).elim⟩
  choose ξ η hdata using he
  refine ⟨ξ,η,hdata,?_⟩
  intro N hN
  have hmaj := hmajorant ψ hψ.2 N ((le_max_right _ _).trans hN)
  have hbound (n : ℤ) (hn : N ≤ n.natAbs) :
      ‖ξ n-(Real.pi : ℂ)*n‖^p.toReal + ‖η n-(Real.pi : ℂ)*n‖^p.toReal ≤ resonantDisplacementMajorant hp w ψ n := by
    have hr := hdata n (hN.trans hn)
    exact (hmaj.2.2 n hn).2 (ξ n) (refinedResonantDisk_subset_strip n hr.1)
      (η n) (refinedResonantDisk_subset_strip n hr.2.1) hr.2.2.1 hr.2.2.2.1
  obtain ⟨hs,hb⟩ := rootDisplacementPowerTail_summable_and_le p N ξ η
    (resonantDisplacementMajorant hp w ψ) hmaj.1 hbound
  exact ⟨hs,hb.trans hmaj.2.1⟩

end NLS.ZakharovShabat
