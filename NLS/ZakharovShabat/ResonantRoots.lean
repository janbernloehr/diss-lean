import NLS.ComplexAnalysis.ZeroMultiset
import NLS.ZakharovShabat.ResonantZeroCount
import NLS.ZakharovShabat.ResonantRootGap

/-!
# The two resonant roots with analytic multiplicity

Each distant strip has two roots, counted with repetition. They exhaust
its scalar determinant zeros, their occurrences equal the actual analytic
orders, and they obey the source localization and factor-six gap bounds.
-/

noncomputable section
open scoped ENNReal Classical
open NLS.ComplexAnalysis
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The two roots of Lemma 6.9, with exact scalar multiplicities and locally uniform bounds. -/
theorem exists_uniform_resonantRoots (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) :
    ∃ N : ℕ, 2 ≤ N ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ ψ ∈ U, ∀ n : ℤ, N ≤ n.natAbs →
        ∃ x ∈ refinedResonantDisk n, ∃ y ∈ refinedResonantDisk n,
          resonantDeterminantExtension hp w ψ n x = 0 ∧
          resonantDeterminantExtension hp w ψ n y = 0 ∧
          (∀ z ∈ resonantStrip n, resonantDeterminantExtension hp w ψ n z = 0 ↔ z = x ∨ z = y) ∧
          (∀ z ∈ resonantStrip n,
            analyticOrderNatAt (resonantDeterminantExtension hp w ψ n) z = ({x,y} : Multiset ℂ).count z) ∧
          ‖x - (Real.pi : ℂ)*n‖ ≤ 3*Real.pi/32 ∧
          ‖y - (Real.pi : ℂ)*n‖ ≤ 3*Real.pi/32 ∧
          ‖x-y‖^2 ≤ 6 * resonantBProductSup hp w ψ n := by
  obtain ⟨N₁,hN₁,U₁,ho₁,hc₁,hφ₁,h0₁,hcount⟩ := exists_uniform_resonantDeterminant_zeroCount hp hp1 w φ
  obtain ⟨N₂,_,U₂,ho₂,hc₂,hφ₂,h0₂,hloc⟩ := exists_uniform_resonantDeterminant_localization hp hp1 w φ
  obtain ⟨N₃,_,U₃,ho₃,hc₃,hφ₃,h0₃,hgap⟩ := exists_uniform_resonantRoot_gap hp hp1 w φ
  refine ⟨max N₁ (max N₂ N₃), hN₁.trans (le_max_left _ _), U₁ ∩ (U₂ ∩ U₃),
    ho₁.inter (ho₂.inter ho₃), hc₁.inter (hc₂.inter hc₃), ⟨hφ₁,hφ₂,hφ₃⟩, ⟨h0₁,h0₂,h0₃⟩, ?_⟩
  intro ψ hψ n hn
  obtain ⟨ha,_,hfin,horder,_,_,hcount₂⟩ := hcount ψ hψ.1 n (by omega)
  have hsupp := hfin.subset (analyticZeroCount_support_subset (resonantDeterminantExtension hp w ψ n) (resonantStrip n))
  obtain ⟨x,hx,y,hy,hxz,hyz,hm⟩ := exists_two_analytic_zeros hsupp hcount₂
  have hlocal := (hloc ψ hψ.2.1 n (by omega)).2.2.1
  have hxlocal := hlocal x hx hxz
  have hylocal := hlocal y hy hyz
  have hmult : ∀ z ∈ resonantStrip n,
      analyticOrderNatAt (resonantDeterminantExtension hp w ψ n) z = ({x,y} : Multiset ℂ).count z := by
    intro z hz
    simpa only [if_pos hz] using hm z
  refine ⟨x,hxlocal.2,y,hylocal.2,hxz,hyz,?_,hmult,hxlocal.1,hylocal.1,?_⟩
  · intro z hz
    constructor
    · intro hfz
      have hpz := analyticOrderNatAt_pos_of_zero (ha z hz) (horder z hz) hfz
      rw [hmult z hz] at hpz
      simpa using Multiset.count_pos.mp hpz
    · rintro (rfl | rfl)
      · exact hxz
      · exact hyz
  · exact (hgap ψ hψ.2.2 n (by omega)).2.2 x hx y hy hxz hyz

end NLS.ZakharovShabat
