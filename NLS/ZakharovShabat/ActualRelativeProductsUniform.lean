import NLS.ZakharovShabat.UniformSpectralDisplacements
import NLS.ZakharovShabat.RelativeSpectralProductsFamilies

/-!
# Uniform relative products for actual potentials

The proved spectral counting and corrected displacement estimates supply one
open convex potential neighborhood on which actual completed root sequences
satisfy the bounded-family convergence theorem. Continuity of individual root
labels is neither assumed nor needed.
-/

noncomputable section
open Filter Topology Metric
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Actual spectral data yield paired relative products uniformly in the potential and off-lattice parameter.
The central placeholders are free, and the original high-pair and counting data are retained. -/
theorem exists_uniform_actualRelativeProducts (hp : p ≠ ⊤) (hp1 : 1 < p)
    (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight p) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∃ ξ η : U → ℤ → ℂ,
      ∃ hξ : ∀ ψ, Memℓp (fun n => ξ ψ n-(Real.pi : ℂ)*n) p,
      ∃ hη : ∀ ψ, Memℓp (fun n => η ψ n-(Real.pi : ℂ)*n) p,
      (∃ R : ℝ, 0 ≤ R ∧ ∀ ψ, ‖(⟨_,hξ ψ⟩ : Coeff p)‖ ≤ R ∧ ‖(⟨_,hη ψ⟩ : Coeff p)‖ ≤ R) ∧
      (∀ ψ : U,
        (∀ n : ℤ, n.natAbs ≤ N₀ → ξ ψ n = (Real.pi : ℂ)*n ∧ η ψ n = (Real.pi : ℂ)*n) ∧
        (∀ n : ℤ, N₀ < n.natAbs → PeriodicResonantPair hp w ψ.val n (ξ ψ n) (η ψ n)) ∧
        ∀ N ≥ N₀, PeriodicCountingData hp (weightedBaseToPair w ψ.val) N) ∧
      ∀ z₀ : ℂ, z₀ ∉ freeLattice →
        TendstoUniformlyOn (fun (M : ℕ) (t : ℂ × U) => ∏ n ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
          spectralRelativeFactor (ξ t.2) t.1 n*spectralRelativeFactor (η t.2) t.1 n)
          (fun t => spectralRelativePairProduct (ξ t.2) (η t.2) t.1) atTop
          (closedBall z₀ (freeGap z₀/2) ×ˢ Set.univ) := by
  obtain ⟨N₀,hN₀,U,ho,hconv,hφ,h0,R,hR,hdata⟩ := exists_uniform_bounded_periodicDisplacements hp hp1 w φ
  choose ξ η hξ hη hbξ hbη hfree hr hc using (fun ψ : U => hdata ψ.val ψ.property)
  refine ⟨N₀,hN₀,U,ho,hconv,hφ,h0,ξ,η,hξ,hη,⟨R,hR,fun ψ => ⟨hbξ ψ,hbη ψ⟩⟩,
    fun ψ => ⟨hfree ψ,hr ψ,hc ψ⟩,?_⟩
  intro z₀ hz₀
  exact tendstoUniformlyOn_spectralRelativePair_family hp hp1 ξ η hξ hη Set.univ R hR
    (fun ψ _ => hbξ ψ) (fun ψ _ => hbη ψ) z₀ hz₀

end NLS.ZakharovShabat
