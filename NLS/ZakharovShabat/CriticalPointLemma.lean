import NLS.ZakharovShabat.CanonicalCriticalContinuity

/-!
# Lemma 8.5: ordered critical coordinates, product, and continuity

The canonical coordinates give one cutoff-independent realization of all
assertions: complete ordered roots, locally bounded lp displacements,
the normalized derivative product, and coordinate continuity at real-type
potentials. The product is understood through its locally uniform literal
symmetric cutoffs. Continuity in the lp norm is not asserted.
-/

noncomputable section
open Set Complex Filter Topology
open NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- All assertions of Lemma 8.5 for the fixed canonical critical coordinates. -/
theorem exists_uniform_canonicalCriticalPoints_lemma_8_5 (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) :
    ∃ N : ℕ, 0 < N ∧ ∃ U : Set (PairSpace p), IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∃ R : ℝ, 0 ≤ R ∧ ∀ ψ ∈ U, ∀ hψ : ψ ∈ pairParitySubspace 0,
        CriticalPointLabeling hp hp1 ψ hψ N (canonicalCriticalPoints hp hp1 ψ hψ) ∧
        Monotone (fun n => complexLexKey (canonicalCriticalPoints hp hp1 ψ hψ n)) ∧
        (∀ n, canonicalCriticalPoints hp hp1 ψ hψ n =
          (Real.pi : ℂ)*n + canonicalCriticalDisplacement hp hp1 ψ hψ n) ∧
        ‖canonicalCriticalDisplacement hp hp1 ψ hψ‖ ≤ R ∧
        (∀ z, deriv (canonicalDiscriminant hp ψ) z =
          entireSingleSpectralProduct (canonicalCriticalPoints hp hp1 ψ hψ) z) ∧
        TendstoLocallyUniformlyOn
          (fun M z => singleSpectralPartialProduct (canonicalCriticalPoints hp hp1 ψ hψ) z M)
          (deriv (canonicalDiscriminant hp ψ)) atTop univ ∧
        (IsRealType ψ → ∀ n : ℤ, ContinuousAt
          (fun χ : pairParitySubspace (p := p) 0 => canonicalCriticalPoints hp hp1 χ.val χ.property n)
          (⟨ψ,hψ⟩ : pairParitySubspace (p := p) 0)) := by
  obtain ⟨N,hN,U,ho,hc,hφ,h0,R,hR,h⟩ := exists_uniform_canonicalCriticalPoints hp hp1 φ
  refine ⟨N,hN,U,ho,hc,hφ,h0,R,hR,?_⟩
  intro ψ hψ heven
  obtain ⟨hl,hnorm⟩ := h ψ hψ heven
  refine ⟨hl,monotone_canonicalCriticalPoints hp hp1 ψ heven,?_,hnorm,
    discriminant_derivative_eq_canonicalCriticalProduct hp hp1 ψ heven,
    tendstoLocallyUniformlyOn_canonicalCriticalProduct hp hp1 ψ heven,?_⟩
  · intro n
    rw [canonicalCriticalDisplacement_apply, add_comm, sub_add_cancel]
  · intro hr n
    exact continuousAt_canonicalCriticalPoints_of_realType hp hp1 ⟨ψ,heven⟩ hr n

end NLS.ZakharovShabat
