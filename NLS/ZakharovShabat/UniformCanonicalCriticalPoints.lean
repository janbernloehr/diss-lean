import NLS.ZakharovShabat.CanonicalCriticalPoints

/-!
# Uniform bounds for the canonical critical coordinates

Uniqueness identifies the local ordered labelings with the fixed canonical
sequence. Thus one neighborhood controls the actual canonical displacement
norms and supplies a common valid cutoff without any continuity assumption.
-/

noncomputable section
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The canonical coordinates have a common valid cutoff and bounded lp norm near every potential. -/
theorem exists_uniform_canonicalCriticalPoints (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p) :
    ∃ N : ℕ, 0 < N ∧ ∃ U : Set (PairSpace p), IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∃ R : ℝ, 0 ≤ R ∧ ∀ ψ ∈ U, ∀ hψ : ψ ∈ pairParitySubspace 0,
        CriticalPointLabeling hp hp1 ψ hψ N (canonicalCriticalPoints hp hp1 ψ hψ) ∧
        ‖canonicalCriticalDisplacement hp hp1 ψ hψ‖ ≤ R := by
  obtain ⟨N,hN,U,ho,hc,hφ,h0,R,hR,h⟩ := exists_uniform_ordered_critical_products hp hp1 φ
  refine ⟨N,hN,U,ho,hc,hφ,h0,R,hR,?_⟩
  intro ψ hψ heven
  obtain ⟨ξ,a,hlabel,hs,he,ha,_,_⟩ := h ψ hψ heven
  have hξ := hlabel.eq_canonicalCriticalPoints hs
  rw [hξ] at hlabel he
  have heq : canonicalCriticalDisplacement hp hp1 ψ heven = a := by
    ext n
    rw [canonicalCriticalDisplacement_apply, he n, add_sub_cancel_left]
  exact ⟨hlabel,heq ▸ ha⟩

/-- Canonical root cutoffs converge locally uniformly to the derivative on the whole plane. -/
theorem tendstoLocallyUniformlyOn_canonicalCriticalProduct (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (hφ : φ ∈ pairParitySubspace 0) :
    TendstoLocallyUniformlyOn (fun M z => singleSpectralPartialProduct (canonicalCriticalPoints hp hp1 φ hφ) z M)
      (deriv (canonicalDiscriminant hp φ)) atTop Set.univ :=
  (canonicalCriticalPoints_spec hp hp1 φ hφ).1.tendstoLocallyUniformlyOn_derivative_product
    (canonicalCriticalPoints_spec hp hp1 φ hφ).2.2

/-- The common canonical labeling remains valid at every larger cutoff in the same neighborhood. -/
theorem exists_uniform_canonicalCriticalPoints_all_cutoffs (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p) :
    ∃ N : ℕ, 0 < N ∧ ∃ U : Set (PairSpace p), IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∃ R : ℝ, 0 ≤ R ∧ ∀ ψ ∈ U, ∀ hψ : ψ ∈ pairParitySubspace 0,
        ‖canonicalCriticalDisplacement hp hp1 ψ hψ‖ ≤ R ∧
        ∀ K : ℕ, N ≤ K → CriticalPointLabeling hp hp1 ψ hψ K (canonicalCriticalPoints hp hp1 ψ hψ) := by
  obtain ⟨N,hN,U,ho,hc,hφ,h0,R,hR,h⟩ := exists_uniform_canonicalCriticalPoints hp hp1 φ
  refine ⟨N,hN,U,ho,hc,hφ,h0,R,hR,?_⟩
  intro ψ hψ heven
  obtain ⟨hlabel,hnorm⟩ := h ψ hψ heven
  exact ⟨hnorm,fun K hK => hlabel.enlarge K hK⟩

end NLS.ZakharovShabat
