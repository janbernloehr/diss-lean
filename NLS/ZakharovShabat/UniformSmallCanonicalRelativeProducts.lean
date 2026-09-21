import NLS.ZakharovShabat.UniformSmallFreeDiscProducts
import NLS.ZakharovShabat.CanonicalPeriodicDisplacementBounds

/-! # Canonical relative products close to one
The actual endpoint displacements have locally uniformly small tails.
Combining them with a fixed neighborhood norm bound yields a common
large-index threshold for both relative products on entire free discs.
-/

noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Both canonical endpoint relative products approach one locally uniformly on distant half-pi discs. -/
theorem exists_uniform_small_canonicalRelativeProducts (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, 0 < N ∧ ∃ U : Set (PairSpace p), IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ ψ ∈ U, ∀ heven : ψ ∈ pairParitySubspace 0, ∀ n : ℤ, N < n.natAbs →
        ∀ z : ℂ, ‖z-(Real.pi : ℂ)*n‖ ≤ Real.pi/2 →
          ‖freeDiscRelativeProduct (canonicalPeriodicLeftDisplacement hp hp1 ψ heven) n z-1‖ < ε ∧
          ‖freeDiscRelativeProduct (canonicalPeriodicRightDisplacement hp hp1 ψ heven) n z-1‖ < ε := by
  obtain ⟨V,hvo,hvc,hvφ,hv0,R,hR,hbound⟩ := exists_uniform_bounded_canonicalPeriodicDisplacements hp hp1 φ
  obtain ⟨δ,hδ,hsmall⟩ := exists_uniform_small_freeDiscRelativeProducts hp hp1 hR hε
  obtain ⟨M,_,W,hwo,hwc,hwφ,hw0,_,_,htail⟩ := exists_uniform_small_canonicalPeriodicDisplacements hp hp1 φ hδ
  obtain ⟨N,hN⟩ := hsmall (Finset.Icc (-(M : ℤ)) M)
  refine ⟨N+1,by omega,V ∩ W,hvo.inter hwo,hvc.inter hwc,⟨hvφ,hwφ⟩,⟨hv0,hw0⟩,
    fun ψ hψ heven n hn z hz => ?_⟩
  obtain ⟨hl,hr⟩ := hbound ψ hψ.1 heven
  obtain ⟨htl,htr⟩ := (htail ψ hψ.2 heven).2.2 M le_rfl
  exact ⟨hN _ hl htl n (by omega) z hz,hN _ hr htr n (by omega) z hz⟩

end NLS.ZakharovShabat
