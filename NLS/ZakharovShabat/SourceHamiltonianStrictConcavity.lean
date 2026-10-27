import NLS.SequenceSpaces.HilbertStrictConcavity
import NLS.ZakharovShabat.SourceHamiltonianOriginal

/-! # Literal strict concavity of the original action Hamiltonian

The retained negative-Hessian bound yields strict Jensen inequalities for
this same Hamiltonian, on one neighborhood of zero. The nonnegative cone
includes boundary points and arbitrary infinite sets of zero actions.
-/
noncomputable section
set_option autoImplicit false

namespace NLS.ZakharovShabat.SourceOriginalHamiltonianData
open Set Metric
open scoped ENNReal
local instance : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩
local instance : (4 : ℝ≥0∞).HolderTriple 4 2 := (ENNReal.holderTriple_iff _ _ _).mpr (by
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_add])
variable {W₀ W V : Set (CoeffPair 4)} {s : (n : ℤ) → CoeffPair 4 → DeletedCoeff 4 n}
  {D : SourceSection17OriginalData (by simp) (by norm_num) W₀ W V s}
  {T : Set (Coeff 2)} {F : Coeff 2 → Coeff 2} {H : Coeff 2 → ℂ}

/-- The same original Hamiltonian is strictly concave near zero, both on the
entire real action ball and on its nonnegative cone. -/
theorem strict_concavity (Q : SourceOriginalHamiltonianData D T F H) :
    ∃ r : ℝ, 0 < r ∧ ball (0:Coeff 2) r ⊆ T ∧
      StrictConcaveOn ℝ (ball (0:Coeff 2) r ∩ Coeff.realLocus 2) (fun b => (H b).re) ∧
      StrictConcaveOn ℝ (ball (0:Coeff 2) r ∩ Coeff.nonnegativeLocus 2) (fun b => (H b).re) := by
  obtain ⟨r,hr,hball,hess⟩ := Q.concavity
  have hc := Coeff.strictConcaveOn_real_hilbert_ball H T Q.frequency.isOpen Q.analytic r hball hess
  refine ⟨r,hr,hball,hc,hc.subset ?_ ?_⟩
  · intro b hb
    exact ⟨hb.1,fun n => (hb.2 n).1⟩
  · exact (convex_ball (0:Coeff 2) r).inter (Coeff.convex_nonnegativeLocus 2)

/-- Literal strict Jensen inequality for any two distinct nonnegative actions
in one common neighborhood, including points with zero coordinates. -/
theorem strict_jensen (Q : SourceOriginalHamiltonianData D T F H) :
    ∃ r : ℝ, 0 < r ∧ ∀ x ∈ Coeff.nonnegativeLocus 2, ‖x‖ < r →
      ∀ y ∈ Coeff.nonnegativeLocus 2, ‖y‖ < r → x ≠ y →
        ∀ t : ℝ, 0 < t → t < 1 →
          (1-t) * (H x).re + t * (H y).re < (H ((1-t) • x + t • y)).re := by
  obtain ⟨r,hr,_,_,hc⟩ := Q.strict_concavity
  refine ⟨r,hr,?_⟩
  intro x hx hxr y hy hyr hxy t ht ht1
  exact hc.2 ⟨mem_ball_zero_iff.mpr hxr,hx⟩ ⟨mem_ball_zero_iff.mpr hyr,hy⟩
    hxy (sub_pos.mpr ht1) ht (by ring)

end NLS.ZakharovShabat.SourceOriginalHamiltonianData
