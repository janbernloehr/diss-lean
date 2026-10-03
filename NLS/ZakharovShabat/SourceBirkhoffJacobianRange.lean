import NLS.ZakharovShabat.SourceBirkhoffJacobian
import NLS.Poisson.SourceHamiltonianDirection
import NLS.SequenceSpaces.Truncation

/-! # Canonical preimages and dense range of the Birkhoff Jacobian

For `2 ≤ p < ∞`, Hamiltonian directions of the actual rectangular
cotangents lie in the source space. The canonical relations give signed
preimages of each output mode, and finite truncations give dense range.
-/

noncomputable section
open Set Complex NLS.Poisson Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceBirkhoffMapComplexData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}

/-- Every pure output mode has an actual source preimage, with the signs
fixed by the canonical Poisson relations. -/
theorem jacobian_single_preimages
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (h2p : (2 : ℝ≥0∞) ≤ p) (φ : realTypeSourceSubmodule p) (m : ℤ) :
    ∃ u v : CoeffPair p,
      sourceBirkhoffJacobian hp hp1 s φ.val u = (lp.single p m 1, 0) ∧
      sourceBirkhoffJacobian hp hp1 s φ.val v = (0, lp.single p m 1) := by
  classical
  obtain ⟨X,Y,hrow,hcan⟩ := D.jacobian_regular_coordinates φ
  have heval (L M : RegularSourceCotangent p) :
      L.toCotangent (sourceHamiltonianDirection h2p M.toCotangent) = L.bivector M := by
    rw [apply_sourceHamiltonianDirection]
    exact (RegularSourceCotangent.bivector_congr (L := L) (M := M)
      (L' := RegularSourceCotangent.ofCotangent h2p L.toCotangent)
      (M' := RegularSourceCotangent.ofCotangent h2p M.toCotangent) rfl rfl).symm
  refine ⟨-sourceHamiltonianDirection h2p (Y m).toCotangent,
    sourceHamiltonianDirection h2p (X m).toCotangent, ?_, ?_⟩
  · apply Prod.ext <;> ext n
    · rw [(hrow _ n).1, map_neg, heval, (hcan n m).2.1]
      simp [lp.single_apply, Pi.single_apply, eq_comm]
    · rw [(hrow _ n).2, map_neg, heval, (hcan n m).2.2]
      simp
  · apply Prod.ext <;> ext n
    · rw [(hrow _ n).1, heval, (hcan n m).1]
      rfl
    · rw [(hrow _ n).2, heval, RegularSourceCotangent.bivector_antisymm,
        (hcan m n).2.1]
      simp [lp.single_apply, Pi.single_apply, eq_comm]

/-- Arbitrary finite truncations of both output sequences lie in the
actual derivative's range. -/
theorem jacobian_truncate_mem_range
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (h2p : (2 : ℝ≥0∞) ≤ p) (φ : realTypeSourceSubmodule p)
    (S : Finset ℤ) (z : Coeff p × Coeff p) :
    (Coeff.truncate S z.1, Coeff.truncate S z.2) ∈
      (sourceBirkhoffJacobian hp hp1 s φ.val).range := by
  classical
  let R := (sourceBirkhoffJacobian hp hp1 s φ.val).range
  have hx (m : ℤ) (c : ℂ) : (lp.single p m c, (0 : Coeff p)) ∈ R := by
    obtain ⟨u, v, hu, hv⟩ := D.jacobian_single_preimages h2p φ m
    have h := R.smul_mem c (show (lp.single p m 1, (0 : Coeff p)) ∈ R from ⟨u,hu⟩)
    simpa only [Prod.smul_mk, smul_zero, ← lp.single_smul, smul_eq_mul, mul_one] using h
  have hy (m : ℤ) (c : ℂ) : ((0 : Coeff p), lp.single p m c) ∈ R := by
    obtain ⟨u, v, hu, hv⟩ := D.jacobian_single_preimages h2p φ m
    have h := R.smul_mem c (show ((0 : Coeff p), lp.single p m 1) ∈ R from ⟨v,hv⟩)
    simpa only [Prod.smul_mk, smul_zero, ← lp.single_smul, smul_eq_mul, mul_one] using h
  have hsum := R.sum_mem (fun m (_ : m ∈ S) => R.add_mem (hx m (z.1 m)) (hy m (z.2 m)))
  have heq : (∑ m ∈ S, ((lp.single p m (z.1 m), (0 : Coeff p)) +
      (0, lp.single p m (z.2 m)))) = (Coeff.truncate S z.1, Coeff.truncate S z.2) := by
    simp only [Prod.mk_add_mk, add_zero, zero_add, ← prod_mk_sum, Coeff.truncate]
  rw [heq] at hsum
  exact hsum

/-- The actual Birkhoff derivative has dense range at every real source,
including sources with infinitely many open gaps. -/
theorem jacobian_denseRange
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (h2p : (2 : ℝ≥0∞) ≤ p) (φ : realTypeSourceSubmodule p) :
    DenseRange (sourceBirkhoffJacobian hp hp1 s φ.val) := by
  intro z
  exact mem_closure_of_tendsto ((Coeff.tendsto_truncate hp z.1).prodMk_nhds
    (Coeff.tendsto_truncate hp z.2))
    (Eventually.of_forall (fun S => D.jacobian_truncate_mem_range h2p φ S z))

end SourceBirkhoffMapComplexData
end NLS.ZakharovShabat
