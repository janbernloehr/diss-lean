import NLS.SequenceSpaces.UniformHolderSums
import NLS.SequenceSpaces.PuncturedLattice
import NLS.SequenceSpaces.Translation

/-! # Uniform sums with a reciprocal off-diagonal bound

A bounded lp family divided by the distance from a fixed integer has
uniformly small absolute tails. A bounded diagonal term can be included
in the same Holder majorant. No uniform tails of the lp family are assumed.
-/
noncomputable section
open Filter Topology
open scoped ENNReal
namespace NLS.Coeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Absolute and uniform convergence from a reciprocal bound away from
one index and a separate bound at that index. -/
theorem summable_uniform_of_reciprocal_bound {X : Type*}
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (S : Set X)
    (u : X → ℤ → ℂ) (a : X → Coeff p) (C M D : ℝ)
    (hC : 0 ≤ C) (ha : ∀ x ∈ S, ‖a x‖ ≤ M)
    (hd : ∀ x ∈ S, ‖u x n‖ ≤ D)
    (hu : ∀ x ∈ S, ∀ k : ℤ, k ≠ n →
      ‖u x k‖ ≤ C*‖a x k‖/|((n-k:ℤ):ℝ)|) :
    (∀ x ∈ S, Summable (fun k => ‖u x k‖)) ∧
      TendstoUniformlyOn
        (fun (N : ℕ) x => ∑ k ∈ Finset.Icc (-(N : ℤ)) N, u x k)
        (fun x => ∑' k, u x k) atTop S := by
  classical
  have hq1 : 1 < p.conjExponent :=
    (ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top
  have hq : p.conjExponent ≠ ⊤ :=
    ((ENNReal.HolderConjugate.lt_top_iff_one_lt p.conjExponent p).mpr hp1).ne
  let : Fact (1 ≤ p.conjExponent) := ⟨hq1.le⟩
  let b : Coeff p.conjExponent := reindex (Equiv.subLeft n)
    (puncturedLattice p.conjExponent hq1) + lp.single p.conjExponent n 1
  let d (x : X) : Coeff p := lp.single p n (u x n)
  have hb (k : ℤ) : ‖b k‖ = if k = n then 1 else |((n-k:ℤ):ℝ)|⁻¹ := by
    by_cases hk : k = n
    · subst k
      simp [b, reindex_apply, Equiv.subLeft_apply, puncturedLattice_apply]
    · have hnk : n-k ≠ 0 := sub_ne_zero.mpr (Ne.symm hk)
      simp only [b, lp.coeFn_add, Pi.add_apply, reindex_apply, Equiv.subLeft_apply,
        puncturedLattice_apply, if_neg hnk, lp.single_apply, Pi.single_eq_of_ne hk,
        add_zero, norm_inv, Complex.norm_intCast, if_neg hk]
  have hbound (x : X) (hx : x ∈ S) (k : ℤ) :
      ‖u x k‖ ≤ (C+1)*(‖a x k‖+‖d x k‖)*‖b k‖ := by
    rw [hb]
    by_cases hk : k = n
    · subst k
      simp only [ite_true, d, lp.single_apply, Pi.single_eq_same, mul_one]
      nlinarith [norm_nonneg (a x n), norm_nonneg (u x n)]
    · rw [if_neg hk]
      have he : d x k = 0 := by simp [d, lp.single_apply, hk]
      rw [he, norm_zero, add_zero]
      apply (hu x hx k hk).trans
      rw [div_eq_mul_inv]
      gcongr
      linarith
  have hs (x : X) (hx : x ∈ S) : Summable (fun k => ‖u x k‖) :=
    (summable_norm_of_two_holder_bounds
      (ENNReal.HolderConjugate.toReal_of_ne_top hp hq) (a x) (d x) b
      (u x) (C+1) (by positivity) (hbound x hx)).1
  refine ⟨hs, ?_⟩
  have hc := uniformCauchySeqOn_two_holder_sums a d b hq u S (C+1) (M+D)
    (by positivity) (fun x hx => by
      have he : ‖d x‖ = ‖u x n‖ := by
        exact lp.norm_single (zero_lt_one.trans hp1) _ _
      rw [he]
      exact add_le_add (ha x hx) (hd x hx)) hbound
  exact hc.tendstoUniformlyOn_of_tendsto (fun x hx =>
    (hs x hx).of_norm.hasSum.comp Finset.tendsto_Icc_neg)

end NLS.Coeff
