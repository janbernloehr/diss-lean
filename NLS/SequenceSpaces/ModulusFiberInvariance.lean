import Mathlib.Analysis.Normed.Lp.lpSpace

/-! # Continuous invariants on full infinite-dimensional modulus fibers -/
noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped ENNReal
namespace NLS

/-- Replace one raw complex coordinate in the same original lp space. -/
def lpReplaceCoordinate {α : Type*} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (z : lp (fun _ : α => ℂ) p) (k : α) (c : ℂ) : lp (fun _ : α => ℂ) p :=
  by
    classical
    exact z+lp.single p k (c-z k)

/-- Finite coordinate replacements and norm convergence of finite lp heads
extend one-coordinate invariance to every full equal-modulus fiber. -/
theorem eq_of_coordinate_moduli_of_replace_invariance
    {α : Type*} {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    {F : Type*} [TopologicalSpace F] [T2Space F]
    (f : lp (fun _ : α => ℂ) p → F) (hf : Continuous f)
    (hinv : ∀ z k c, ‖c‖ = ‖z k‖ → f (lpReplaceCoordinate z k c) = f z)
    (z w : lp (fun _ : α => ℂ) p) (he : ∀ k, ‖z k‖ = ‖w k‖) : f w = f z := by
  classical
  let a : Finset α → lp (fun _ : α => ℂ) p := fun s =>
    z+∑ k ∈ s, lp.single p k (w k-z k)
  have ha (s : Finset α) (k : α) : a s k = if k ∈ s then w k else z k := by
    dsimp only [a]
    rw [lp.coeFn_add,lp.coeFn_sum]
    simp only [Pi.add_apply,Finset.sum_apply,lp.single_apply]
    by_cases hk : k ∈ s <;> simp [hk]
  have hc (s : Finset α) : f (a s) = f z := by
    induction s using Finset.induction_on with
    | empty => simp [a]
    | @insert k s hk ih =>
      have hek : lpReplaceCoordinate (a s) k (w k) = a (insert k s) := by
        ext j
        rw [ha]
        simp only [lpReplaceCoordinate,lp.coeFn_add,Pi.add_apply,lp.single_apply,ha]
        by_cases hj : j = k
        · subst j
          simp [hk]
        · simp [hj]
      rw [←hek,hinv (a s) k (w k) (by rw [ha,if_neg hk]; exact (he k).symm)]
      exact ih
  have ht : Tendsto a atTop (𝓝 w) := by
    have h := (tendsto_const_nhds (x := z)).add (lp.hasSum_single hp (w-z))
    simpa only [a,lp.coeFn_sub,Pi.sub_apply,add_sub_cancel] using! h
  apply tendsto_nhds_unique (hf.continuousAt.tendsto.comp ht)
  simpa only [Function.comp_def,hc] using (tendsto_const_nhds : Tendsto (fun _ : Finset α => f z) atTop (𝓝 (f z)))

end NLS
