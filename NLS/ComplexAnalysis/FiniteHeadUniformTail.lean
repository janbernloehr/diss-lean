import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Data.PNat.Basic
import Mathlib.Tactic

/-! # One metric neighborhood from a finite head and a uniform tail

Only finitely many individual neighborhoods are intersected. The tail
already has one neighborhood before all indices.
-/

open Set Metric Filter Topology
namespace NLS.ComplexAnalysis
variable {A : Type*} [PseudoMetricSpace A]

theorem exists_ball_forall_pos_index_of_local_and_uniform_tail
    (P : ℕ+ → A → Prop) (a : A)
    (hlocal : ∀ k : ℕ+, ∀ᶠ u in 𝓝 a, P k u)
    (N : ℕ) (r : ℝ) (hr : 0 < r)
    (htail : ∀ k : ℕ+, N ≤ (k : ℕ) → ∀ u ∈ ball a r, P k u) :
    ∃ η : ℝ, 0 < η ∧ η ≤ r ∧ ∀ k : ℕ+, ∀ u ∈ ball a η, P k u := by
  have hhead (m : ℕ) : ∀ᶠ u in 𝓝 a, ∀ k : ℕ+, (k : ℕ) < m → P k u := by
    induction m with
    | zero => exact Eventually.of_forall (by intro u k hk; omega)
    | succ m ih =>
      by_cases hm : 0 < m
      · filter_upwards [ih,hlocal ⟨m,hm⟩] with u hu hmu
        intro k hk
        by_cases hkm : (k : ℕ) = m
        · have he : k = ⟨m,hm⟩ := Subtype.ext hkm
          exact he ▸ hmu
        · exact hu k (by omega)
      · have hm0 : m = 0 := Nat.eq_zero_of_not_pos hm
        subst m
        exact Eventually.of_forall (fun _ k hk => False.elim ((Nat.not_lt.mpr k.property) hk))
  obtain ⟨ε,hε,hεsub⟩ := Metric.mem_nhds_iff.mp (hhead N)
  refine ⟨min ε r,lt_min hε hr,min_le_right _ _,?_⟩
  intro k u hu
  by_cases hk : N ≤ (k : ℕ)
  · exact htail k hk u (ball_subset_ball (min_le_right _ _) hu)
  · exact hεsub (ball_subset_ball (min_le_left _ _) hu) k (by omega)

end NLS.ComplexAnalysis
