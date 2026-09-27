import NLS.ZakharovShabat.SourceCriticalDisplacementContinuity
import NLS.ZakharovShabat.SourceDistantCriticalPointsAnalyticNeighborhood

/-!
# Uniform free circles around distant critical points

The critical displacement has locally uniformly small finite tails.
Consequently one source neighborhood and one cutoff put every distant
critical point strictly inside its free-centered eighth-pi circle.
-/

noncomputable section
open Set Metric Complex Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- All sufficiently distant critical points lie inside their
free-centered eighth-pi circles on one complex source neighborhood. -/
theorem exists_local_source_distantCriticalPoints_inside_free_eighth_ball
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ)) :
    ∃ K : ℕ, ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∀ ψ ∈ V, ∀ n : ℤ, K < n.natAbs →
        canonicalCriticalPoints hp hp1 (periodOnePotential ψ)
          (periodOnePotential_mem ψ) n ∈
            ball ((Real.pi:ℂ)*n) (Real.pi/8) := by
  obtain ⟨s,V,hVopen,hφV,htail⟩ :=
    exists_local_sourceCriticalDisplacement_uniform_tails hp hp1 φ hreal
      (Real.pi/16) (by positivity)
  let K := s.sup (fun n : ℤ => n.natAbs)
  refine ⟨K,V,hVopen,hφV,?_⟩
  intro ψ hψ n hn
  have hnot : n ∉ s := by
    intro hns
    exact (not_lt_of_ge (Finset.le_sup hns)) hn
  have hpoint := lp.norm_apply_le_norm (zero_lt_one.trans hp1).ne'
    (sourceCriticalDisplacement hp hp1 ψ -
      Coeff.truncate s (sourceCriticalDisplacement hp hp1 ψ)) n
  have hsmall : ‖canonicalCriticalPoints hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n - (Real.pi:ℂ)*n‖ ≤ Real.pi/16 := by
    calc
      _ = ‖(sourceCriticalDisplacement hp hp1 ψ -
          Coeff.truncate s (sourceCriticalDisplacement hp hp1 ψ)) n‖ := by
        simp only [lp.coeFn_sub, Pi.sub_apply, Coeff.truncate_apply,
          if_neg hnot, sub_zero, sourceCriticalDisplacement,
          canonicalCriticalDisplacement_apply]
      _ ≤ ‖sourceCriticalDisplacement hp hp1 ψ -
          Coeff.truncate s (sourceCriticalDisplacement hp hp1 ψ)‖ := hpoint
      _ ≤ Real.pi/16 := htail ψ hψ
  rw [mem_ball, dist_eq_norm]
  exact lt_of_le_of_lt hsmall (by nlinarith [Real.pi_pos])

end NLS.ZakharovShabat
