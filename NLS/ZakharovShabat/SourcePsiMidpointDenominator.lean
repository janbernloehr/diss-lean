import NLS.ZakharovShabat.SourcePsiFreeLatticeBound
import NLS.ZakharovShabat.SourcePeriodicMidpointAsymptotics

/-!
# Uniform omitted-midpoint separation on psi tail discs

The omitted root in Lemma 12.12 is the moving periodic midpoint.
Its displacement has locally bounded norm and uniformly small tails.
The small tail handles distant omitted indices; one larger selected
index cutoff handles the finite omitted head. The resulting lattice
separation is uniform in both indices on one source neighborhood.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Moving a free root by a controlled amount preserves half of
the lattice distance on a selected free-centered disc. -/
theorem shifted_root_free_disc_distance_lower
    (n m : ℤ) (ξ : ℂ) (R : ℝ)
    (hsep : 2*(‖ξ-(Real.pi : ℂ)*n‖+R) ≤ Real.pi*|((n-m : ℤ) : ℝ)|)
    (z : ℂ) (hz : z ∈ closedBall ((Real.pi : ℂ)*m) R) :
    (Real.pi/2)*|((n-m : ℤ) : ℝ)| ≤ ‖ξ-z‖ := by
  have hcenter := norm_free_center_sub n m
  have hzR : ‖z-(Real.pi : ℂ)*m‖ ≤ R := by
    simpa only [mem_closedBall,dist_eq_norm] using hz
  have htri : ‖(Real.pi : ℂ)*n-(Real.pi : ℂ)*m‖ ≤
      ‖ξ-(Real.pi : ℂ)*n‖+‖ξ-z‖+‖z-(Real.pi : ℂ)*m‖ := by
    calc
      ‖(Real.pi : ℂ)*n-(Real.pi : ℂ)*m‖ =
          ‖((Real.pi : ℂ)*n-ξ)+(ξ-z)+(z-(Real.pi : ℂ)*m)‖ := by congr 1; ring
      _ ≤ ‖(Real.pi : ℂ)*n-ξ‖+‖ξ-z‖+‖z-(Real.pi : ℂ)*m‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ = ‖ξ-(Real.pi : ℂ)*n‖+‖ξ-z‖+‖z-(Real.pi : ℂ)*m‖ := by rw [norm_sub_rev]
  rw [hcenter] at htri
  linarith

/-- On one neighborhood of any complex source, the actual omitted
midpoints have a common lattice denominator bound on all sufficiently
distant selected eighth-pi discs, independently of the omitted index. -/
theorem exists_local_sourcePeriodicMidpoint_tail_lattice_separation
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∃ D : ℝ, 0 ≤ D ∧ ∃ K : ℕ, ∀ ψ ∈ V,
        ‖sourcePeriodicMidpointDisplacement hp hp1 ψ‖ ≤ D ∧
        ∀ m : ℤ, K ≤ m.natAbs → ∀ n : ℤ, n ≠ m →
          ∀ z ∈ closedBall ((Real.pi : ℂ)*m) (Real.pi/8),
            (Real.pi/2)*|((n-m : ℤ) : ℝ)| ≤
              ‖sourceStandardRootMidpoint hp hp1 ψ n-z‖ := by
  obtain ⟨N,hN,V,hVopen,hφV,D,hD,hdata⟩ :=
    exists_uniform_small_sourcePeriodicMidpointDisplacement hp hp1 φ
      (by positivity : 0 < Real.pi/8)
  obtain ⟨L,hL⟩ := exists_nat_gt (2*(D+Real.pi/8)/Real.pi)
  have hLπ : 2*(D+Real.pi/8) ≤ Real.pi*(L : ℝ) := by
    have h := (div_lt_iff₀ Real.pi_pos).mp hL
    nlinarith
  refine ⟨V,hVopen,hφV,D,hD,N+L,?_⟩
  intro ψ hψ
  obtain ⟨hbound,htail⟩ := hdata ψ hψ
  refine ⟨hbound,?_⟩
  intro m hm n hnm z hz
  have hpoint : ‖sourceStandardRootMidpoint hp hp1 ψ n-(Real.pi : ℂ)*n‖ ≤ D := by
    have h := (lp.norm_apply_le_norm (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
      (sourcePeriodicMidpointDisplacement hp hp1 ψ) n).trans hbound
    simpa only [sourcePeriodicMidpointDisplacement_apply,sourceStandardRootMidpoint] using h
  apply shifted_root_free_disc_distance_lower n m _ _ ?_ z hz
  by_cases hn : N < n.natAbs
  · have hnot : n ∉ Finset.Icc (-(N : ℤ)) N := by
      simp only [Finset.mem_Icc]
      omega
    have hsmall : ‖sourceStandardRootMidpoint hp hp1 ψ n-(Real.pi : ℂ)*n‖ ≤ Real.pi/8 := by
      have h := (lp.norm_apply_le_norm (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
        (sourcePeriodicMidpointDisplacement hp hp1 ψ-
          Coeff.truncate (Finset.Icc (-(N : ℤ)) N)
            (sourcePeriodicMidpointDisplacement hp hp1 ψ)) n).trans (htail N le_rfl)
      simpa only [lp.coeFn_sub,Pi.sub_apply,Coeff.truncate_apply,if_neg hnot,sub_zero,
        sourcePeriodicMidpointDisplacement_apply,sourceStandardRootMidpoint] using h
    have hd : 1 ≤ |((n-m : ℤ) : ℝ)| := by
      exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hnm)
    nlinarith [Real.pi_pos]
  · have htri : m.natAbs ≤ (m-n).natAbs+n.natAbs := by
      simpa only [sub_add_cancel] using Int.natAbs_add_le (m-n) n
    have hdist : L ≤ (n-m).natAbs := by
      have heq : (m-n).natAbs = (n-m).natAbs := by
        rw [← Int.natAbs_neg (n-m),neg_sub]
      rw [heq] at htri
      omega
    have habs : (L : ℝ) ≤ |((n-m : ℤ) : ℝ)| := by
      have hcast : (L : ℝ) ≤ ((n-m).natAbs : ℝ) := by exact_mod_cast hdist
      simpa only [Nat.cast_natAbs,Int.cast_abs] using hcast
    nlinarith [mul_le_mul_of_nonneg_left habs Real.pi_pos.le]

end NLS.ZakharovShabat
