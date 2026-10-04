import NLS.ZakharovShabat.SourceFullAbelianGapAllExponentTails

/-! # The mixed sequence error on distant gaps in Lemma 19.4

The deleted-factor majorants and the actual critical offset combine into
locally bounded `ell^q + ell^(p/2)` majorants for the gap-normalized error
of the actual primitive. Every finite `q > 1` is allowed, and the proof
includes the quasi-norm range `1 < p < 2`.
-/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)]

/-- One source neighborhood and one sequence-norm bound control both
boundary errors on all distant complex gaps. No asymptotic hypothesis
on the primitive or the deleted factor is supplied by the caller. -/
theorem exists_local_sourceFullAbelian_gap_tail_majorants
    (hp : p ≠ ⊤) (hp1 : 1 < p) (hq : q ≠ ⊤) (hq1 : 1 < q)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧ ∃ K : ℕ, ∃ M : ℝ, 0 ≤ M ∧
      ∀ ψ ∈ V, ∃ Bq : Coeff q, ∃ Bg : Coeff (ENNReal.ofReal (p.toReal/2)),
        ‖Bq‖ ≤ M ∧ ‖Bg‖ ≤ M ∧
        ∀ (W : Set (CoeffPair p)) (C : SourceFullAbelianUniformCauchyFamily hp hp1 W),
          ψ ∈ ball C.discs.source.val C.discs.sourceRadius →
          ∀ n : ℤ, K ≤ n.natAbs → ∀ θ ∈ Icc (0:ℝ) Real.pi, ∀ upper : Bool,
            ‖C.gapBoundary n ψ θ upper-I*sourceStandardRootGapBoundary hp hp1 ψ n θ upper‖ ≤
              ‖sourcePeriodicGapDisplacement hp hp1 ψ n‖*(‖Bq n‖+‖Bg n‖) := by
  obtain ⟨V,hV,hφV,K,hb⟩ := exists_local_sourceFullAbelian_gap_all_exponent_tails hp hp1 φ hφ
  exact ⟨V,hV,hφV,K,hb q hq hq1⟩

end NLS.ZakharovShabat
