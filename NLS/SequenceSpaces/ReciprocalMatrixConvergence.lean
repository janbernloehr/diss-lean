import NLS.SequenceSpaces.FiniteOutputReciprocalTail

/-!
# Norm convergence from a common reciprocal matrix bound

A single lp row majorant controls every off-diagonal operator in the
family. Its output tails and the conjugate-space reciprocal input tails
give uniform finite-block approximations. Coordinatewise convergence
then implies operator-norm convergence of the off-diagonal parts.
-/

noncomputable section
open Filter Topology Metric
open scoped ENNReal
namespace NLS.Coeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A common reciprocal entry majorant upgrades coordinatewise convergence
to norm convergence for the off-diagonal operators. -/
theorem tendsto_offDiagonal_of_coordinatewise_and_reciprocalEntries
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (T : ℤ → Coeff p →L[ℂ] Coeff p) (Q : Coeff p →L[ℂ] Coeff p)
    (hpoint : ∀ x : Coeff p, ∀ m : ℤ,
      Tendsto (fun n : ℤ => (T n x) m) (Filter.comap Int.natAbs atTop) (𝓝 ((Q x) m)))
    (b : Coeff p)
    (hentry : ∀ n m k : ℤ, k ≠ m →
      ‖(T n (lp.single p k 1)) m‖ ≤ ‖b m‖/|((k-m:ℤ):ℝ)|) :
    Tendsto (fun n : ℤ => operatorOffDiagonal (T n)) (Filter.comap Int.natAbs atTop)
      (𝓝 (operatorOffDiagonal Q)) := by
  let q := p.conjExponent
  let : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
  have hq : q ≠ ⊤ := (ENNReal.HolderConjugate.lt_top_iff_one_lt q p).mpr hp1 |>.ne
  let A (n : ℤ) := operatorOffDiagonal (T n)
  let c : Coeff q := puncturedLattice q
    ((ENNReal.HolderConjugate.lt_top_iff_one_lt p q).mp hp.lt_top)
  let B : Coeff p := (‖c‖:ℂ) • b
  have hAe (n m k : ℤ) (hkm : k ≠ m) :
      ‖(A n (lp.single p k 1)) m‖ ≤ ‖b m‖/|((k-m:ℤ):ℝ)| := by
    rw [operatorOffDiagonal_entry_other (T n) m k hkm.symm]
    exact hentry n m k hkm
  have hrow (n m : ℤ) (x : Coeff p) : ‖A n x m‖ ≤ ‖B m‖*‖x‖ := by
    obtain ⟨row,hr,he⟩ := exists_operator_rowKernel_of_reciprocalEntries (q := q)
      hp m (A n) b (operatorOffDiagonal_diagonal (T n) m) (hAe n m)
    have hB : ‖B m‖ = ‖c‖*‖b m‖ := by
      simp only [B,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,norm_mul,
        Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg c)]
    rw [he x,hB]
    exact ((norm_dualPairing_le x row).trans
      (mul_le_mul_of_nonneg_left hr (norm_nonneg x))).trans_eq (by ring)
  have hpointA (x : Coeff p) (m : ℤ) :
      Tendsto (fun n : ℤ => (A n x) m) (Filter.comap Int.natAbs atTop)
        (𝓝 ((operatorOffDiagonal Q x) m)) := by
    simpa [A,operatorOffDiagonal] using (hpoint x m).sub ((hpoint (lp.single p m 1) m).mul_const (x m))
  apply tendsto_operator_of_coordinatewise_and_eventual_remainder_finiteBlocks
    A (operatorOffDiagonal Q) 0 hpointA
  intro ε hε
  obtain ⟨s,hs⟩ := Metric.tendsto_atTop.mp (tendsto_truncate hp B) (ε/2) (half_pos hε)
  obtain ⟨t,ht⟩ := exists_uniform_finiteOutput_inputTail_cutoff_of_reciprocalEntries
    q hp hq s 0 ‖b‖ (norm_nonneg b) (ε/2) (half_pos hε)
  refine ⟨s,t,Eventually.of_forall (fun n => ?_)⟩
  have hout : ‖A n-(truncateCLM s).comp (A n)‖ < ε/2 := by
    rw [norm_sub_rev]
    have hb : ‖truncate s B-B‖ < ε/2 := by simpa only [dist_eq_norm] using hs s le_rfl
    apply lt_of_le_of_lt ?_ hb
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro x
    exact norm_truncate_operator_sub_le_rowTail (A n) B (hrow n) s x
  have hin := ht (A n) (fun m _ k _ hkm => (hAe n m k hkm).trans
    (div_le_div_of_nonneg_right (lp.norm_apply_le_norm (zero_lt_one.trans hp1).ne' b m) (abs_nonneg _)))
  have he : A n-(truncateCLM s).comp ((A n).comp (truncateCLM t)) =
      (A n-(truncateCLM s).comp (A n)) + (truncateCLM s).comp
        ((A n).comp (ContinuousLinearMap.id ℂ (Coeff p)-truncateCLM t)) := by
    ext x
    simp
  simp only [sub_zero]
  rw [he]
  exact (norm_add_le _ _).trans_lt (by linarith)

end NLS.Coeff
