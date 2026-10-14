import NLS.SequenceSpaces.CompactTailReciprocalMatrix
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Finite output approximations of deleted-coordinate operators

An lp row majorant gives convergence of the actual finite output cutoffs
in operator norm. Each cutoff has finite-dimensional range, with no
assumption about how the omitted index meets the finite set.
-/

noncomputable section
open Set Filter Topology Metric
open scoped ENNReal
namespace NLS.Coeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Keep finitely many output coordinates of a deleted-space operator. -/
def deletedOutputCutoff (n : ℤ) (T : DeletedCoeff p n →L[ℂ] DeletedCoeff p n)
    (s : Finset ℤ) : DeletedCoeff p n →L[ℂ] DeletedCoeff p n :=
  (deleteCoordinateTo n).comp ((truncateCLM s).comp
    (((lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n).ker.subtypeL).comp T))

theorem deletedOutputCutoff_apply (n : ℤ) (T : DeletedCoeff p n →L[ℂ] DeletedCoeff p n)
    (s : Finset ℤ) (a : DeletedCoeff p n) :
    (deletedOutputCutoff n T s a : Coeff p) = truncate s (T a : Coeff p) := by
  apply (deleteCoordinate_eq_self_iff n _).mpr
  simp [show (T a : Coeff p) n = 0 from (T a).property]

/-- The cutoff range lies in the span of finitely many projected coordinate vectors. -/
theorem finiteDimensional_range_deletedOutputCutoff (n : ℤ)
    (T : DeletedCoeff p n →L[ℂ] DeletedCoeff p n) (s : Finset ℤ) :
    FiniteDimensional ℂ (LinearMap.range (deletedOutputCutoff n T s).toLinearMap) := by
  let e : ℤ → DeletedCoeff p n := fun k => deleteCoordinateTo n (lp.single p k 1)
  let S := Submodule.span ℂ (e '' (s : Set ℤ))
  let : FiniteDimensional ℂ S := FiniteDimensional.span_of_finite ℂ (s.finite_toSet.image e)
  apply Submodule.finiteDimensional_of_le (S₂ := S)
  rintro b ⟨a,rfl⟩
  change deleteCoordinateTo n (truncate s (T a : Coeff p)) ∈ S
  rw [truncate,map_sum]
  apply Submodule.sum_mem
  intro k hk
  have he : deleteCoordinateTo n (lp.single p k ((T a:Coeff p) k)) =
      (T a:Coeff p) k • e k := by
    dsimp [e]
    rw [← map_smul]
    congr 1
    ext j
    by_cases hj : j = k
    · subst j; simp
    · simp [hj]
  rw [he]
  exact S.smul_mem _ (Submodule.subset_span ⟨k,hk,rfl⟩)

/-- The actual cutoff error is controlled by the lp tail of a row majorant. -/
theorem norm_deletedOutputCutoff_sub_le (n : ℤ)
    (T : DeletedCoeff p n →L[ℂ] DeletedCoeff p n) (b : Coeff p)
    (hrow : ∀ m : ℤ, ∀ a : DeletedCoeff p n, ‖(T a:Coeff p) m‖ ≤ ‖b m‖*‖a‖)
    (s : Finset ℤ) : ‖deletedOutputCutoff n T s-T‖ ≤ ‖truncate s b-b‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro a
  change ‖((deletedOutputCutoff n T s a-T a : DeletedCoeff p n):Coeff p)‖ ≤ _
  rw [Submodule.coe_sub,deletedOutputCutoff_apply]
  exact norm_truncate_operator_sub_le_rowTail
    (((lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n).ker.subtypeL).comp T) b hrow s a

/-- Finite-dimensional output cutoffs converge in operator norm. -/
theorem tendsto_deletedOutputCutoff_of_rowMajorant (hp : p ≠ ⊤) (n : ℤ)
    (T : DeletedCoeff p n →L[ℂ] DeletedCoeff p n) (b : Coeff p)
    (hrow : ∀ m : ℤ, ∀ a : DeletedCoeff p n, ‖(T a:Coeff p) m‖ ≤ ‖b m‖*‖a‖) :
    Tendsto (deletedOutputCutoff n T) atTop (𝓝 T) := by
  let ι : DeletedCoeff p n →L[ℂ] Coeff p :=
    (lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n).ker.subtypeL
  have ht := tendsto_truncate_operator_of_rowMajorant hp (ι.comp T) b hrow
  have hc := ((ContinuousLinearMap.compL ℂ (DeletedCoeff p n) (Coeff p)
    (DeletedCoeff p n)) (deleteCoordinateTo n)).continuous.tendsto
      ((ι.comp T)) |>.comp ht
  have he : (deleteCoordinateTo n).comp (ι.comp T) = T := by
    ext a m
    exact congrArg (fun b : Coeff p => b m)
      ((deleteCoordinate_eq_self_iff n (T a : Coeff p)).mpr (T a).property)
  change Tendsto (deletedOutputCutoff n T) atTop
    (𝓝 ((deleteCoordinateTo n).comp (ι.comp T))) at hc
  rwa [he] at hc

/-- Reciprocal matrix entries give an actual lp row majorant on the whole space. -/
theorem exists_deletedOperator_rowMajorant_of_reciprocalEntries
    (q : ℝ≥0∞) [Fact (1 ≤ q)] [p.HolderConjugate q]
    (hp : p ≠ ⊤) (n : ℤ) (T : DeletedCoeff p n →L[ℂ] DeletedCoeff p n)
    (b : Coeff p) (hdiag : ∀ m : ℤ, deletedOperatorMatrixEntry n T m m = 0)
    (hoff : ∀ m k : ℤ, k ≠ m →
      ‖deletedOperatorMatrixEntry n T m k‖ ≤ ‖b m‖/|((k-m:ℤ):ℝ)|) :
    ∃ B : Coeff p, ∀ m : ℤ, ∀ a : DeletedCoeff p n,
      ‖(T a:Coeff p) m‖ ≤ ‖B m‖*‖a‖ := by
  let c := puncturedLattice q ((ENNReal.HolderConjugate.lt_top_iff_one_lt p q).mp hp.lt_top)
  let B : Coeff p := (‖c‖:ℂ) • b
  refine ⟨B,?_⟩
  intro m a
  obtain ⟨row,hrow,hrep⟩ := exists_deletedOperator_rowKernel_of_reciprocalEntries
    (q := q) hp n m T b (hdiag m) (hoff m)
  have hB : ‖B m‖ = ‖c‖*‖b m‖ := by
    simp only [B,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,norm_mul,
      Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg c)]
  rw [hrep a,hB]
  calc
    ‖dualPairing (a : Coeff p) row‖ ≤ ‖(a : Coeff p)‖ * ‖row‖ := norm_dualPairing_le _ _
    _ ≤ ‖a‖ * (‖b m‖ * ‖c‖) := mul_le_mul_of_nonneg_left hrow (norm_nonneg a)
    _ = (‖c‖ * ‖b m‖) * ‖a‖ := by ring

end NLS.Coeff
