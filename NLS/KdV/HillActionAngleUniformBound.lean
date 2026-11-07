import NLS.KdV.HillActionAngleCartesian
import NLS.KdV.HillAbelianUniformExponentialBound

/-! The action-normalized factors inherit ONE local inverse-square-root
index bound relative to the actual diagonal factors, BEFORE ALL n.
The remaining diagonal spectral estimate is a separate obligation. -/
noncomputable section
open Set Complex
open scoped Classical
namespace NLS.KdV

theorem exists_local_uniform_actionAngle_diagonal_bound (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusActionAmplitudeDomain) :
    ∃ U : Set PeriodOneHminusOne, IsOpen U ∧ q ∈ U ∧ U ⊆ hillHminusActionAmplitudeDomain ∧
      ∃ C : ℝ, 0 < C ∧ ∀ a ∈ U, ∀ n : ℕ+,
        ‖hillHminusActionAngleFactorPlus n a‖ ≤
          (C/Real.sqrt (n:ℕ))*‖hillHminusDiagonalCartesianPlus n a‖ ∧
        ‖hillHminusActionAngleFactorMinus n a‖ ≤
          (C/Real.sqrt (n:ℕ))*‖hillHminusDiagonalCartesianMinus n a‖ := by
  obtain ⟨Ua,hUa,hqa,hUaD,A,hA,ha⟩ :=
    exists_local_uniform_hillHminusCanonicalActionAmplitude_bound q hq
  obtain ⟨Ub,hUb,hqb,_,B,hB,hb⟩ :=
    exists_local_uniform_complete_Abelian_diagonal_multiplier_bound q
      (hillHminusActionAmplitudeDomain_subset_bounded hq)
  refine ⟨Ua ∩ Ub,hUa.inter hUb,⟨hqa,hqb⟩,(fun _ h => hUaD h.1),A*B,mul_pos hA hB,?_⟩
  intro a haU n
  have ha' := ha a haU.1 n
  have hb' := hb a haU.2 n
  have hA' : 0 ≤ A/Real.sqrt (n:ℕ) := div_nonneg hA.le (Real.sqrt_nonneg _)
  constructor
  · rw [hillHminusActionAngleFactorPlus,norm_mul]
    calc
      _ ≤ (A/Real.sqrt (n:ℕ))*(B*‖hillHminusDiagonalCartesianPlus n a‖) :=
        mul_le_mul ha' hb'.1 (norm_nonneg _) hA'
      _ = _ := by ring
  · rw [hillHminusActionAngleFactorMinus,norm_mul]
    calc
      _ ≤ (A/Real.sqrt (n:ℕ))*(B*‖hillHminusDiagonalCartesianMinus n a‖) :=
        mul_le_mul ha' hb'.2 (norm_nonneg _) hA'
      _ = _ := by ring

end NLS.KdV
