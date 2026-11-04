import NLS.KdV.HillAbelianUniformValueBound
import NLS.KdV.HillOffIndexUniformSeries
import NLS.SequenceSpaces.PositiveReciprocalSumBound

/-! The ACTUAL infinite physical correction is locally bounded
UNIFORMLY in ALL numerator indices. The complete absolute sum has the
same bound, including low gaps, complex collapses and endpoint sheets. -/
noncomputable section
open Set Metric Complex NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch

theorem exists_local_uniform_physicalOffIndexAbelianCorrection_bound (P : HillProductEquationPatch)
    (H : SourceLemma12_12Data (by norm_num) (by norm_num) P.parent.family.originalDomain
      P.parent.family.domain P.parent.family.roots)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q) :
    ∃ U : Set PeriodOneHminusOne, IsOpen U ∧ q ∈ U ∧ U ⊆ P.physicalDirichletSource ∧
      ∃ R : ℝ, 0 < R ∧ ∀ a ∈ U, ∀ n : ℕ+,
        (∑' m : ℕ+, ‖P.physicalOffIndexAbelianTerm n a m‖) ≤ R ∧
          ‖P.physicalOffIndexAbelianCorrection n a‖ ≤ R := by
  obtain ⟨Uv,hUv,hqv,hvP,C,hC,hbound⟩ := P.exists_local_uniform_physicalOffIndexAbelianValue_bound H q hq hr
  obtain ⟨Uw,hUw,hqw,_,B,hB,hweights⟩ := P.exists_local_abelianWeight_norm_bound q hq
  let κ := Coeff.puncturedLattice 2 (by norm_num : 1 < (2:ℝ≥0∞))
  let R := C*B*(2*‖κ‖)+1
  have hR : 0 < R := by dsimp only [R]; positivity
  refine ⟨Uv ∩ Uw,hUv.inter hUw,⟨hqv,hqw⟩,(fun a ha => hvP ha.1),R,hR,?_⟩
  intro a ha n
  let gap := sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (P.sourcePsi a)
  let d := P.physicalAbelianMidpointDisplacement a
  have hu (m : ℕ+) (hmn : m ≠ n) : ‖P.physicalOffIndexAbelianTerm n a m‖ ≤
      C*(‖gap ((m:ℕ):ℤ)‖+‖d ((m:ℕ):ℤ)‖)*
        (1/|((n:ℕ):ℝ)-(m:ℕ)|+1/((n:ℕ)+(m:ℕ):ℝ)) := by
    simpa only [physicalOffIndexAbelianTerm,if_neg hmn,d,P.physicalAbelianMidpointDisplacement_apply] using
      hbound a ha.1 n m hmn
  obtain ⟨hs,habs⟩ := Coeff.summable_norm_positive_and_tsum_le_of_signed_reciprocal_bound gap d n
    (P.physicalOffIndexAbelianTerm n a) (by simp [physicalOffIndexAbelianTerm]) C hC.le hu
  have htotal : (∑' m : ℕ+, ‖P.physicalOffIndexAbelianTerm n a m‖) ≤ R := by
    apply habs.trans
    have hw := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hweights a ha.2) hC.le)
      (show 0 ≤ 2*‖κ‖ by positivity)
    exact hw.trans (by dsimp only [R]; linarith)
  exact ⟨htotal,(norm_tsum_le_tsum_norm hs).trans htotal⟩

end NLS.KdV.HillProductEquationPatch
