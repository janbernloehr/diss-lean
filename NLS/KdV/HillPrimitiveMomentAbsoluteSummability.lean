import NLS.KdV.HillPrimitiveMomentTailBound
import NLS.SequenceSpaces.PositiveSquaredGapMomentSummability

/-! Every actual weighted second-moment row is absolutely summable on
one complex neighborhood chosen before all rows. This does not yet
identify its sum with the physical Hamiltonian frequency. -/
noncomputable section
open Set Metric Complex NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch

theorem exists_open_centeredSecondMoment_absolute_summability (P : HillProductEquationPatch)
    (H : SourceLemma12_12Data (by norm_num) (by norm_num) P.parent.family.originalDomain
      P.parent.family.domain P.parent.family.roots)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q) :
    ∃ W : Set (CoeffPair 2),
    ∃ C : SourceFullAbelianUniformCauchyFamily (by simp) (by norm_num) W,
    ∃ U : Set PeriodOneHminusOne, IsOpen U ∧ q ∈ U ∧ U ⊆ P.momentSource C ∧
      ∀ n : ℕ+, ∀ a ∈ U,
        Summable (fun m : ℕ+ => ‖((m:ℕ):ℂ)*P.centeredMoment W n m 1 a‖) := by
  obtain ⟨W,C,U,hU,hqU,hUC,K,B,hB,hbound⟩ :=
    P.exists_local_uniform_centeredSecondMoment_tail_bound H q hq hr
  refine ⟨W,C,U,hU,hqU,hUC,?_⟩
  intro n a ha
  have hs := Coeff.summable_norm_positive_weighted_of_squared_gap_tail
    (sourcePeriodicGapDisplacement (by simp) (by norm_num) (P.sourcePsi a)) n
    (fun m => (2*Real.pi:ℂ)⁻¹*P.centeredMoment W n m 1 a) K B hB.le
    (fun m hm hmn => hbound a ha n m hm hmn)
  apply (hs.mul_left (2*Real.pi)).congr
  intro m
  have he : ((m:ℕ):ℂ)*P.centeredMoment W n m 1 a =
      (2*Real.pi:ℂ)*(((m:ℕ):ℂ)*((2*Real.pi:ℂ)⁻¹*P.centeredMoment W n m 1 a)) := by
    have hpi : (Real.pi:ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
    field_simp
  rw [he,norm_mul]
  simp only [norm_mul,norm_ofNat,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]

end NLS.KdV.HillProductEquationPatch
