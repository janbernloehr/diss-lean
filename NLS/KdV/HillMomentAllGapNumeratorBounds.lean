import NLS.KdV.HillMomentSelectedNumeratorBound
import NLS.KdV.HillMomentDiagonalNumeratorBound
import NLS.ComplexAnalysis.FiniteLocalMajorants

/-! One complex source neighborhood controls the actual numerators on
ALL moving gaps and BEFORE ALL rows, including low and collapsed gaps. -/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch

theorem exists_local_uniform_abelianGapNumerator_all_gap_bound (P : HillProductEquationPatch)
    (H : SourceLemma12_12Data (by norm_num) (by norm_num) P.parent.family.originalDomain
      P.parent.family.domain P.parent.family.roots)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q) :
    ∃ U : Set PeriodOneHminusOne, IsOpen U ∧ q ∈ U ∧ U ⊆ P.source ∧
      ∃ C : ℝ, 0 < C ∧ ∀ a ∈ U, ∀ n m : ℕ+, m ≠ n →
        ∀ z ∈ sourcePeriodicSegment (by simp) (by norm_num) (P.sourcePsi a) (m:ℤ),
          ‖P.abelianGapNumerator n m (z,a)‖ ≤
            C*(1/|((n:ℕ):ℝ)-(m:ℕ)|+1/((n:ℕ)+(m:ℕ):ℝ)) := by
  obtain ⟨Ut,hUt,hqt,htP,K,Ct,hCt,htail⟩ :=
    P.exists_local_uniform_abelianGapNumerator_gap_tail_bound H q hq
  have hf : {m : ℕ+ | (m:ℕ) ≤ K}.Finite :=
    (Set.finite_Iic K).preimage (fun _ _ _ _ h => PNat.coe_injective h)
  let Q : ℕ+ → PeriodOneHminusOne → ℝ → Prop := fun m a C => ∀ n : ℕ+, m ≠ n →
    ∀ z ∈ sourcePeriodicSegment (by simp) (by norm_num) (P.sourcePsi a) (m:ℤ),
      ‖P.abelianGapNumerator n m (z,a)‖ ≤
        C*(1/|((n:ℕ):ℝ)-(m:ℕ)|+1/((n:ℕ)+(m:ℕ):ℝ))
  obtain ⟨V,hV,hqV,Ch,hCh,hhead⟩ := exists_common_open_finite_majorant hf.toFinset q Q (by
    intro m a C D hCD hb n hmn z hz
    exact (hb n hmn z hz).trans (mul_le_mul_of_nonneg_right hCD (by positivity))) (by
    intro m _
    obtain ⟨U,hU,hqU,_,B,hB,hbound⟩ := P.exists_local_selected_abelianGapNumerator_gap_bound H q hq hr m
    exact ⟨U,hU,hqU,B,hB.le,hbound⟩)
  refine ⟨Ut ∩ V,hUt.inter hV,⟨hqt,hqV⟩,(fun a ha => htP ha.1),Ct+Ch+1,by linarith,?_⟩
  intro a ha n m hmn z hz
  by_cases hm : K < (m:ℕ)
  · exact (htail a ha.1 n m hm hmn z hz).trans
      (mul_le_mul_of_nonneg_right (by linarith : Ct ≤ Ct+Ch+1) (by positivity))
  · have hms := hf.mem_toFinset.mpr (le_of_not_gt hm)
    exact (hhead m hms a ha.2 n hmn z hz).trans
      (mul_le_mul_of_nonneg_right (by linarith : Ch ≤ Ct+Ch+1) (by positivity))

theorem exists_local_uniform_diagonal_abelianGapNumerator_all_gap_bound (P : HillProductEquationPatch)
    (H : SourceLemma12_12Data (by norm_num) (by norm_num) P.parent.family.originalDomain
      P.parent.family.domain P.parent.family.roots)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q) :
    ∃ U : Set PeriodOneHminusOne, IsOpen U ∧ q ∈ U ∧ U ⊆ P.source ∧
      ∃ C : ℝ, 0 < C ∧ ∀ a ∈ U, ∀ n : ℕ+,
        ∀ z ∈ sourcePeriodicSegment (by simp) (by norm_num) (P.sourcePsi a) (n:ℤ),
          ‖P.abelianGapNumerator n n (z,a)‖ ≤ C := by
  obtain ⟨Ut,hUt,hqt,htP,K,Ct,hCt,htail⟩ :=
    P.exists_local_uniform_diagonal_abelianGapNumerator_gap_tail_bound H q hq
  have hf : {m : ℕ+ | (m:ℕ) ≤ K}.Finite :=
    (Set.finite_Iic K).preimage (fun _ _ _ _ h => PNat.coe_injective h)
  let Q : ℕ+ → PeriodOneHminusOne → ℝ → Prop := fun m a C =>
    ∀ z ∈ sourcePeriodicSegment (by simp) (by norm_num) (P.sourcePsi a) (m:ℤ),
      ‖P.abelianGapNumerator m m (z,a)‖ ≤ C
  obtain ⟨V,hV,hqV,Ch,hCh,hhead⟩ := exists_common_open_finite_majorant hf.toFinset q Q (by
    intro m a C D hCD hb z hz
    exact (hb z hz).trans hCD) (by
    intro m _
    obtain ⟨U,hU,hqU,_,B,hB,hbound⟩ := P.exists_local_selected_diagonal_abelianGapNumerator_gap_bound q hq hr m
    exact ⟨U,hU,hqU,B,hB.le,hbound⟩)
  refine ⟨Ut ∩ V,hUt.inter hV,⟨hqt,hqV⟩,(fun a ha => htP ha.1),Ct+Ch+1,by linarith,?_⟩
  intro a ha n z hz
  by_cases hn : K < (n:ℕ)
  · exact (htail a ha.1 n hn z hz).trans (by linarith)
  · exact (hhead n (hf.mem_toFinset.mpr (le_of_not_gt hn)) a ha.2 z hz).trans (by linarith)

end NLS.KdV.HillProductEquationPatch
