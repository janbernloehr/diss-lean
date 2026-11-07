import NLS.KdV.HillMomentAllGapNumeratorBounds
import NLS.KdV.HillPrimitiveMomentSeriesNeighborhood

/-! Actual second-moment estimates on every row and every gap, on
one common complex neighborhood. No low-index or diagonal exceptions
remain, and every estimate retains the squared actual gap. -/
noncomputable section
open Set Metric Complex NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch

theorem exists_momentSeriesNeighborhood_all_index_bound (P : HillProductEquationPatch)
    (H : SourceLemma12_12Data (by norm_num) (by norm_num) P.parent.family.originalDomain
      P.parent.family.domain P.parent.family.roots)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q) :
    ∃ D : MomentSeriesNeighborhood P, q ∈ D.source ∧
      ∀ a ∈ D.source, ∀ n m : ℕ+,
        ‖(2*Real.pi:ℂ)⁻¹*P.centeredMoment D.ambient n m 1 a‖ ≤
          D.constant*‖sourcePeriodicGapDisplacement (by simp) (by norm_num) (P.sourcePsi a) (m:ℤ)‖^2*
            (if m=n then 1 else 1/|((n:ℕ):ℝ)-(m:ℕ)|+1/((n:ℕ)+(m:ℕ):ℝ)) := by
  obtain ⟨W,hlocal⟩ := exists_sourceFullAbelian_local_uniform_square_gap_bound
  let u : PeriodOneRealL2 := ⟨P.parent.parent.miuraBall.actionBall.lift q,
    P.parent.parent.miuraBall.actionBall.lift_real q (P.parent.subset (P.subset hq)).1 hr⟩
  let φ : realTypeSourceSubmodule 2 := ⟨P.sourcePsi q,(hillMiuraRealSource u).property⟩
  obtain ⟨C,V,hV,hφ,hVC,S,hS,hsq⟩ := hlocal φ
  obtain ⟨Uo,hUo,hqo,_,Bo,hBo,hoff⟩ := P.exists_local_uniform_abelianGapNumerator_all_gap_bound H q hq hr
  obtain ⟨Ud,hUd,hqd,_,Bd,hBd,hdiag⟩ := P.exists_local_uniform_diagonal_abelianGapNumerator_all_gap_bound H q hq hr
  let T := P.source ∩ P.sourcePsi ⁻¹' V
  have hT : IsOpen T := P.analytic_sourcePsi.continuousOn.isOpen_inter_preimage P.source_open hV
  let U := (Uo ∩ Ud) ∩ T
  have hU : IsOpen U := (hUo.inter hUd).inter hT
  have hqU : q ∈ U := ⟨⟨hqo,hqd⟩,hq,hφ⟩
  have hUC : U ⊆ P.momentSource C := fun a ha => ⟨ha.2.1,hVC ha.2.2⟩
  let B := S*(Bo+Bd)
  have hB : 0 < B := mul_pos hS (add_pos hBo hBd)
  have hfull : ∀ a ∈ U, ∀ n m : ℕ+,
      ‖(2*Real.pi:ℂ)⁻¹*P.centeredMoment W n m 1 a‖ ≤
        B*‖sourcePeriodicGapDisplacement (by simp) (by norm_num) (P.sourcePsi a) (m:ℤ)‖^2*
          (if m=n then 1 else 1/|((n:ℕ):ℝ)-(m:ℕ)|+1/((n:ℕ)+(m:ℕ):ℝ)) := by
    intro a ha n m
    have hnum : ∀ z ∈ sourcePeriodicSegment (by simp) (by norm_num) (P.sourcePsi a) (m:ℤ),
        ‖P.abelianGapNumerator n m (z,a)‖ ≤
          (Bo+Bd)*(if m=n then 1 else 1/|((n:ℕ):ℝ)-(m:ℕ)|+1/((n:ℕ)+(m:ℕ):ℝ)) := by
      intro z hz
      by_cases hmn : m=n
      · subst m
        rw [if_pos (show n=n from rfl),mul_one]
        exact (hdiag a ha.1.2 n z hz).trans (by linarith)
      · rw [if_neg hmn]
        exact (hoff a ha.1.1 n m hmn z hz).trans
          (mul_le_mul_of_nonneg_right (by linarith : Bo ≤ Bo+Bd) (by positivity))
    have hb := P.norm_normalized_centeredSecondMoment_le C n m a (hUC ha)
      (S*‖sourcePeriodicGapDisplacement (by simp) (by norm_num) (P.sourcePsi a) (m:ℤ)‖^2)
      ((Bo+Bd)*(if m=n then 1 else 1/|((n:ℕ):ℝ)-(m:ℕ)|+1/((n:ℕ)+(m:ℕ):ℝ)))
      (by positivity) (hsq (P.sourcePsi a) ha.2.2 (m:ℤ)) hnum
    convert hb using 1; dsimp only [B]; ring
  let D : MomentSeriesNeighborhood P := {
    ambient := W
    cauchy := C
    source := U
    source_open := hU
    subset := hUC
    threshold := 0
    constant := B
    constant_pos := hB
    tail_bound := by
      intro a ha n m _ hmn
      simpa only [if_neg hmn] using hfull a ha n m }
  exact ⟨D,hqU,hfull⟩

end NLS.KdV.HillProductEquationPatch
