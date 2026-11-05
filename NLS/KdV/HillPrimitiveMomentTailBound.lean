import NLS.KdV.HillPrimitiveMomentsCosineBound
import NLS.KdV.HillMomentGapNumeratorTail
import NLS.ZakharovShabat.SourceFullAbelianSquareUniformGapBound

/-! The actual centered second moments retain the squared complex gap
and both signed reciprocal-index factors on one common neighborhood. -/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch

theorem exists_local_uniform_centeredSecondMoment_tail_bound (P : HillProductEquationPatch)
    (H : SourceLemma12_12Data (by norm_num) (by norm_num) P.parent.family.originalDomain
      P.parent.family.domain P.parent.family.roots)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q) :
    ∃ W : Set (CoeffPair 2),
    ∃ C : SourceFullAbelianUniformCauchyFamily (by simp) (by norm_num) W,
    ∃ U : Set PeriodOneHminusOne, IsOpen U ∧ q ∈ U ∧ U ⊆ P.momentSource C ∧
      ∃ K : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ a ∈ U, ∀ n m : ℕ+, K < (m:ℕ) → m ≠ n →
        ‖(2*Real.pi:ℂ)⁻¹*P.centeredMoment W n m 1 a‖ ≤
          B*‖sourcePeriodicGapDisplacement (by simp) (by norm_num) (P.sourcePsi a) (m:ℤ)‖^2*
            (1/|((n:ℕ):ℝ)-(m:ℕ)|+1/((n:ℕ)+(m:ℕ):ℝ)) := by
  obtain ⟨W,hlocal⟩ := exists_sourceFullAbelian_local_uniform_square_gap_bound
  let u : PeriodOneRealL2 := ⟨P.parent.parent.miuraBall.actionBall.lift q,
    P.parent.parent.miuraBall.actionBall.lift_real q (P.parent.subset (P.subset hq)).1 hr⟩
  let φ : realTypeSourceSubmodule 2 := ⟨P.sourcePsi q,(hillMiuraRealSource u).property⟩
  obtain ⟨C,V,hV,hφ,hVC,S,hS,hsq⟩ := hlocal φ
  obtain ⟨Un,hUn,hqn,hnP,K,B,hB,hnum⟩ :=
    P.exists_local_uniform_abelianGapNumerator_gap_tail_bound H q hq
  let T := P.source ∩ P.sourcePsi ⁻¹' V
  have hT : IsOpen T := P.analytic_sourcePsi.continuousOn.isOpen_inter_preimage P.source_open hV
  refine ⟨W,C,Un ∩ T,hUn.inter hT,⟨hqn,hq,hφ⟩,
    (fun a ha => ⟨hnP ha.1,hVC ha.2.2⟩),K,S*B,mul_pos hS hB,?_⟩
  intro a ha n m hm hmn
  have hb := P.norm_normalized_centeredSecondMoment_le C n m a
    ⟨hnP ha.1,hVC ha.2.2⟩
    (S*‖sourcePeriodicGapDisplacement (by simp) (by norm_num) (P.sourcePsi a) (m:ℤ)‖^2)
    (B*(1/|((n:ℕ):ℝ)-(m:ℕ)|+1/((n:ℕ)+(m:ℕ):ℝ))) (by positivity)
    (hsq (P.sourcePsi a) ha.2.2 (m:ℤ)) (hnum a ha.1 n m hm hmn)
  convert hb using 1; ring

end NLS.KdV.HillProductEquationPatch
