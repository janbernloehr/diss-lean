import NLS.KdV.HillHminusOneCanonicalGapHighNormalization
import NLS.ZakharovShabat.SourceHigherActionOneNormalized

/-! # Analytic nonzero normalized Hill actions at every fixed positive index

For the actual Miura action I=2*higherAction(k=1), the normalization is
R=16*pi*n*(higherAction(k=1)/gamma_Dirac^2)/(2*midpoint_Dirac)^2.
The weighted filled quotient and positive midpoint sum make this analytic
and nonzero near EVERY real H-minus-one source, including collapsed gaps.
All original Hill labels and the canonical squared gap are retained.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.KdV

def HillHminusMiuraGapBall.normalizedRatio (B : HillHminusMiuraGapBall) (n : ℕ+)
    (q : PeriodOneHminusOne) : ℂ :=
  (16*((Real.pi : ℂ)*(n : ℕ)))*
    sourceHigherActionOneNormalized (by simp) (by norm_num) (n : ℕ)
      (hillMiuraDiagonal (B.actionBall.lift q))/(B.diracSum n q)^2

theorem exists_local_hillHminus_canonical_normalized_ratio
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q) (n : ℕ+) :
    ∃ U : Set PeriodOneHminusOne, IsOpen U ∧ q ∈ U ∧ U ⊆ hillHminusCanonicalGapDomain ∧
      ∃ R : PeriodOneHminusOne → ℂ, AnalyticOnNhd ℂ R U ∧
        ∀ a ∈ U, R a ≠ 0 ∧
          hillHminusCanonicalAction n a = hillHminusCanonicalGapSquare n a /
            (8*((Real.pi : ℂ)*(n : ℕ)))*R a ∧
          (hillHminusCanonicalAction n a = 0 ↔ hillHminusCanonicalGapSquare n a = 0) ∧
          (hillHminusCanonicalGapSquare n a ≠ 0 →
            (8*((Real.pi : ℂ)*(n : ℕ)))*hillHminusCanonicalAction n a/hillHminusCanonicalGapSquare n a = R a) := by
  obtain ⟨B,hB⟩ := exists_hillHminusMiuraGapBall q hq
  let v : PeriodOneRealL2 := ⟨B.actionBall.lift q,B.actionBall.lift_real q hB hq⟩
  let φ := hillMiuraRealSource v
  obtain ⟨T,hT,hφT,hF,hdata⟩ := exists_local_sourceHigherActionOneNormalized_nonzero_of_left_pos
    (p := 2) (by simp) (by norm_num) φ (n : ℕ)
    (hillMiura_positive_gap_left_pos v (n : ℕ) (by exact_mod_cast n.pos))
  let f : PeriodOneHminusOne → CoeffPair 2 := fun a => hillMiuraDiagonal (B.actionBall.lift a)
  have hf : AnalyticOnNhd ℂ f B.source := by
    intro a ha
    exact (hillMiuraDiagonal.analyticAt (B.actionBall.lift a)).comp
      (f := B.actionBall.lift) (B.actionBall.lift_analytic a ha)
  let V := B.source ∩ f ⁻¹' T
  have hV : IsOpen V := hf.continuousOn.isOpen_inter_preimage B.source_open hT
  have hqV : q ∈ V := ⟨hB,hφT⟩
  have hsum : B.diracSum n q ≠ 0 := by
    intro he
    have hp := B.diracSum_re_pos_of_real n q hB hq
    rw [he,zero_re] at hp
    exact lt_irrefl 0 hp
  let U := V ∩ {a | B.diracSum n a ≠ 0}
  have hU : IsOpen U := ((B.analytic_diracSum n).mono inter_subset_left).continuousOn.isOpen_inter_preimage
    hV isOpen_compl_singleton
  have hK : (8*((Real.pi : ℂ)*(n : ℕ))) ≠ 0 :=
    mul_ne_zero (by norm_num) (mul_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero) (by exact_mod_cast n.ne_zero))
  have hL : (16*((Real.pi : ℂ)*(n : ℕ))) ≠ 0 :=
    mul_ne_zero (by norm_num) (mul_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero) (by exact_mod_cast n.ne_zero))
  refine ⟨U,hU,⟨hqV,hsum⟩,(fun a ha => mem_iUnion.mpr ⟨B,ha.1.1⟩),B.normalizedRatio n,?_,?_⟩
  · intro a ha
    exact (analyticAt_const.mul ((hF (f a) ha.1.2).comp (f := f) (hf a ha.1.1))).div
      ((B.analytic_diracSum n a ha.1.1).pow 2) (pow_ne_zero 2 ha.2)
  · intro a ha
    obtain ⟨hFnz,hfactor⟩ := hdata (f a) ha.1.2
    have hRn : B.normalizedRatio n a ≠ 0 := div_ne_zero (mul_ne_zero hL hFnz) (pow_ne_zero 2 ha.2)
    have hI : hillHminusCanonicalAction n a = 2*((sourcePeriodicGapDisplacement (by simp) (by norm_num)
        (f a) (n : ℕ))^2*sourceHigherActionOneNormalized (by simp) (by norm_num) (n : ℕ) (f a)) := by
      rw [B.actionBall.canonical_action_eq n a ha.1.1]
      change 2*sourceIndexedHigherAction (by simp) (by norm_num) (n : ℕ) 1 (f a) = _
      rw [hfactor]
    have hG : hillHminusCanonicalGapSquare n a =
        (sourcePeriodicGapDisplacement (by simp) (by norm_num) (f a) (n : ℕ))^2*(B.diracSum n a)^2 := by
      rw [B.canonical_gapSquare_eq n a ha.1.1]
      simp only [HillHminusMiuraGapBall.gapSquare,sourcePeriodicGapDisplacement_apply,f]
    have he : hillHminusCanonicalAction n a = hillHminusCanonicalGapSquare n a /
        (8*((Real.pi : ℂ)*(n : ℕ)))*B.normalizedRatio n a := by
      rw [hI,hG]
      unfold HillHminusMiuraGapBall.normalizedRatio
      let D := sourcePeriodicGapDisplacement (by simp) (by norm_num) (f a) (n : ℕ)
      let F := sourceHigherActionOneNormalized (by simp) (by norm_num) (n : ℕ) (f a)
      let S := B.diracSum n a
      change 2*(D^2*F) = (D^2*S^2)/(8*((Real.pi : ℂ)*(n : ℕ)))*
        ((16*((Real.pi : ℂ)*(n : ℕ)))*F/S^2)
      have hS : S ≠ 0 := ha.2
      have hπ : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
      have hn : ((n : ℕ) : ℂ) ≠ 0 := by exact_mod_cast n.ne_zero
      field_simp [hS,hπ,hn]
      ring
    refine ⟨hRn,he,?_,?_⟩
    · rw [he]
      simp only [mul_eq_zero,div_eq_zero_iff,hRn,hK,or_false]
    · intro hg
      rw [he]
      field_simp [hg,hK]

end NLS.KdV
