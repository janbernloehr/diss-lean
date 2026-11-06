import NLS.SequenceSpaces.PeriodOneRealFormIdentity
import NLS.SequenceSpaces.PeriodOneMiuraReality

/-! # Rough real-form uniqueness on domains away from zero

A connected open domain needs only one real point. Real projection also
shows that overlapping balls with real centers have a real overlap.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex NLS.ComplexAnalysis
open scoped ComplexConjugate
namespace NLS

theorem periodOneHminus_real_form_identity_at
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]
    {U : Set PeriodOneHminusOne} (hU : IsOpen U) (hconn : IsPreconnected U)
    (q0 : PeriodOneHminusOne) (hq0 : q0 ∈ U) (hr0 : IsRealPeriodOneHminusOne q0)
    (F G : PeriodOneHminusOne → Y) (hF : AnalyticOnNhd ℂ F U) (hG : AnalyticOnNhd ℂ G U)
    (he : ∀ q ∈ U, IsRealPeriodOneHminusOne q → F q = G q) : EqOn F G U := by
  let R : Set PeriodOneHminusOne := {q | periodOneHminusConjugation q = q}
  have hRadd : ∀ {x y : PeriodOneHminusOne}, x ∈ R → y ∈ R → x+y ∈ R := by
    intro x y hx hy
    change periodOneHminusConjugation (x+y) = x+y
    rw [periodOneHminusConjugation_add,hx,hy]
  have hRsmul : ∀ t : ℝ, ∀ {x : PeriodOneHminusOne}, x ∈ R → (t : ℂ) • x ∈ R := by
    intro t x hx
    change periodOneHminusConjugation ((t : ℂ) • x) = (t : ℂ) • x
    rw [periodOneHminusConjugation_smul,conj_ofReal,hx]
  have hA : Continuous periodOneConjugationRealPart :=
    (continuous_id.add continuous_periodOneHminusConjugation).const_smul (1/2 : ℂ)
  have hB : Continuous periodOneConjugationImagPart :=
    (continuous_id.sub continuous_periodOneHminusConjugation).const_smul (-I/2 : ℂ)
  have hA0 : periodOneConjugationRealPart 0 = 0 := by simp [periodOneConjugationRealPart]
  have hB0 : periodOneConjugationImagPart 0 = 0 := by simp [periodOneConjugationImagPart]
  have hz := AnalyticOnNhd.eqOn_zero_of_continuous_real_form R
    (fun {_ _} hx hy => hRadd hx hy) (fun t {_} hx => hRsmul t hx)
    periodOneConjugationRealPart periodOneConjugationImagPart periodOneHminusRealPart_isReal
    periodOneHminusImagPart_isReal periodOneHminusRealPart_add_I_smul_imag
    hA.continuousAt hA0 hB.continuousAt hB0 U hU hconn
    ⟨q0,hq0,(periodOneHminusConjugation_fixed_iff q0).mpr hr0⟩ (F-G) (hF.sub hG)
    (fun q hq hqr => sub_eq_zero.mpr (he q hq ((periodOneHminusConjugation_fixed_iff q).mp hqr)))
  intro q hq
  exact sub_eq_zero.mp (hz hq)

theorem norm_periodOneHminusRealPart_le (q : PeriodOneHminusOne) :
    ‖periodOneConjugationRealPart q‖ ≤ ‖q‖ := by
  rw [periodOneConjugationRealPart,norm_smul,show ‖(1/2 : ℂ)‖ = (1/2 : ℝ) from by norm_num]
  calc
    (1/2 : ℝ)*‖q+periodOneHminusConjugation q‖ ≤
        (1/2 : ℝ)*(‖q‖+‖periodOneHminusConjugation q‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)
    _ = ‖q‖ := by rw [norm_periodOneHminusConjugation]; ring

theorem periodOneHminusRealPart_mem_ball
    (q0 q : PeriodOneHminusOne) (hr0 : IsRealPeriodOneHminusOne q0) (r : ℝ)
    (hq : q ∈ ball q0 r) : periodOneConjugationRealPart q ∈ ball q0 r := by
  have hJ := (periodOneHminusConjugation_fixed_iff q0).mpr hr0
  have he : periodOneConjugationRealPart q-q0 = periodOneConjugationRealPart (q-q0) := by
    unfold periodOneConjugationRealPart
    rw [periodOneHminusConjugation_sub,hJ]
    module
  rw [mem_ball,dist_eq_norm,he]
  exact (norm_periodOneHminusRealPart_le (q-q0)).trans_lt (by simpa only [mem_ball,dist_eq_norm] using hq)

theorem real_point_of_inter_real_centered_rough_balls
    (q0 q1 : PeriodOneHminusOne) (hr0 : IsRealPeriodOneHminusOne q0)
    (hr1 : IsRealPeriodOneHminusOne q1) (r s : ℝ)
    (h : (ball q0 r ∩ ball q1 s).Nonempty) :
    ∃ q ∈ ball q0 r ∩ ball q1 s, IsRealPeriodOneHminusOne q := by
  obtain ⟨q,hq⟩ := h
  exact ⟨periodOneConjugationRealPart q,
    ⟨periodOneHminusRealPart_mem_ball q0 q hr0 r hq.1,
      periodOneHminusRealPart_mem_ball q1 q hr1 s hq.2⟩,
    (periodOneHminusConjugation_fixed_iff _).mp (periodOneHminusRealPart_isReal q)⟩

end NLS
