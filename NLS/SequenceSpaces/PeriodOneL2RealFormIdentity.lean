import NLS.SequenceSpaces.PeriodOneMiuraConjugation
import NLS.ComplexAnalysis.ContinuousRealFormIdentity
import NLS.ComplexAnalysis.ConjugateAnalytic

/-! # Real-form uniqueness and conjugate analytic transport in period-one L2 -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ComplexConjugate
namespace NLS

theorem periodOneL2Conjugation_smul (c : ℂ) (u : Coeff 2) :
    periodOneL2Conjugation (c • u) = conj c • periodOneL2Conjugation u := by
  ext j
  simp only [periodOneL2Conjugation_apply,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,map_mul]

theorem periodOneL2Conjugation_sub (u v : Coeff 2) :
    periodOneL2Conjugation (u-v) = periodOneL2Conjugation u-periodOneL2Conjugation v := by
  ext j
  simp only [periodOneL2Conjugation_apply,lp.coeFn_sub,Pi.sub_apply,map_sub]

theorem continuous_periodOneL2Conjugation : Continuous periodOneL2Conjugation :=
  continuous_star.comp Coeff.reflection.continuous

@[simp] theorem periodOneL2Conjugation_zero : periodOneL2Conjugation 0 = 0 := by ext j; simp

def periodOneL2RealPart (u : Coeff 2) : Coeff 2 := (1/2 : ℂ) • (u+periodOneL2Conjugation u)
def periodOneL2ImagPart (u : Coeff 2) : Coeff 2 := (-I/2 : ℂ) • (u-periodOneL2Conjugation u)

theorem periodOneL2RealPart_fixed (u : Coeff 2) :
    periodOneL2Conjugation (periodOneL2RealPart u) = periodOneL2RealPart u := by
  rw [periodOneL2RealPart,periodOneL2Conjugation_smul,periodOneL2Conjugation_add,periodOneL2Conjugation_involutive]
  simp only [map_div₀,map_one,map_ofNat]
  rw [add_comm u]

theorem periodOneL2ImagPart_fixed (u : Coeff 2) :
    periodOneL2Conjugation (periodOneL2ImagPart u) = periodOneL2ImagPart u := by
  rw [periodOneL2ImagPart,periodOneL2Conjugation_smul,periodOneL2Conjugation_sub,periodOneL2Conjugation_involutive]
  simp only [map_div₀,map_neg,conj_I,map_ofNat,neg_neg]
  module

theorem periodOneL2RealPart_add_I_imagPart (u : Coeff 2) :
    u = periodOneL2RealPart u+I • periodOneL2ImagPart u := by
  unfold periodOneL2RealPart periodOneL2ImagPart
  rw [smul_smul]
  have he : (I : ℂ)*(-I/2)=1/2 := by rw [mul_div,mul_neg,I_mul_I,neg_neg]
  rw [he,← smul_add]
  have hs : u+periodOneL2Conjugation u+(u-periodOneL2Conjugation u)=(2 : ℂ) • u := by module
  rw [hs,smul_smul]
  norm_num

theorem periodOneL2_real_form_identity {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {U : Set (Coeff 2)} (hU : IsOpen U) (hconn : IsPreconnected U) (h0U : (0 : Coeff 2) ∈ U)
    (F G : Coeff 2 → E) (hF : AnalyticOnNhd ℂ F U) (hG : AnalyticOnNhd ℂ G U)
    (he : ∀ u ∈ U, periodOneL2Conjugation u = u → F u = G u) : EqOn F G U := by
  let R : Set (Coeff 2) := {u | periodOneL2Conjugation u = u}
  have hRadd : ∀ {x y : Coeff 2}, x ∈ R → y ∈ R → x+y ∈ R := by
    intro x y hx hy
    change periodOneL2Conjugation (x+y)=x+y
    rw [periodOneL2Conjugation_add,hx,hy]
  have hRsmul : ∀ t : ℝ, ∀ {x : Coeff 2}, x ∈ R → (t : ℂ) • x ∈ R := by
    intro t x hx
    change periodOneL2Conjugation ((t : ℂ) • x)=(t : ℂ) • x
    rw [periodOneL2Conjugation_smul,conj_ofReal,hx]
  have hA : Continuous periodOneL2RealPart :=
    (continuous_id.add continuous_periodOneL2Conjugation).const_smul (1/2 : ℂ)
  have hB : Continuous periodOneL2ImagPart :=
    (continuous_id.sub continuous_periodOneL2Conjugation).const_smul (-I/2 : ℂ)
  have hA0 : periodOneL2RealPart 0 = 0 := by simp [periodOneL2RealPart]
  have hB0 : periodOneL2ImagPart 0 = 0 := by simp [periodOneL2ImagPart]
  have hz := AnalyticOnNhd.eqOn_zero_of_continuous_real_form R
    (fun {_ _} hx hy => hRadd hx hy) (fun t {_} hx => hRsmul t hx)
    periodOneL2RealPart periodOneL2ImagPart periodOneL2RealPart_fixed periodOneL2ImagPart_fixed
    periodOneL2RealPart_add_I_imagPart hA.continuousAt hA0 hB.continuousAt hB0 U hU hconn
    ⟨0,h0U,periodOneL2Conjugation_zero⟩ (F-G) (hF.sub hG)
    (fun u hu hr => sub_eq_zero.mpr (he u hu hr))
  exact fun u hu => sub_eq_zero.mp (hz hu)

theorem analyticOnNhd_periodOneL2_conjugate (T : Coeff 2 → Coeff 2) (η : ℝ)
    (hT : AnalyticOnNhd ℂ T (ball (0 : Coeff 2) η)) :
    AnalyticOnNhd ℂ (fun u => periodOneL2Conjugation (T (periodOneL2Conjugation u))) (ball (0 : Coeff 2) η) := by
  let L := (Coeff.reflection (p := 2)).toContinuousLinearEquiv.toContinuousLinearMap
  let H := fun u => Coeff.reflection (T u)
  have hHa : AnalyticOnNhd ℂ H (ball (0 : Coeff 2) η) := fun u hu => (L.analyticAt _).comp (hT u hu)
  intro u hu
  have hJu : periodOneL2Conjugation u ∈ ball (0 : Coeff 2) η := by
    rwa [mem_ball_zero_iff,norm_periodOneL2Conjugation,← mem_ball_zero_iff]
  have hs := analyticAt_star_star (hHa _ hJu)
  simp only [periodOneL2Conjugation,star_star] at hs
  exact hs.comp (f := Coeff.reflection) (L.analyticAt u)

end NLS
