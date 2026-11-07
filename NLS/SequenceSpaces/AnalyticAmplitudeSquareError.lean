import NLS.SequenceSpaces.WeightedPhysicalRealFormIdentity
import NLS.SequenceSpaces.PositiveBoundedAnalyticFamily

/-! Analytic physical squared-amplitude identities give a common
complex quantitative bound on the SAME original weighted source. -/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.WeightedCoeff

theorem exists_local_analytic_amplitude_square_error
    (v : Weight) (hv : ∀ j,v (-j)=v j)
    (V W : Set (WeightedCoeff v 2)) (hV : IsOpen V) (hW : IsOpen W)
    (q : WeightedCoeff v 2) (hqV : q∈V) (hqW : q∈W) (hJq : conjugateReflection v hv q=q)
    (A : WeightedCoeff v 2 → Coeff ⊤) (hAa : AnalyticOnNhd ℂ A W)
    (a : ℕ+ → ℝ) (R : ℕ+ → WeightedCoeff v 2 → ℂ) (N : ℕ) (K : ℝ)
    (hR : ∀ n : ℕ+,N≤(n:ℕ) → AnalyticOnNhd ℂ (R n) V ∧
      ∀ p∈V,(1+(n:ℝ))*‖(2*((Real.pi:ℂ)*(n:ℕ)))*R n p-1‖≤K)
    (he : ∀ n : ℕ+,N≤(n:ℕ) → ∀ p∈V∩W,conjugateReflection v hv p=p →
      (A p (n:ℤ)/(a n:ℂ))^2=(2*((Real.pi:ℂ)*(n:ℕ)))*R n p) :
    ∃ U : Set (WeightedCoeff v 2),IsOpen U ∧ q∈U ∧ U⊆V∩W ∧
      ∀ n : ℕ+,N≤(n:ℕ) → ∀ p∈U,(1+(n:ℝ))*‖(A p (n:ℤ)/(a n:ℂ))^2-1‖≤K := by
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp ((hV.inter hW).mem_nhds ⟨hqV,hqW⟩)
  let U := ball q r
  refine ⟨U,isOpen_ball,mem_ball_self hr,hball,?_⟩
  intro n hn
  let F := fun p => (A p (n:ℤ)/(a n:ℂ))^2
  let G := fun p => (2*((Real.pi:ℂ)*(n:ℕ)))*R n p
  have hF : AnalyticOnNhd ℂ F U := fun p hp =>
    (((((lp.evalCLM ℂ (fun _ : ℤ => ℂ) ⊤ (n:ℤ)).analyticAt _).comp (hAa p (hball hp).2)).div_const).pow 2)
  have hG : AnalyticOnNhd ℂ G U := analyticOnNhd_const.mul ((hR n hn).1.mono (fun p hp => (hball hp).1))
  have hid := physical_real_form_identity v hv U isOpen_ball (convex_ball q r).isPreconnected q
    (mem_ball_self hr) hJq F G hF hG (fun p hp hJp => he n hn p (hball hp) hJp)
  intro p hp
  have hb := (hR n hn).2 p (hball hp).1
  change (1+(n:ℝ))*‖G p-1‖≤K at hb
  rw [←hid hp] at hb
  exact hb

end NLS.WeightedCoeff
