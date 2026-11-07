import NLS.ComplexAnalysis.EnergySqrtCoordinates
import NLS.ComplexAnalysis.QuadraticEnergyLoop
import NLS.ComplexAnalysis.RealCenteredCircleHomotopy

/-! Exact local square-root loop transport. Squaring the transported
loop recovers every original energy integral, and its positive-disk
winding is fixed by the original energy winding. -/
noncomputable section
open Set Metric Complex
namespace NLS.ComplexAnalysis
namespace PiecewiseC1Loop

def frequencyLoop (Γ : PiecewiseC1Loop) (c : ℂ) (hΓ : Γ.Inside (energyFrequencyDomain c)) : PiecewiseC1Loop :=
  Γ.mapOn (energyFrequency c) (energyFrequencyDomain c) ((contDiffOn_energyFrequency c).of_le (by norm_num)) hΓ

theorem integral_frequencyLoop (Γ : PiecewiseC1Loop) (c : ℂ) (hΓ : Γ.Inside (energyFrequencyDomain c))
    (f g : ℂ → ℂ)
    (hpull : ∀ E ∈ energyFrequencyDomain c, f (energyFrequency c E)/(2*energyFrequency c E) = g E) :
    (Γ.frequencyLoop c hΓ).integral f = Γ.integral g := by
  apply Γ.integral_mapOn_of_holomorphic_pullback _ _ _ _ (fun E => 1/(2*energyFrequency c E)) f g
    (fun E hE => hasDerivAt_energyFrequency c E hE)
  intro E hE
  simpa only [one_div,div_eq_mul_inv,one_mul] using hpull E hE

theorem integral_energy_frequencyLoop (Γ : PiecewiseC1Loop) (c : ℂ)
    (hΓ : Γ.Inside (energyFrequencyDomain c)) (f : ℂ → ℂ) :
    (quadraticEnergyLoop (Γ.frequencyLoop c hΓ) c).integral f = Γ.integral f := by
  have he : (quadraticEnergyLoop (Γ.frequencyLoop c hΓ) c).integral f =
      (Γ.frequencyLoop c hΓ).integral (fun z => f (z^2-c)*(2*z)) := by
    apply integral_quadraticEnergyLoop _ c _ _ univ (fun _ _ => mem_univ _)
    intro z _
    rfl
  rw [he]
  apply Γ.integral_frequencyLoop c hΓ
  intro E hE
  rw [energyFrequency_sq,add_sub_cancel_right]
  have hn := energyFrequency_ne_zero c E hE
  field_simp

theorem windingIntegral_frequencyLoop_quadratic (Γ : PiecewiseC1Loop) (c : ℂ)
    (hΓ : Γ.Inside (energyFrequencyDomain c)) (a : ℂ)
    (havoid : (Γ.frequencyLoop c hΓ).Inside {z : ℂ | z ≠ a ∧ z ≠ -a}) :
    Γ.windingIntegral (a^2-c) =
      (Γ.frequencyLoop c hΓ).windingIntegral a+(Γ.frequencyLoop c hΓ).windingIntegral (-a) := by
  have he : (quadraticEnergyLoop (Γ.frequencyLoop c hΓ) c).windingIntegral (a^2-c) = Γ.windingIntegral (a^2-c) := by
    unfold windingIntegral normalizedIntegral
    rw [Γ.integral_energy_frequencyLoop c hΓ]
  rw [← he]
  exact windingIntegral_quadraticEnergyLoop _ c a havoid

theorem windingIntegral_zero_of_inside_ball (Γ : PiecewiseC1Loop) (b a : ℂ) (R : ℝ)
    (hΓ : Γ.Inside (ball b R)) (ha : a ∉ ball b R) : Γ.windingIntegral a = 0 := by
  have hf : AnalyticOnNhd ℂ (fun z : ℂ => (z-a)⁻¹) (ball b R) := by
    intro z hz
    have hne : z ≠ a := by intro he; exact ha (he ▸ hz)
    exact (analyticAt_id.sub analyticAt_const).inv (sub_ne_zero.mpr hne)
  obtain ⟨F,hF⟩ := exists_primitive_on_convex (fun z : ℂ => (z-a)⁻¹) (ball b R)
    (convex_ball b R) isOpen_ball hf.differentiableOn
  unfold windingIntegral normalizedIntegral
  rw [Γ.integral_eq_zero_of_primitive _ F _ hf.continuousOn hF hΓ,mul_zero]

theorem frequencyLoop_winding_one_of_positive_disk (Γ : PiecewiseC1Loop) (c : ℂ)
    (hΓ : Γ.Inside (energyFrequencyDomain c)) (b R : ℝ) (a : ℂ)
    (hpos : 0 < b-R) (hball : (Γ.frequencyLoop c hΓ).Inside (ball (b:ℂ) R))
    (ha : a ∈ ball (b:ℂ) R) (havoid : (Γ.frequencyLoop c hΓ).Inside {z : ℂ | z ≠ a})
    (hwind : Γ.windingIntegral (a^2-c) = 1) : (Γ.frequencyLoop c hΓ).windingIntegral a = 1 := by
  have hare : 0 < a.re := by
    have hb := re_bounds_of_mem_realCenteredClosedBall (ball_subset_closedBall ha)
    linarith [hb.1]
  have hneg : -a ∉ ball (b:ℂ) R := by
    intro hn
    have hb := re_bounds_of_mem_realCenteredClosedBall (ball_subset_closedBall hn)
    simp only [neg_re] at hb
    linarith [hb.1]
  have hz := (Γ.frequencyLoop c hΓ).windingIntegral_zero_of_inside_ball (b:ℂ) (-a) R hball hneg
  have hfull : (Γ.frequencyLoop c hΓ).Inside {z : ℂ | z ≠ a ∧ z ≠ -a} := by
    intro i t
    exact ⟨havoid i t,fun he => hneg (he ▸ hball i t)⟩
  have he := Γ.windingIntegral_frequencyLoop_quadratic c hΓ a hfull
  rw [hwind,hz,add_zero] at he
  exact he.symm

end PiecewiseC1Loop
end NLS.ComplexAnalysis
