import NLS.ComplexAnalysis.ContinuousRealFormIdentity

/-! # Real-form uniqueness and ball overlaps from an isometric conjugation

The physical real projection is contractive. Thus any overlap of two
balls centered on the real form contains a real point. Analytic maps
agreeing on the real form agree on every such overlap, on its whole
unchanged complex domain.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
namespace NLS.ComplexAnalysis
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def conjugationRealPart (J : E ≃ₗᵢ⋆[ℂ] E) (v : E) : E := (1/2 : ℂ) • (v+J v)
def conjugationImagPart (J : E ≃ₗᵢ⋆[ℂ] E) (v : E) : E := (1/(2*I) : ℂ) • (v-J v)

theorem conjugationRealPart_fixed (J : E ≃ₗᵢ⋆[ℂ] E) (hJ : ∀ v, J (J v) = v) (v : E) :
    J (conjugationRealPart J v) = conjugationRealPart J v := by
  simp only [conjugationRealPart,map_smulₛₗ,map_add,hJ]
  simp only [starRingEnd_apply,star_div₀,star_one,star_ofNat]
  rw [add_comm]

theorem conjugationRealPart_of_fixed (J : E ≃ₗᵢ⋆[ℂ] E) (v : E) (hv : J v = v) :
    conjugationRealPart J v = v := by
  dsimp only [conjugationRealPart]
  rw [hv]
  module

theorem conjugationImagPart_fixed (J : E ≃ₗᵢ⋆[ℂ] E) (hJ : ∀ v, J (J v) = v) (v : E) :
    J (conjugationImagPart J v) = conjugationImagPart J v := by
  simp only [conjugationImagPart,map_smulₛₗ,map_sub,hJ]
  have hc : starRingEnd ℂ (1/(2*I)) = -(1/(2*I)) := by
    simp only [map_div₀,map_one,map_mul,map_ofNat,conj_I,div_neg,mul_neg]
  rw [hc]
  module

theorem conjugation_real_imag_decomp (J : E ≃ₗᵢ⋆[ℂ] E) (v : E) :
    v = conjugationRealPart J v+I • conjugationImagPart J v := by
  dsimp only [conjugationRealPart,conjugationImagPart]
  have hc : I*(1/(2*I) : ℂ) = 1/2 := by field_simp
  rw [smul_smul,hc]
  module

theorem continuous_conjugationRealPart (J : E ≃ₗᵢ⋆[ℂ] E) : Continuous (conjugationRealPart J) :=
  continuous_const.smul (continuous_id.add J.continuous)

theorem continuous_conjugationImagPart (J : E ≃ₗᵢ⋆[ℂ] E) : Continuous (conjugationImagPart J) :=
  continuous_const.smul (continuous_id.sub J.continuous)

theorem isPreconnected_fixed_real_form (J : E ≃ₗᵢ⋆[ℂ] E) (hJ : ∀ v, J (J v) = v) :
    IsPreconnected {v : E | J v = v} := by
  have he : range (conjugationRealPart J) = {v : E | J v = v} := by
    ext v
    constructor
    · rintro ⟨u,rfl⟩
      exact conjugationRealPart_fixed J hJ u
    · intro hv
      exact ⟨v,conjugationRealPart_of_fixed J v hv⟩
  rw [← he]
  exact isPreconnected_range (continuous_conjugationRealPart J)

theorem norm_conjugationRealPart_le (J : E ≃ₗᵢ⋆[ℂ] E) (v : E) :
    ‖conjugationRealPart J v‖ ≤ ‖v‖ := by
  unfold conjugationRealPart
  rw [norm_smul]
  have hb := norm_add_le v (J v)
  rw [J.norm_map] at hb
  norm_num
  linarith

theorem conjugationRealPart_sub_fixed (J : E ≃ₗᵢ⋆[ℂ] E) (v a : E) (ha : J a = a) :
    conjugationRealPart J (v-a) = conjugationRealPart J v-a := by
  dsimp only [conjugationRealPart]
  rw [map_sub,ha]
  module

theorem exists_fixed_mem_ball_inter (J : E ≃ₗᵢ⋆[ℂ] E) (hJ : ∀ v, J (J v) = v)
    (a b : E) (ha : J a = a) (hb : J b = b) (r s : ℝ)
    (hne : (ball a r ∩ ball b s).Nonempty) :
    ∃ v ∈ ball a r ∩ ball b s, J v = v := by
  obtain ⟨z,hza,hzb⟩ := hne
  refine ⟨conjugationRealPart J z,⟨?_,?_⟩,conjugationRealPart_fixed J hJ z⟩
  · rw [mem_ball,dist_eq_norm,← conjugationRealPart_sub_fixed J z a ha]
    exact (norm_conjugationRealPart_le J (z-a)).trans_lt (by simpa only [mem_ball,dist_eq_norm] using hza)
  · rw [mem_ball,dist_eq_norm,← conjugationRealPart_sub_fixed J z b hb]
    exact (norm_conjugationRealPart_le J (z-b)).trans_lt (by simpa only [mem_ball,dist_eq_norm] using hzb)

theorem analytic_eqOn_of_fixed_real_form (J : E ≃ₗᵢ⋆[ℂ] E) (hJ : ∀ v, J (J v) = v)
    (U : Set E) (hU : IsOpen U) (hconn : IsPreconnected U)
    (hne : ∃ v ∈ U, J v = v) (f g : E → ℂ)
    (hf : AnalyticOnNhd ℂ f U) (hg : AnalyticOnNhd ℂ g U)
    (he : ∀ v ∈ U, J v = v → f v = g v) : EqOn f g U := by
  have hzero := AnalyticOnNhd.eqOn_zero_of_continuous_real_form
    {v : E | J v = v}
    (fun x y hx hy => by simp only [mem_ofPred_eq] at hx hy ⊢; rw [map_add,hx,hy])
    (fun t x hx => by
      change J ((t : ℂ) • x) = (t : ℂ) • x
      rw [map_smulₛₗ,hx]
      simp)
    (conjugationRealPart J) (conjugationImagPart J)
    (conjugationRealPart_fixed J hJ) (conjugationImagPart_fixed J hJ)
    (conjugation_real_imag_decomp J)
    (continuous_conjugationRealPart J).continuousAt (by simp [conjugationRealPart])
    (continuous_conjugationImagPart J).continuousAt (by simp [conjugationImagPart])
    U hU hconn (by obtain ⟨v,hv,hvr⟩ := hne; exact ⟨v,hv,hvr⟩)
    (fun v => f v-g v) (hf.sub hg) (fun v hv hvr => sub_eq_zero.mpr (he v hv hvr))
  intro v hv
  exact sub_eq_zero.mp (hzero hv)

end NLS.ComplexAnalysis
