import NLS.KdV.ClassicalBranchPrimitive

/-! # Uniform control of the normalized Hill cosh branch

Inside the canonical imaginary strip, cosh(z) approaching one forces z
to approach zero. The filter formulation gives a single delta for all
such z, not a branch chart selected separately at each spectral point.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
namespace NLS.KdV

theorem tendsto_zero_of_cosh_tendsto_one_in_strip
    {A : Type*} {l : Filter A} (f : A → ℂ)
    (hcosh : Tendsto (fun i => cosh (f i)) l (𝓝 1))
    (hstrip : ∀ᶠ i in l, |(f i).im| < Real.pi/2) : Tendsto f l (𝓝 0) := by
  have he (z : ℂ) : cosh z^2-1 = sinh z^2 := by
    linear_combination cosh_sq_sub_sinh_sq z
  have hsq : Tendsto (fun i => sinh (f i)^2) l (𝓝 0) := by
    simpa only [one_pow,sub_self,he] using (hcosh.pow 2).sub_const 1
  have hsinh : Tendsto (fun i => sinh (f i)) l (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hn : Tendsto (fun i => ‖sinh (f i)^2‖) l (𝓝 0) := by
      simpa only [norm_zero] using hsq.norm
    have h := Real.continuous_sqrt.continuousAt.tendsto.comp hn
    simpa only [Function.comp_def,norm_pow,Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero] using h
  have hexp : Tendsto (fun i => exp (f i)) l (𝓝 1) := by
    simpa only [cosh_add_sinh,add_zero] using hcosh.add hsinh
  have hlog := (continuousAt_clog (by simp : (1 : ℂ) ∈ slitPlane)).tendsto.comp hexp
  have ht : Tendsto (fun i => log (exp (f i))) l (𝓝 0) := by
    simpa only [Function.comp_def,log_one] using hlog
  apply ht.congr'
  filter_upwards [hstrip] with i hi
  exact log_exp (by linarith [(abs_lt.mp hi).1,Real.pi_pos])
    (by linarith [(abs_lt.mp hi).2,Real.pi_pos])

/-- One smallness threshold controls every point of the canonical strip. -/
theorem exists_delta_cosh_strip_control (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ z : ℂ, |z.im| < Real.pi/2 →
      ‖cosh z-1‖ < delta → ‖z‖ < epsilon := by
  let S : Set ℂ := {z | |z.im| < Real.pi/2}
  let l : Filter ℂ := comap cosh (𝓝 (1 : ℂ)) ⊓ 𝓟 S
  have hc : Tendsto cosh l (𝓝 1) := tendsto_comap.mono_left inf_le_left
  have hstrip : ∀ᶠ z in l, |z.im| < Real.pi/2 := mem_inf_of_right (by simp [S])
  have ht : Tendsto (id : ℂ → ℂ) l (𝓝 0) :=
    tendsto_zero_of_cosh_tendsto_one_in_strip id hc hstrip
  have hev : ∀ᶠ z in l, ‖z‖ < epsilon := by
    simpa only [id_eq,mem_ball,dist_zero_right] using ht.eventually (ball_mem_nhds 0 hepsilon)
  have hb : l.HasBasis (fun delta : ℝ => 0 < delta)
      (fun delta => cosh ⁻¹' ball (1 : ℂ) delta ∩ S) :=
    (nhds_basis_ball.comap cosh).inf_principal S
  obtain ⟨delta,hdelta,hbound⟩ := hb.eventually_iff.mp hev
  refine ⟨delta,hdelta,?_⟩
  intro z hz hsmall
  exact hbound ⟨by simpa only [mem_preimage,mem_ball,dist_eq_norm] using hsmall,hz⟩

end NLS.KdV
