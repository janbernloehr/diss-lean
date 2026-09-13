import NLS.ComplexAnalysis.UniformProductTails

/-!
# Products close to one from small absolute perturbations

A summable absolute perturbation controls the entire unconditional product by
an exponential bound. When the total absolute perturbation tends to zero,
the product tends to one, without any nonvanishing assumptions on the factors.
-/

noncomputable section
open Filter Topology
namespace NLS.ComplexAnalysis

/-- The unconditional product error is bounded by the exponential of the total absolute perturbation. -/
theorem norm_tprod_one_add_sub_one_le_exp {ι : Type*} (u : ι → ℂ)
    (hu : Summable (fun i => ‖u i‖)) :
    ‖(∏' i, (1+u i))-1‖ ≤ Real.exp (∑' i, ‖u i‖)-1 := by
  have ht := (multipliable_one_add_of_summable hu).hasProd
  apply le_of_tendsto (ht.sub_const 1).norm
  filter_upwards [] with s
  exact (s.norm_prod_one_add_sub_one_le u).trans
    (sub_le_sub_right (Real.exp_le_exp.mpr (hu.sum_le_tsum s (fun _ _ => norm_nonneg _))) 1)

/-- Vanishing total absolute perturbation makes the corresponding products converge to one. -/
theorem tendsto_tprod_one_add_of_tsum_norm_tendsto_zero {α ι : Type*} {l : Filter α}
    (u : α → ι → ℂ) (hu : ∀ᶠ a in l, Summable (fun i => ‖u a i‖))
    (hs : Tendsto (fun a => ∑' i, ‖u a i‖) l (𝓝 0)) :
    Tendsto (fun a => ∏' i, (1+u a i)) l (𝓝 1) := by
  have hb : Tendsto (fun a => Real.exp (∑' i, ‖u a i‖)-1) l (𝓝 0) := by
    simpa using ((Real.continuous_exp.tendsto 0).comp hs).sub_const 1
  have hn : Tendsto (fun a => ‖(∏' i, (1+u a i))-1‖) l (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ hb
    filter_upwards [hu] with a ha
    exact norm_tprod_one_add_sub_one_le_exp (u a) ha
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hn

end NLS.ComplexAnalysis
