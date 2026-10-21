import NLS.Dynamics.UnboundedPhaseObstruction

noncomputable section
set_option autoImplicit false
open Set Filter Topology
namespace NLS.Dynamics

/-- Diverging negative phase rotations obstruct uniform convergence even when
the amplitude is a converging continuous trajectory instead of a constant. -/
theorem not_tendsto_modulated_trajectories {ι : Type*} {l : Filter ι} [NeBot l]
    (T : ℝ) (hT : 0 < T) (freq : ι → ℝ) (hfreq : Tendsto freq l atTop)
    (r : ι → C(Icc (0 : ℝ) T,ℂ)) (R : C(Icc (0 : ℝ) T,ℂ))
    (hr : Tendsto r l (𝓝 R)) (hR : R ⟨0,le_rfl,hT.le⟩ ≠ 0)
    (g : ι → C(Icc (0 : ℝ) T,ℂ))
    (he : ∀ᶠ j in l, ∀ τ : Icc (0 : ℝ) T,
      g j τ = Complex.exp (-((τ.val*freq j : ℝ) : ℂ)*Complex.I)*r j τ)
    (G : C(Icc (0 : ℝ) T,ℂ)) : ¬ Tendsto g l (𝓝 G) := by
  intro hg
  let z : Icc (0 : ℝ) T := ⟨0,le_rfl,hT.le⟩
  have hz : G z = R z := by
    have h := (continuous_eval_const z).tendsto G |>.comp hg
    have he0 : (fun j => g j z) =ᶠ[l] (fun j => r j z) := by
      filter_upwards [he] with j hj
      simp [hj,z]
    change Tendsto (fun j => g j z) l (𝓝 (G z)) at h
    exact tendsto_nhds_unique (h.congr' he0)
      ((continuous_eval_const z).tendsto R |>.comp hr)
  let time (j : ι) : Icc (0 : ℝ) T :=
    ⟨min T (max 0 (Real.pi/freq j)),le_min hT.le (le_max_left _ _),min_le_left _ _⟩
  have hdiv : Tendsto (fun j => Real.pi/freq j) l (𝓝 (0 : ℝ)) :=
    hfreq.const_div_atTop Real.pi
  have htime : Tendsto time l (𝓝 z) := by
    apply tendsto_subtype_rng.mpr
    have hh := (tendsto_const_nhds (x := T)).min
      ((tendsto_const_nhds (x := (0 : ℝ))).max hdiv)
    simpa only [max_self,min_eq_right hT.le] using hh
  have hvalue : Tendsto (fun j => g j (time j)) l (𝓝 (G z)) :=
    continuous_eval.continuousAt.tendsto.comp (hg.prodMk_nhds htime)
  have hrvalue : Tendsto (fun j => r j (time j)) l (𝓝 (R z)) :=
    continuous_eval.continuousAt.tendsto.comp (hr.prodMk_nhds htime)
  have hphase : (fun j => g j (time j)) =ᶠ[l] (fun j => -r j (time j)) := by
    filter_upwards [he,hfreq.eventually (eventually_gt_atTop 0),
      hdiv.eventually (gt_mem_nhds hT)] with j hej hj hsmall
    have hnonneg : 0 ≤ Real.pi/freq j := div_nonneg Real.pi_pos.le hj.le
    have ht : (time j).val = Real.pi/freq j := by
      simp only [time,max_eq_right hnonneg,min_eq_right hsmall.le]
    rw [hej,ht,div_mul_cancel₀ _ hj.ne',neg_mul,Complex.exp_neg,Complex.exp_pi_mul_I]
    simp
  have hneg : Tendsto (fun j => g j (time j)) l (𝓝 (-R z)) :=
    hrvalue.neg.congr' hphase.symm
  have h := tendsto_nhds_unique hvalue hneg
  rw [hz] at h
  apply hR
  have htwo : (2 : ℂ)*R z = 0 := by linear_combination h
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

end NLS.Dynamics
