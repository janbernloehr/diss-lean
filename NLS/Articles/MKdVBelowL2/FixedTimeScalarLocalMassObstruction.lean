import NLS.Articles.MKdVBelowL2.FixedTimeScalarMassObstruction

/-! # Fixed-time mass obstruction with only local smooth agreement

Agreement on a neighborhood of the rough datum suffices: both controlled
smooth approximation sequences eventually enter that same neighborhood.
-/
noncomputable section
set_option autoImplicit false
open Set Filter Topology Complex
open scoped ENNReal
namespace NLS.Articles.MKdVBelowL2
open NLS.ZakharovShabat NLS.Dynamics
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A nonzero fixed mass phase prevents continuous extension at every
non-Hilbert original real scalar datum with nonzero continuous amplitude. -/
theorem not_continuousWithinAt_fixed_scalar_mass_phase_extension_of_mem_nhds
    (hp : p ≠ ⊤) (h2p : 2 ≤ p) (u : PhysicalScalarRealInput p)
    (hu : ¬ physicalPairHasHilbertRepresentative (physicalScalarPairCLM u))
    (c : ℝ) (hc : c ≠ 0) (R : PhysicalScalarRealInput p → ℂ)
    (hR : ContinuousAt R u) (hRu : R u ≠ 0)
    (G : PhysicalScalarRealInput p → ℂ) (U : Set (PhysicalScalarRealInput p)) (hU : U ∈ 𝓝 u)
    (V : Set (PhysicalScalarRealInput p))
    (hV : ∀ v ∈ U, IsSmoothPhysicalScalarInput v → v ∈ V)
    (hG : ∀ (a : FourthClassicalSource)
      (ha : (originalWeightedRealSource _ a).val.fst = (originalWeightedRealSource _ a).val.snd),
      IsSmoothPhysicalScalarInput (fourthClassicalScalarInput h2p a ha) →
      fourthClassicalScalarInput h2p a ha ∈ U →
      G (fourthClassicalScalarInput h2p a ha) =
        Complex.exp (((2*Real.pi*c*(fourthClassicalMass a).re : ℝ) : ℂ)*Complex.I)*
          R (fourthClassicalScalarInput h2p a ha)) : ¬ ContinuousWithinAt G V u := by
  intro hcont
  obtain ⟨a,ha,hsa,hta,hpa⟩ := exists_smooth_scalar_mass_phase_sequence hp h2p u hu |c| 0 (abs_pos.mpr hc) le_rfl
  obtain ⟨b,hb,hsb,htb,hpb⟩ := exists_smooth_scalar_mass_phase_sequence hp h2p u hu |c| (1/2) (abs_pos.mpr hc) (by norm_num)
  have hp0 (j : ℕ) : Complex.exp (((2*Real.pi*c*(fourthClassicalMass (a j)).re : ℝ) : ℂ)*Complex.I) = 1 := by
    apply exp_signed_mass_phase c _ 1 (Or.inl rfl)
    simpa only [mul_zero,Complex.ofReal_zero,zero_mul,Complex.exp_zero] using hpa j
  have hhalf : Complex.exp (((2*Real.pi*(1/2:ℝ) : ℝ) : ℂ)*Complex.I) = -1 := by
    have he : (((2*Real.pi*(1/2:ℝ) : ℝ) : ℂ)*Complex.I) = (Real.pi : ℂ)*Complex.I := by push_cast; ring
    rw [he,Complex.exp_pi_mul_I]
  have hp1 (j : ℕ) : Complex.exp (((2*Real.pi*c*(fourthClassicalMass (b j)).re : ℝ) : ℂ)*Complex.I) = -1 := by
    apply exp_signed_mass_phase c _ (-1) (Or.inr rfl)
    exact (hpb j).trans hhalf
  have hea : (fun j => G (fourthClassicalScalarInput h2p (a j) (ha j))) =ᶠ[atTop]
      fun j => R (fourthClassicalScalarInput h2p (a j) (ha j)) := by
    filter_upwards [hta.eventually hU] with j hj
    rw [hG (a j) (ha j) (hsa j) hj,hp0,one_mul]
  have heb : (fun j => G (fourthClassicalScalarInput h2p (b j) (hb j))) =ᶠ[atTop]
      fun j => -R (fourthClassicalScalarInput h2p (b j) (hb j)) := by
    filter_upwards [htb.eventually hU] with j hj
    rw [hG (b j) (hb j) (hsb j) hj,hp1,neg_one_mul]
  have htaV : Tendsto (fun j => fourthClassicalScalarInput h2p (a j) (ha j)) atTop (𝓝[V] u) :=
    tendsto_nhdsWithin_iff.mpr ⟨hta,by
      filter_upwards [hta.eventually hU] with j hj
      exact hV _ hj (hsa j)⟩
  have htbV : Tendsto (fun j => fourthClassicalScalarInput h2p (b j) (hb j)) atTop (𝓝[V] u) :=
    tendsto_nhdsWithin_iff.mpr ⟨htb,by
      filter_upwards [htb.eventually hU] with j hj
      exact hV _ hj (hsb j)⟩
  have hga : Tendsto (fun j => R (fourthClassicalScalarInput h2p (a j) (ha j))) atTop (𝓝 (G u)) :=
    (hcont.tendsto.comp htaV).congr' hea
  have hgb : Tendsto (fun j => -R (fourthClassicalScalarInput h2p (b j) (hb j))) atTop (𝓝 (G u)) :=
    (hcont.tendsto.comp htbV).congr' heb
  have he0 : G u = R u := tendsto_nhds_unique hga (hR.tendsto.comp hta)
  have he1 : G u = -R u := tendsto_nhds_unique hgb (hR.tendsto.comp htb).neg
  apply hRu
  have hh : (2:ℂ)*R u = 0 := by linear_combination he1-he0
  exact (mul_eq_zero.mp hh).resolve_left (by norm_num)

/-- In particular no ambient continuous extension can agree locally. -/
theorem not_continuousAt_fixed_scalar_mass_phase_extension_of_mem_nhds
    (hp : p ≠ ⊤) (h2p : 2 ≤ p) (u : PhysicalScalarRealInput p)
    (hu : ¬ physicalPairHasHilbertRepresentative (physicalScalarPairCLM u))
    (c : ℝ) (hc : c ≠ 0) (R : PhysicalScalarRealInput p → ℂ)
    (hR : ContinuousAt R u) (hRu : R u ≠ 0)
    (G : PhysicalScalarRealInput p → ℂ) (U : Set (PhysicalScalarRealInput p)) (hU : U ∈ 𝓝 u)
    (hG : ∀ (a : FourthClassicalSource)
      (ha : (originalWeightedRealSource _ a).val.fst = (originalWeightedRealSource _ a).val.snd),
      IsSmoothPhysicalScalarInput (fourthClassicalScalarInput h2p a ha) →
      fourthClassicalScalarInput h2p a ha ∈ U →
      G (fourthClassicalScalarInput h2p a ha) =
        Complex.exp (((2*Real.pi*c*(fourthClassicalMass a).re : ℝ) : ℂ)*Complex.I)*
          R (fourthClassicalScalarInput h2p a ha)) : ¬ ContinuousAt G u := by
  simpa only [continuousWithinAt_univ] using
    not_continuousWithinAt_fixed_scalar_mass_phase_extension_of_mem_nhds hp h2p u hu c hc R hR hRu G U hU
      univ (fun _ _ _ => mem_univ _) hG

end NLS.Articles.MKdVBelowL2
