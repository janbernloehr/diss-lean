import NLS.Articles.MKdVBelowL2.ScalarSmoothMassApproximants

/-! # Fixed-time scalar obstruction from the actual physical mass

Two controlled smooth real approximation sequences give respectively the
phases one and minus one at the same fixed nonzero mass frequency. If the
remaining amplitude is continuous and nonzero at the original rough datum,
no function agreeing with the modulated smooth values can be continuous
there. The conclusion is at the selected time, rather than in a path norm.
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
theorem not_continuousAt_fixed_scalar_mass_phase_extension
    (hp : p ≠ ⊤) (h2p : 2 ≤ p) (u : PhysicalScalarRealInput p)
    (hu : ¬ physicalPairHasHilbertRepresentative (physicalScalarPairCLM u))
    (c : ℝ) (hc : c ≠ 0) (R : PhysicalScalarRealInput p → ℂ)
    (hR : ContinuousAt R u) (hRu : R u ≠ 0)
    (G : PhysicalScalarRealInput p → ℂ)
    (hG : ∀ (a : FourthClassicalSource)
      (ha : (originalWeightedRealSource _ a).val.fst = (originalWeightedRealSource _ a).val.snd),
      IsSmoothPhysicalScalarInput (fourthClassicalScalarInput h2p a ha) →
      G (fourthClassicalScalarInput h2p a ha) =
        Complex.exp (((2*Real.pi*c*(fourthClassicalMass a).re : ℝ) : ℂ)*Complex.I)*
          R (fourthClassicalScalarInput h2p a ha)) : ¬ ContinuousAt G u := by
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
  have hea : (fun j => G (fourthClassicalScalarInput h2p (a j) (ha j))) =
      fun j => R (fourthClassicalScalarInput h2p (a j) (ha j)) := by
    funext j
    rw [hG (a j) (ha j) (hsa j),hp0,one_mul]
  have heb : (fun j => G (fourthClassicalScalarInput h2p (b j) (hb j))) =
      fun j => -R (fourthClassicalScalarInput h2p (b j) (hb j)) := by
    funext j
    rw [hG (b j) (hb j) (hsb j),hp1,neg_one_mul]
  have hga := hcont.tendsto.comp hta
  have hgb := hcont.tendsto.comp htb
  dsimp only [Function.comp_def] at hga hgb
  rw [hea] at hga
  rw [heb] at hgb
  have he0 : G u = R u := tendsto_nhds_unique hga (hR.tendsto.comp hta)
  have he1 : G u = -R u := tendsto_nhds_unique hgb (hR.tendsto.comp htb).neg
  apply hRu
  have hh : (2:ℂ)*R u = 0 := by linear_combination he1-he0
  exact (mul_eq_zero.mp hh).resolve_left (by norm_num)

end NLS.Articles.MKdVBelowL2
