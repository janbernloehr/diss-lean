import NLS.Articles.KdVKdV2Frequencies.OriginalActionHamiltonians

/-! # Intrinsic physical hierarchy frequencies at every native action point

The frequencies are defined as actual derivatives of the independent physical
Hamiltonians along positive action rays. Every genuine analytic factor gives
the same unscaled positive coordinate derivative, including all closed gaps.
-/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.KdV
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies

namespace OriginalHierarchyActionFactor
variable {D : GlobalRoughAbelianForwardData} {m : ℕ} {r : ℝ} {hrs : r=2*((m : ℝ)+1/2)}

/-- The unscaled original positive action derivative of this factor. -/
def frequency (F : OriginalHierarchyActionFactor D m r hrs)
    (a : WeightedCoeff (Weight.sobolev r) 1) (n : ℕ+) : ℝ :=
  ((fderiv ℂ F.value a) (WeightedCoeff.single (Weight.sobolev r) (n : ℤ) 1)).re

/-- The positive action derivative is physically real at every actual action point. -/
theorem frequency_complex_value (F : OriginalHierarchyActionFactor D m r hrs)
    (a : WeightedCoeff.positiveActionLocus (Weight.sobolev r) 1) (n : ℕ+) :
    (F.frequency a.val n : ℂ) =
      (fderiv ℂ F.value a.val) (WeightedCoeff.single (Weight.sobolev r) (n : ℤ) 1) := by
  apply Complex.ext
  · rfl
  · exact (WeightedCoeff.fderiv_single_im_eq_zero_of_positive_action_recovery F.value a.val
      a.property n (by exact_mod_cast n.pos)
      (F.analytic a.val (F.nonnegative_subset_domain a.property.1)).differentiableAt
      (fun b hb => F.value_im_eq_zero ⟨b,hb⟩)).symm

/-- The SAME original action neighborhood works for every scalar frequency. -/
theorem frequency_analytic (F : OriginalHierarchyActionFactor D m r hrs) (n : ℕ+) :
    AnalyticOnNhd ℝ (fun a => F.frequency a n) F.domain := by
  intro a ha
  exact (Complex.reCLM.analyticAt _).comp
    ((WeightedCoeff.analyticOnNhd_fderiv_single F.value F.analytic (n : ℤ) a ha).restrictScalars (𝕜 := ℝ))

/-- Positive frequencies are independent of the chosen analytic factor at
EVERY actual action point, including every closed gap and infinite support. -/
theorem frequency_eq (F G : OriginalHierarchyActionFactor D m r hrs)
    (a : WeightedCoeff.positiveActionLocus (Weight.sobolev r) 1) (n : ℕ+) :
    F.frequency a.val n = G.frequency a.val n := by
  apply congrArg Complex.re
  exact WeightedCoeff.fderiv_single_eq_of_positive_action_recovery F.value G.value a.val a.property n
    (by exact_mod_cast n.pos)
    (F.analytic a.val (F.nonnegative_subset_domain a.property.1)).differentiableAt
    (G.analytic a.val (G.nonnegative_subset_domain a.property.1)).differentiableAt
    (fun b hb => F.value_eq_on_positive_actions G ⟨b,hb⟩)

/-- The actual physical Hamiltonian, evaluated at real native potentials with
one increased action, has this right derivative even at a closed gap. -/
theorem hasDerivWithinAt_physical_actionHamiltonian
    (F : OriginalHierarchyActionFactor D m r hrs)
    (a : WeightedCoeff.positiveActionLocus (Weight.sobolev r) 1) (n : ℕ+) :
    HasDerivWithinAt (fun t : ℝ => D.originalActionHamiltonian m r hrs
      (WeightedCoeff.positiveActionRay (Weight.sobolev r) 1 a n t))
      (F.frequency a.val n) (Ici 0) 0 := by
  have hd := NLS.ComplexAnalysis.hasDerivAt_comp_real_action_line F.value a.val
    (WeightedCoeff.single (Weight.sobolev r) (n : ℤ) 1)
    (F.analytic a.val (F.nonnegative_subset_domain a.property.1)).differentiableAt
  have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 hd
  have he (t : ℝ) (ht : 0 ≤ t) :
      D.originalActionHamiltonian m r hrs (WeightedCoeff.positiveActionRay (Weight.sobolev r) 1 a n t) =
      (F.value (a.val+(t : ℂ) • WeightedCoeff.single (Weight.sobolev r) (n : ℤ) 1)).re := by
    have h := congrArg Complex.re
      (F.value_eq_physical_actionHamiltonian (WeightedCoeff.positiveActionRay (Weight.sobolev r) 1 a n t))
    rw [WeightedCoeff.positiveActionRay_val_of_nonneg _ _ a n t ht,Complex.ofReal_re] at h
    exact h.symm
  exact hr.hasDerivWithinAt.congr (fun t ht => he t ht) (he 0 le_rfl)

end OriginalHierarchyActionFactor

namespace GlobalRoughAbelianForwardData

/-- The intrinsic original frequency is an actual positive action derivative
of the independently defined physical H_m, without choosing an analytic factor. -/
def originalHierarchyFrequency (D : GlobalRoughAbelianForwardData) (m : ℕ) (r : ℝ)
    (hrs : r=2*((m : ℝ)+1/2))
    (a : WeightedCoeff.positiveActionLocus (Weight.sobolev r) 1) (n : ℕ+) : ℝ :=
  derivWithin (fun t : ℝ => D.originalActionHamiltonian m r hrs
    (WeightedCoeff.positiveActionRay (Weight.sobolev r) 1 a n t)) (Ici 0) 0

/-- The intrinsic frequency equals the positive coordinate derivative of ANY
genuine analytic action factor, with the literal raw unit direction. -/
theorem originalHierarchyFrequency_eq_factor_derivative
    (D : GlobalRoughAbelianForwardData) (m : ℕ) (r : ℝ) (hrs : r=2*((m : ℝ)+1/2))
    (F : OriginalHierarchyActionFactor D m r hrs)
    (a : WeightedCoeff.positiveActionLocus (Weight.sobolev r) 1) (n : ℕ+) :
    (D.originalHierarchyFrequency m r hrs a n : ℂ) =
      (fderiv ℂ F.value a.val) (WeightedCoeff.single (Weight.sobolev r) (n : ℤ) 1) := by
  have he := (F.hasDerivWithinAt_physical_actionHamiltonian a n).derivWithin
    (uniqueDiffWithinAt_Ici (0 : ℝ))
  change D.originalHierarchyFrequency m r hrs a n = F.frequency a.val n at he
  rw [he]
  exact F.frequency_complex_value a n

/-- All original native scalar frequencies admit real analytic extensions on
ONE complex action neighborhood, chosen before every positive frequency index. -/
theorem exists_originalHierarchyFrequency_native_analytic_extensions
    (D : GlobalRoughAbelianForwardData) (m : ℕ) (r : ℝ) (hrs : r=2*((m : ℝ)+1/2)) :
    ∃ U : Set (WeightedCoeff (Weight.sobolev r) 1),
      ∃ ω : ℕ+ → WeightedCoeff (Weight.sobolev r) 1 → ℝ,
      IsOpen U ∧ WeightedCoeff.positiveActionLocus (Weight.sobolev r) 1 ⊆ U ∧
      (∀ n, AnalyticOnNhd ℝ (ω n) U) ∧
      ∀ a : WeightedCoeff.positiveActionLocus (Weight.sobolev r) 1, ∀ n,
        ω n a.val = D.originalHierarchyFrequency m r hrs a n := by
  obtain ⟨F⟩ := nonempty_originalHierarchyActionFactor D m r hrs
  refine ⟨F.domain,fun n a => F.frequency a n,F.domain_open,
    fun _ ha => F.nonnegative_subset_domain ha.1,F.frequency_analytic,?_⟩
  intro a n
  exact (congrArg Complex.re (D.originalHierarchyFrequency_eq_factor_derivative m r hrs F a n)).symm

/-- Original KdV frequencies on the literal weighted l1 action cone of order three. -/
def originalKdVFrequency (D : GlobalRoughAbelianForwardData)
    (a : WeightedCoeff.positiveActionLocus (Weight.sobolev 3) 1) (n : ℕ+) : ℝ :=
  D.originalHierarchyFrequency 1 3 (by norm_num) a n

/-- Original KdV2 frequencies on the literal weighted l1 action cone of order five. -/
def originalKdV2Frequency (D : GlobalRoughAbelianForwardData)
    (a : WeightedCoeff.positiveActionLocus (Weight.sobolev 5) 1) (n : ℕ+) : ℝ :=
  D.originalHierarchyFrequency 2 5 (by norm_num) a n

/-- The KdV frequency differentiates the actual printed physical Hamiltonian,
including when the prescribed nth action is zero. -/
theorem originalKdVFrequency_eq_physical_derivative (D : GlobalRoughAbelianForwardData)
    (a : WeightedCoeff.positiveActionLocus (Weight.sobolev 3) 1) (n : ℕ+) :
    D.originalKdVFrequency a n = derivWithin (fun t : ℝ => (nativeKdVHamiltonian
      (D.originalActionPotential 1 3 (by norm_num)
        (WeightedCoeff.positiveActionRay (Weight.sobolev 3) 1 a n t))).re) (Ici 0) 0 := by
  simp only [originalKdVFrequency,originalHierarchyFrequency,originalActionHamiltonian,
    nativeHillHierarchyHamiltonian_one]

/-- The KdV2 frequency differentiates the actual printed physical Hamiltonian
on its entire native action cone, with the original normalization. -/
theorem originalKdV2Frequency_eq_physical_derivative (D : GlobalRoughAbelianForwardData)
    (a : WeightedCoeff.positiveActionLocus (Weight.sobolev 5) 1) (n : ℕ+) :
    D.originalKdV2Frequency a n = derivWithin (fun t : ℝ => (nativeKdV2Hamiltonian
      (D.originalActionPotential 2 5 (by norm_num)
        (WeightedCoeff.positiveActionRay (Weight.sobolev 5) 1 a n t))).re) (Ici 0) 0 := by
  simp only [originalKdV2Frequency,originalHierarchyFrequency,originalActionHamiltonian,
    nativeHillHierarchyHamiltonian_two]

/-- The original scalar KdV frequencies are real analytic in the exact native
weighted l1 norm, with one common neighborhood for all indices. -/
theorem exists_originalKdVFrequency_native_analytic_extensions (D : GlobalRoughAbelianForwardData) :
    ∃ U : Set (WeightedCoeff (Weight.sobolev 3) 1),
      ∃ ω : ℕ+ → WeightedCoeff (Weight.sobolev 3) 1 → ℝ,
      IsOpen U ∧ WeightedCoeff.positiveActionLocus (Weight.sobolev 3) 1 ⊆ U ∧
      (∀ n, AnalyticOnNhd ℝ (ω n) U) ∧
      ∀ a : WeightedCoeff.positiveActionLocus (Weight.sobolev 3) 1, ∀ n, ω n a.val = D.originalKdVFrequency a n :=
  D.exists_originalHierarchyFrequency_native_analytic_extensions 1 3 (by norm_num)

/-- The corresponding actual KdV2 result in the exact order-five action norm. -/
theorem exists_originalKdV2Frequency_native_analytic_extensions (D : GlobalRoughAbelianForwardData) :
    ∃ U : Set (WeightedCoeff (Weight.sobolev 5) 1),
      ∃ ω : ℕ+ → WeightedCoeff (Weight.sobolev 5) 1 → ℝ,
      IsOpen U ∧ WeightedCoeff.positiveActionLocus (Weight.sobolev 5) 1 ⊆ U ∧
      (∀ n, AnalyticOnNhd ℝ (ω n) U) ∧
      ∀ a : WeightedCoeff.positiveActionLocus (Weight.sobolev 5) 1, ∀ n, ω n a.val = D.originalKdV2Frequency a n :=
  D.exists_originalHierarchyFrequency_native_analytic_extensions 2 5 (by norm_num)

end GlobalRoughAbelianForwardData
end NLS.Articles.KdVKdV2Frequencies
