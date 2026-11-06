import NLS.Articles.KdVConvexity.IntrinsicPhysicalFrequencies

/-! # Physical energy determines its analytic germ near every positive ell2 action

The physical original ell^(3,1) cone is dense in the positive ell2 cone.
Holomorphic uniqueness then gives equality of extension germs at every
positive Hilbert action, including boundary points and nonsummable actions.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.Articles.KdVConvexity

def finiteHilbertActions (s : Finset ℤ) (a : ActionSpace) : ActionSpace :=
  actionUnreindex (Coeff.truncate s (actionReindex a))

@[simp] theorem finiteHilbertActions_apply (s : Finset ℤ) (a : ActionSpace) (n : ℕ+) :
    finiteHilbertActions s a n = if actionIndexEquiv.symm n ∈ s then a n else 0 := by
  simp only [finiteHilbertActions,actionUnreindex_apply,Coeff.truncate_apply,
    actionReindex_apply,Equiv.apply_symm_apply]

theorem finiteHilbertActions_mem_original_domain (s : Finset ℤ) (a : ActionSpace)
    (ha : a ∈ positiveQuadrant) : finiteHilbertActions s a ∈ originalPositiveActionDomain := by
  classical
  refine ⟨?_,?_⟩
  · intro n
    by_cases hn : actionIndexEquiv.symm n ∈ s
    · simpa only [finiteHilbertActions_apply,if_pos hn] using ha n
    · simp only [finiteHilbertActions_apply,if_neg hn,zero_im,zero_re,le_refl,and_self]
  · apply actionIndexEquiv.summable_iff.mp
    apply summable_of_ne_finset_zero (s := s)
    intro k hk
    simp only [Function.comp_def,finiteHilbertActions_apply,Equiv.symm_apply_apply,
      if_neg hk,norm_zero,mul_zero]

theorem tendsto_finiteHilbertActions (a : ActionSpace) :
    Tendsto (fun s : Finset ℤ => finiteHilbertActions s a) atTop (nhds a) := by
  have h := actionUnreindex.continuous.continuousAt.tendsto.comp
    (Coeff.tendsto_truncate (by simp : (2 : ℝ≥0∞) ≠ ⊤) (actionReindex a))
  simpa only [finiteHilbertActions,Function.comp_def,actionUnreindex_actionReindex] using h

theorem positiveQuadrant_subset_closure_original_domain :
    positiveQuadrant ⊆ closure originalPositiveActionDomain := by
  intro a ha
  exact mem_closure_of_tendsto (tendsto_finiteHilbertActions a)
    (Eventually.of_forall (fun s => finiteHilbertActions_mem_original_domain s a ha))

/-- Continuous agreement on original physical actions extends to every
positive Hilbert action in the same open domain. -/
theorem eqOn_positive_of_original_domain_agreement
    (f g : ActionSpace → ℂ) (U : Set ActionSpace) (hU : IsOpen U)
    (hf : ContinuousOn f U) (hg : ContinuousOn g U)
    (he : ∀ a ∈ U, a ∈ originalPositiveActionDomain → f a=g a) :
    ∀ a ∈ U, a ∈ positiveQuadrant → f a=g a := by
  intro a ha hapos
  have ht := tendsto_finiteHilbertActions a
  have hmem := ht.eventually (hU.mem_nhds ha)
  have hfg : (fun s : Finset ℤ => f (finiteHilbertActions s a)) =ᶠ[atTop]
      (fun s => g (finiteHilbertActions s a)) := by
    filter_upwards [hmem] with s hs
    exact he _ hs (finiteHilbertActions_mem_original_domain s a hapos)
  have hflim := ((hf a ha).continuousAt (hU.mem_nhds ha)).tendsto.comp ht
  have hglim := ((hg a ha).continuousAt (hU.mem_nhds ha)).tendsto.comp ht
  exact tendsto_nhds_unique hflim (hglim.congr' hfg.symm)

/-- Agreement on the original weighted physical action cone fixes the
entire complex analytic germ at ANY positive ell2 action. -/
theorem eventuallyEq_of_original_domain_agreement
    (f g : ActionSpace → ℂ) (U : Set ActionSpace) (hU : IsOpen U)
    (hf : AnalyticOnNhd ℂ f U) (hg : AnalyticOnNhd ℂ g U)
    (he : ∀ a ∈ U, a ∈ originalPositiveActionDomain → f a=g a)
    (a : ActionSpace) (ha : a ∈ U) (hapos : a ∈ positiveQuadrant) : f =ᶠ[𝓝 a] g := by
  let L := actionUnreindex
  have hV : IsOpen (L ⁻¹' U) := hU.preimage L.continuous
  have hc : actionReindex a ∈ L ⁻¹' U := by
    change actionUnreindex (actionReindex a) ∈ U
    rwa [actionUnreindex_actionReindex]
  have hcpos : actionReindex a ∈ Coeff.nonnegativeLocus 2 := fun k => hapos (actionIndexEquiv k)
  have hfc : AnalyticOnNhd ℂ (fun b : Coeff 2 => f (L b)) (L ⁻¹' U) :=
    fun b hb => (hf _ hb).comp (L.toContinuousLinearMap.analyticAt b)
  have hgc : AnalyticOnNhd ℂ (fun b : Coeff 2 => g (L b)) (L ⁻¹' U) :=
    fun b hb => (hg _ hb).comp (L.toContinuousLinearMap.analyticAt b)
  have hfg := Coeff.eventuallyEq_of_nonnegative_agreement (by simp : (2 : ℝ≥0∞) ≠ ⊤)
    (fun b : Coeff 2 => f (L b)) (fun b => g (L b)) (L ⁻¹' U) hV
    (actionReindex a) hc hcpos hfc.differentiableOn hgc.differentiableOn (by
      intro b hb hbpos
      apply eqOn_positive_of_original_domain_agreement f g U hU hf.continuousOn hg.continuousOn he (L b) hb
      intro n
      exact hbpos (actionIndexEquiv.symm n))
  have ht := hfg.comp_tendsto actionReindex.continuous.continuousAt
  simpa only [Function.comp_def,L,actionUnreindex_actionReindex] using ht

/-- Every global physical extension has the SAME germ near every point
of the positive Hilbert cone, rather than merely the same original values. -/
theorem PhysicalHstarExtension.eventuallyEq (E D : PhysicalHstarExtension)
    (a : ActionSpace) (ha : a ∈ positiveQuadrant) : E.hamiltonian =ᶠ[𝓝 a] D.hamiltonian := by
  apply eventuallyEq_of_original_domain_agreement E.hamiltonian D.hamiltonian
    (E.domain ∩ D.domain) (E.isOpen.inter D.isOpen)
    (E.analytic.mono inter_subset_left) (D.analytic.mono inter_subset_right) ?_
    a ⟨E.contains_cone ha,D.contains_cone ha⟩ ha
  intro b _ hb
  obtain ⟨c,hc,hcb⟩ := original_domain_has_weighted_representative b hb
  rw [←hcb]
  exact (E.physical_agreement ⟨c,hc⟩).trans (D.physical_agreement ⟨c,hc⟩).symm

theorem PhysicalHstarExtension.actionGradient_eq (E D : PhysicalHstarExtension)
    (a : ActionSpace) (ha : a ∈ positiveQuadrant) :
    actionGradient E.hamiltonian a=actionGradient D.hamiltonian a := by
  unfold actionGradient
  rw [(E.eventuallyEq D a ha).fderiv_eq]

end NLS.Articles.KdVConvexity
