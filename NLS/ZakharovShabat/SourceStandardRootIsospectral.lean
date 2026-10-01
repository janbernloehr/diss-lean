import NLS.ZakharovShabat.SourcePeriodicIsospectral
import NLS.ZakharovShabat.SourceStandardRootJointAnalytic

/-! # Actual standard-root factors are stationary under action Hamiltonians

The normalized root depends analytically on the actual midpoint and
squared gap away from the selected cut. Both inputs are stationary
in an isospectral direction, so the actual root factor is stationary.
-/

noncomputable section
open Set Complex NLS.Poisson
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Every actual standard-root factor is stationary in an isospectral
direction off its selected segment, including for a collapsed gap. -/
theorem fderiv_sourceStandardRoot_isospectral_eq_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hreal : IsRealType (CoeffPair.toMax p φ)) (h : CoeffPair p)
    (hiso : SourceIsospectralDirection hp φ h) (n : ℤ) (z : ℂ)
    (hz : z ∉ sourcePeriodicSegment hp hp1 φ n) :
    (fderiv ℂ (fun ψ : CoeffPair p => sourceStandardRoot hp hp1 ψ n z) φ) h = 0 := by
  let M : CoeffPair p → ℂ := fun ψ => canonicalPeriodicMidpoint hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ) n
  let G : CoeffPair p → ℂ := fun ψ => (canonicalPeriodicGap hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ) n)^2
  obtain ⟨W,_,_,hWreal,hMG⟩ := exists_global_source_analytic_midpoint_squaredGap hp hp1
  have hM : DifferentiableAt ℂ M φ := (hMG φ (hWreal hreal) n).1.differentiableAt
  have hG : DifferentiableAt ℂ G φ := (hMG φ (hWreal hreal) n).2.differentiableAt
  have hnonzero : M φ ≠ z := by
    intro he
    exact hz (he.symm ▸ sourcePeriodicMidpoint_mem_segment hp hp1 φ n)
  have hslit : 1-G φ/(4*(M φ-z)^2) ∈ Complex.slitPlane :=
    sourceStandardRoot_radicand_mem_slitPlane hp hp1 φ n z hz
  let R : ℂ × ℂ → ℂ := fun t => normalizedStandardRoot t.1 t.2 z
  have hR : DifferentiableAt ℂ R (M φ,G φ) := by
    have ha := normalizedStandardRoot_joint_analyticAt
      (fun t : ℂ × ℂ => t.1) (fun t : ℂ × ℂ => t.2)
      (M φ,G φ) z analyticAt_fst analyticAt_snd hnonzero hslit
    exact (ha.comp (f := fun t : ℂ × ℂ => (z,t))
      (analyticAt_const.prod analyticAt_id)).differentiableAt
  have hd := (hR.hasFDerivAt.comp φ
    (hM.hasFDerivAt.prodMk hG.hasFDerivAt)).fderiv
  have he := congrArg (fun L : CoeffPair p →L[ℂ] ℂ => L h) hd
  have hzero := fderiv_canonicalPeriodicMidpoint_squaredGap_isospectral_eq_zero hp hp1 φ hreal h hiso n
  change (fderiv ℂ M φ) h = 0 ∧ (fderiv ℂ G φ) h = 0 at hzero
  simp only [Function.comp_def,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply,hzero.1,hzero.2] at he
  change (fderiv ℂ (fun ψ : CoeffPair p => sourceStandardRoot hp hp1 ψ n z) φ) h = _ at he
  change (fderiv ℂ (fun ψ : CoeffPair p => sourceStandardRoot hp hp1 ψ n z) φ) h =
    (fderiv ℂ R (M φ,G φ)) (0 : ℂ × ℂ) at he
  rw [map_zero] at he
  exact he

/-- Every actual action Hamiltonian fixes the selected standard root
at each spectral parameter off its segment. -/
theorem fderiv_sourceStandardRoot_sourceHamiltonianVector_action_eq_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ))
    (n m : ℤ) (z : ℂ) (hz : z ∉ sourcePeriodicSegment hp hp1 φ n) :
    (fderiv ℂ (fun ψ : CoeffPair p => sourceStandardRoot hp hp1 ψ n z) φ)
      (sourceHamiltonianVector h2p (sourceComplexAction hp hp1 m) φ) = 0 :=
  fderiv_sourceStandardRoot_isospectral_eq_zero hp hp1 φ hreal _
    (sourceHamiltonianVector_action_isospectral hp hp1 h2p φ hreal m) n z hz

/-- The actual fixed-parameter standard root commutes with every
actual action wherever that root avoids its selected cut. -/
theorem sourceBracket_standardRoot_action_eq_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ))
    (n m : ℤ) (z : ℂ) (hz : z ∉ sourcePeriodicSegment hp hp1 φ n) :
    sourceBracket h2p (fun ψ : CoeffPair p => sourceStandardRoot hp hp1 ψ n z)
      (sourceComplexAction hp hp1 m) φ = 0 := by
  rw [← fderiv_apply_sourceHamiltonianVector]
  exact fderiv_sourceStandardRoot_sourceHamiltonianVector_action_eq_zero hp hp1 h2p φ hreal n m z hz

end NLS.ZakharovShabat
