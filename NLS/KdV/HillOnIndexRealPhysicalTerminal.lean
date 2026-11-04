import NLS.KdV.HillOnIndexRealCosinePhase
import NLS.KdV.HillOnIndexRealClosedGap
import NLS.ComplexAnalysis.RealCosineRootTerminal

/-! Real physical terminals retain the actual norming-sheet sign,
including the two Dirichlet endpoints of an open original gap. -/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch

theorem exists_real_physical_cosine_terminal (P : HillProductEquationPatch) (n : ℕ+)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q)
    (hgap : hillHminusCanonicalGapSquare n q ≠ 0) :
    ∃ t : ℝ,
      cosineGapPoint (sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi q) ((n:ℕ):ℤ))
        (sourceStandardRootHalfGap (by norm_num) (by norm_num) (P.sourcePsi q) ((n:ℕ):ℤ)) (t:ℂ) =
          P.physicalDirichletFrequency ((n:ℕ):ℤ) q ∧
      -I*sourceStandardRootHalfGap (by norm_num) (by norm_num) (P.sourcePsi q) ((n:ℕ):ℤ)*Complex.sin (t:ℂ) =
        P.physicalDirichletRootCoefficient n q := by
  let τ := sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi q) ((n:ℕ):ℤ)
  let δ := sourceStandardRootHalfGap (by norm_num) (by norm_num) (P.sourcePsi q) ((n:ℕ):ℤ)
  have hδsq : δ^2 = (canonicalPeriodicGap (by norm_num) (by norm_num)
      (periodOnePotential (P.sourcePsi q)) (periodOnePotential_mem _) ((n:ℕ):ℤ))^2/4 := by
    dsimp only [δ,sourceStandardRootHalfGap]
    ring
  have hphys := P.real_mem_physicalDirichletSource q hq hr
  have hδ : δ ≠ 0 := by
    intro he
    have h := P.frequency_half_gap_square_ne_zero_of_original_gap n q hphys hgap
    apply h
    rw [← hδsq,he]
    norm_num
  let u : PeriodOneRealL2 := ⟨P.parent.parent.miuraBall.actionBall.lift q,
    P.parent.parent.miuraBall.actionBall.lift_real q (P.parent.subset (P.subset hq)).1 hr⟩
  have hμ : P.physicalDirichletFrequency ((n:ℕ):ℤ) q ∈ segment ℝ (τ-δ) (τ+δ) := by
    rw [sourcePeriodicSegment_eq_of_halfGap_sq (by norm_num) (by norm_num)
      (P.sourcePsi q) ((n:ℕ):ℤ) δ rfl]
    exact canonicalAuxiliaryPeriodOneRoots_mem_sourcePeriodicSegment_of_realType (by norm_num) (by norm_num)
      .dirichlet (P.sourcePsi q) (hillMiuraRealSource u).property _
  have hs : (P.physicalDirichletRootCoefficient n q)^2 =
      quadraticRootPolynomial τ (δ^2) (P.physicalDirichletFrequency ((n:ℕ):ℤ) q) := by
    rw [hδsq]
    exact P.physicalDirichletRootCoefficient_sq n q hphys
  exact exists_real_cosine_terminal_with_root τ δ _ _ hδ hμ hs

theorem exists_real_original_diagonal_phase (P : HillProductEquationPatch) (n : ℕ+)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q)
    (hgap : hillHminusCanonicalGapSquare n q ≠ 0) :
    ∃ a : ℝ,
      P.physicalOnIndexCartesianPlus n q =
        ((hillHminusLabels q hr (2*(n:ℕ))-hillHminusLabels q hr (2*(n:ℕ)-1):ℝ):ℂ)*Complex.exp (I*(a:ℂ)) ∧
      P.physicalOnIndexCartesianMinus n q =
        ((hillHminusLabels q hr (2*(n:ℕ))-hillHminusLabels q hr (2*(n:ℕ)-1):ℝ):ℂ)*Complex.exp (-I*(a:ℂ)) := by
  obtain ⟨t,hpoint,hroot⟩ := P.exists_real_physical_cosine_terminal n q hq hr hgap
  let δ := sourceStandardRootHalfGap (by norm_num) (by norm_num) (P.sourcePsi q) ((n:ℕ):ℤ)
  let α := P.onIndexAbelianCosinePhase n q δ (t:ℂ)
  have him : α.im = 0 := P.onIndexAbelianCosinePhase_im_eq_zero_of_real n q hq hr δ rfl t
  have hα : (α.re:ℂ) = α := by simpa [him] using Complex.re_add_im α
  have hp := P.physicalOnIndexCartesianPlus_eq_gap_mul_phase_exp n q δ (t:ℂ) hpoint hroot
  have hm := P.physicalOnIndexCartesianMinus_eq_gap_mul_phase_exp n q δ (t:ℂ) hpoint hroot
  rw [P.original_energy_gap_eq_four_midpoint_halfgap_of_real n q hq hr] at hp hm
  refine ⟨α.re,?_,?_⟩
  · rw [hα]
    exact hp
  · rw [hα]
    exact hm

theorem onIndexAbelianCosinePhase_mod_two_pi_of_physical_terminals (P : HillProductEquationPatch)
    (n : ℕ+) (q : PeriodOneHminusOne) (δ e f : ℂ) (hδ : δ ≠ 0)
    (he : cosineGapPoint (sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi q) ((n:ℕ):ℤ)) δ e = P.physicalDirichletFrequency ((n:ℕ):ℤ) q)
    (hf : cosineGapPoint (sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi q) ((n:ℕ):ℤ)) δ f = P.physicalDirichletFrequency ((n:ℕ):ℤ) q)
    (hre : -I*δ*Complex.sin e = P.physicalDirichletRootCoefficient n q)
    (hrf : -I*δ*Complex.sin f = P.physicalDirichletRootCoefficient n q) :
    ∃ k : ℤ, P.onIndexAbelianCosinePhase n q δ e-P.onIndexAbelianCosinePhase n q δ f = (k:ℂ)*(2*(Real.pi:ℂ)) := by
  obtain ⟨k,hk⟩ := cosine_phase_terminal_mod_two_pi _ δ _ _ e f hδ he hf hre hrf
  rw [P.onIndexAbelianCosinePhase_at_physical_terminal n q δ e he hre,
    P.onIndexAbelianCosinePhase_at_physical_terminal n q δ f hf hrf]
  exact ⟨k,by linear_combination hk⟩

end NLS.KdV.HillProductEquationPatch
