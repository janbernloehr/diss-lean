import NLS.Articles.KdVPseudomeasures.SourceH1Actions

/-! Theorem 3.1(iii): analytic dependence of the actual physical KdV
Hamiltonian on the whole positive n^3-weighted l1 action quadrant. -/
noncomputable section
open Set Complex NLS.WeightedCoeff
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures

def sourceH1PositiveActions : Set SourceH1Actions :=
  {a | ∀ k, (a.val.val k).im=0 ∧ 0≤(a.val.val k).re}

theorem sourceH1CanonicalActions_mem_positive
    (z : RealSignedHilbert (signedStepOrder (1/2) 1)) :
    sourceH1CanonicalActions z ∈ sourceH1PositiveActions := by
  intro k
  by_cases hk : 0 < k
  · rw [sourceH1CanonicalActions_apply z k hk,z.property k]
    constructor
    · simp only [mul_im,conj_re,conj_im]
      ring
    · simp only [mul_re,conj_re,conj_im,mul_neg,sub_neg_eq_add]
      exact add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)
  · rw [(sourceH1CanonicalActions z).property k (by omega)]
    exact ⟨rfl,le_rfl⟩

/-- There is a single holomorphic function on an open neighborhood of
the ENTIRE original n^3-weighted positive action quadrant, recovering the
genuine Hamiltonian in the original canonical coordinates. -/
theorem sourceTheorem3_1_iii_complex :
    ∃ U : Set SourceH1Actions, ∃ G : SourceH1Actions → ℂ,
      IsOpen U ∧ sourceH1PositiveActions ⊆ U ∧ AnalyticOnNhd ℂ G U ∧
      (∀ a ∈ sourceH1PositiveActions, (G a).im=0) ∧
      ∀ z : RealSignedHilbert (signedStepOrder (1/2) 1),
        G (sourceH1CanonicalActions z)=(hillH1CanonicalHamiltonian z:ℂ) := by
  obtain ⟨U,G,hU,hpos,hG,hrec⟩ :=
    Coeff.exists_analytic_scalar_action_factor_of_real_analytic (q := 1) (by simp : (2:ℝ≥0∞)≠⊤)
      sourceH1CartesianHamiltonian analyticAt_sourceH1CartesianHamiltonian
      sourceH1CartesianHamiltonian_action_invariant
  have hreal (b : Coeff 1) (hb : b ∈ Coeff.nonnegativeLocus 1) : (G b).im=0 := by
    obtain ⟨w,hw,he,_⟩ := Coeff.exists_real_quadraticActions_lift (p := 2) (by simp : (2:ℝ≥0∞)≠⊤) b hb
    obtain ⟨x,rfl⟩ := (Coeff.mem_realPairLocus_iff w).mp hw
    rw [← he,hrec]
    exact Complex.ofReal_im _
  refine ⟨sourceH1NormalizedActions ⁻¹' U,fun a => G (sourceH1NormalizedActions a),
    hU.preimage sourceH1NormalizedActions.continuous,?_,?_,?_,?_⟩
  · intro a ha
    exact hpos (sourceH1NormalizedActions_nonnegative a ha)
  · intro a ha
    exact (hG _ ha).comp (sourceH1NormalizedActions.analyticAt a)
  · intro a ha
    exact hreal _ (sourceH1NormalizedActions_nonnegative a ha)
  · intro z
    change G (sourceH1NormalizedActions (sourceH1CanonicalActions z)) = _
    rw [sourceH1CanonicalActions_normalized,hrec]
    simp only [sourceH1CartesianHamiltonian,signedRealCartesianDecoder_parameters]

/-- The real-valued physical Hamiltonian is a real analytic function of
the original actions on ALL of the positive weighted quadrant. Analyticity
is supplied on an open ambient neighborhood, also at every boundary point. -/
theorem sourceTheorem3_1_iii :
    ∃ U : Set SourceH1Actions, ∃ H : SourceH1Actions → ℝ,
      IsOpen U ∧ sourceH1PositiveActions ⊆ U ∧ AnalyticOnNhd ℝ H U ∧
      ∀ z : RealSignedHilbert (signedStepOrder (1/2) 1),
        H (sourceH1CanonicalActions z)=hillH1CanonicalHamiltonian z := by
  obtain ⟨U,G,hU,hpos,hG,_,hrec⟩ := sourceTheorem3_1_iii_complex
  refine ⟨U,fun a => (G a).re,hU,hpos,?_,?_⟩
  · intro a ha
    exact (Complex.reCLM.analyticAt _).comp ((hG a ha).restrictScalars)
  · intro z
    change (G (sourceH1CanonicalActions z)).re = _
    rw [hrec,Complex.ofReal_re]

end NLS.Articles.KdVPseudomeasures
