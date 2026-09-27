import NLS.ZakharovShabat.SourceNormalizedActionSequenceMajorants
import NLS.ZakharovShabat.SourceActionAllGapPositive

/-!
# Positive normalized action on noncollapsed real-type gaps

The indexed action is a positive real number whenever the selected
real gap is noncollapsed. Its squared gap is also a positive real
number. Consequently the raw normalized action has positive real
part on its real-type noncollapsed domain. This establishes the
positivity assertion of Theorem 11.2 away from collapsed gaps.
-/

noncomputable section
open Complex
open scoped ENNReal Topology
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The selected periodic gap is real at a real-type source. -/
theorem sourcePeriodicGapDisplacement_im_eq_zero_of_realType
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ) :
    (sourcePeriodicGapDisplacement hp hp1 ψ n).im = 0 := by
  obtain ⟨hl,hr⟩ := canonicalPeriodicEndpoints_im_eq_zero_of_realType
    hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ)
      (isRealType_periodOnePotential ψ hreal) n
  simp only [sourcePeriodicGapDisplacement_apply, canonicalPeriodicGap,
    Complex.sub_im, hl, hr, sub_self]

/-- The raw quotient is real at every real-type source. At a
collapsed gap its definition has value zero by field convention. -/
theorem sourceRawNormalizedAction_im_eq_zero_of_realType
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ)) :
    (sourceRawNormalizedAction hp hp1 n ψ).im = 0 := by
  have hIim : (sourceComplexAction hp hp1 n ψ).im = 0 := by
    rw [sourceComplexAction_eq_sourceRealAction hp hp1 n ψ hreal]
    exact (sourceRealAction_nonneg_and_eq_zero_iff_gap_zero
      hp hp1 ψ hreal n).2.1
  have hγim := sourcePeriodicGapDisplacement_im_eq_zero_of_realType
    hp hp1 ψ hreal n
  let Iₙ := sourceComplexAction hp hp1 n ψ
  let γ := sourcePeriodicGapDisplacement hp hp1 ψ n
  have hI : Iₙ = (Iₙ.re:ℂ) := by
    apply Complex.ext
    · simp
    · simpa only [Complex.ofReal_im] using hIim
  have hγ : γ = (γ.re:ℂ) := by
    apply Complex.ext
    · simp
    · simpa only [Complex.ofReal_im] using hγim
  change (Iₙ / γ^2).im = 0
  rw [hI,hγ]
  norm_num only [← Complex.ofReal_pow, ← Complex.ofReal_div, Complex.ofReal_im]

/-- The raw normalized action has strictly positive real part at
every noncollapsed real-type gap. -/
theorem sourceRawNormalizedAction_re_pos_of_realType_gap_ne_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (hgap : sourcePeriodicGapDisplacement hp hp1 ψ n ≠ 0) :
    0 < (sourceRawNormalizedAction hp hp1 n ψ).re := by
  let Iₙ := sourceComplexAction hp hp1 n ψ
  let γ := sourcePeriodicGapDisplacement hp hp1 ψ n
  obtain ⟨hAnonneg,hAim,hAzero⟩ :=
    sourceRealAction_nonneg_and_eq_zero_iff_gap_zero hp hp1 ψ hreal n
  have hApos : 0 < Iₙ.re := by
    change 0 < (sourceComplexAction hp hp1 n ψ).re
    rw [sourceComplexAction_eq_sourceRealAction hp hp1 n ψ hreal]
    apply lt_of_le_of_ne hAnonneg
    intro he
    have hzero : sourceRealAction hp hp1 ψ hreal n = 0 := by
      apply Complex.ext
      · simpa using he.symm
      · simpa using hAim
    exact hgap (hAzero.mp hzero)
  have hI : Iₙ = (Iₙ.re:ℂ) := by
    apply Complex.ext
    · simp
    · have hIim : Iₙ.im = 0 := by
        change (sourceComplexAction hp hp1 n ψ).im = 0
        rw [sourceComplexAction_eq_sourceRealAction hp hp1 n ψ hreal]
        exact hAim
      simpa only [Complex.ofReal_im] using hIim
  have hγim : γ.im = 0 :=
    sourcePeriodicGapDisplacement_im_eq_zero_of_realType hp hp1 ψ hreal n
  have hγ : γ = (γ.re:ℂ) := by
    apply Complex.ext
    · simp
    · simpa only [Complex.ofReal_im] using hγim
  have hγre : γ.re ≠ 0 := by
    intro he
    apply hgap
    change γ = 0
    rw [hγ,he]
    simp
  have hden : 0 < γ.re^2 := sq_pos_of_ne_zero hγre
  have hformula : sourceRawNormalizedAction hp hp1 n ψ =
      ((Iₙ.re / γ.re^2 : ℝ):ℂ) := by
    simp only [sourceRawNormalizedAction]
    rw [show sourceComplexAction hp hp1 n ψ = Iₙ from rfl,
      show sourcePeriodicGapDisplacement hp hp1 ψ n = γ from rfl,
      hI,hγ]
    push_cast
    rfl
  rw [hformula]
  exact div_pos hApos hden

/-- At a noncollapsed real-type gap, the real part of the quotient
stays bounded below by half its positive base value on a complex
neighborhood. -/
theorem exists_local_sourceRawNormalizedAction_re_lower_bound
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ))
    (hgap : sourcePeriodicGapDisplacement hp hp1 φ n ≠ 0) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∀ ψ ∈ V,
        (sourceRawNormalizedAction hp hp1 n φ).re / 2 <
          (sourceRawNormalizedAction hp hp1 n ψ).re := by
  have hpos := sourceRawNormalizedAction_re_pos_of_realType_gap_ne_zero
    hp hp1 n φ hreal hgap
  have hcont : ContinuousAt
      (fun ψ : CoeffPair p => (sourceRawNormalizedAction hp hp1 n ψ).re) φ :=
    continuous_re.continuousAt.comp
      (differentiableAt_sourceRawNormalizedAction_of_gap_ne_zero
        hp hp1 n φ hreal hgap).continuousAt
  have hhalf : (sourceRawNormalizedAction hp hp1 n φ).re / 2 <
      (sourceRawNormalizedAction hp hp1 n φ).re := by linarith
  have hnear : ∀ᶠ ψ : CoeffPair p in 𝓝 φ,
      (sourceRawNormalizedAction hp hp1 n φ).re / 2 <
        (sourceRawNormalizedAction hp hp1 n ψ).re :=
    hcont.eventually (lt_mem_nhds hhalf)
  obtain ⟨V,hVsub,hVopen,hφV⟩ := _root_.mem_nhds_iff.mp hnear
  exact ⟨V,hVopen,hφV,fun ψ hψ => hVsub hψ⟩

end NLS.ZakharovShabat
