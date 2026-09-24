import NLS.ZakharovShabat.SourceActionStadiumLimit

/-!
# Nonvanishing action circles around open real gaps

The weighted stadium integral has a nonzero real boundary limit.
The small-circle deformation identifies the action circle with its
negative, so sufficiently small enclosing circles have nonzero
weighted integral.
-/

noncomputable section
open Set Filter Topology Complex
open NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Every sufficiently small positive corner-circle radius has a
nonzero recentered weighted quotient integral. -/
theorem sourceAction_cornerCircleIntegral_eventually_ne_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re)
    (q : ℝ) :
    let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let c : ℂ := (((l.re+r.re)/2 : ℝ) : ℂ)
    let d : ℝ := (r.re-l.re)/2
    ∀ᶠ ρ in 𝓝[Set.Ioi 0] (0:ℝ),
      (∮ z in C(c,stadiumCornerRadius d ρ),
        (z-(q:ℂ)) * sourceCriticalRootRatioJoint hp hp1 (z,ψ)) ≠ 0 := by
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let c : ℂ := (((l.re+r.re)/2 : ℝ) : ℂ)
  let d : ℝ := (r.re-l.re)/2
  let W := sourceAction_cosineBoundaryIntegral hp hp1 ψ n (q:ℂ) true
  have hW : W ≠ 0 :=
    (sourceAction_upper_cosineBoundaryIntegral_sign
      hp hp1 ψ hreal n hopen q).2
  have htwo : (2:ℂ)*W ≠ 0 := mul_ne_zero (by norm_num) hW
  have hstad := sourceAction_stadium_curveIntegral_tendsto_two_upper
    hp hp1 ψ hreal n hopen q
  have hstadNe : ∀ᶠ ρ in 𝓝[Set.Ioi 0] (0:ℝ),
      (∫ᶜ z in sourceGapStadiumPath l r ρ,
        holomorphicOneForm
          (fun w => (w-(q:ℂ)) * sourceCriticalRootRatioJoint hp hp1 (w,ψ)) z)
        ≠ 0 := hstad.eventually_ne htwo
  obtain ⟨ε,hε,heq⟩ :=
    exists_sourceAction_cornerCircleIntegral_eq_neg_stadium
      hp hp1 ψ hreal n hopen (q:ℂ)
  have hsmall0 : ∀ᶠ ρ in 𝓝 (0:ℝ), ρ < ε := Iio_mem_nhds hε
  have hsmall : ∀ᶠ ρ in 𝓝[Set.Ioi 0] (0:ℝ), ρ < ε :=
    hsmall0.filter_mono nhdsWithin_le_nhds
  filter_upwards [hstadNe,hsmall,self_mem_nhdsWithin] with ρ hne hρε hρ
  have h := heq ρ ⟨hρ,hρε.le⟩
  rw [h]
  exact neg_ne_zero.mpr hne

/-- The action itself is nonzero on sufficiently small corner circles
around any open real-type gap. -/
theorem sourceActionCircle_eventually_ne_zero_of_openRealGap
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re) :
    let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let c : ℂ := (((l.re+r.re)/2 : ℝ) : ℂ)
    let d : ℝ := (r.re-l.re)/2
    ∀ᶠ ρ in 𝓝[Set.Ioi 0] (0:ℝ),
      sourceActionCircle hp hp1 ψ c (stadiumCornerRadius d ρ) ≠ 0 := by
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let c : ℂ := (((l.re+r.re)/2:ℝ):ℂ)
  let d : ℝ := (r.re-l.re)/2
  have h := sourceAction_cornerCircleIntegral_eventually_ne_zero
    hp hp1 ψ hreal n hopen 0
  filter_upwards [h] with ρ hρ
  unfold sourceActionCircle
  change (Real.pi:ℂ)⁻¹ *
      (∮ z in C(c,stadiumCornerRadius d ρ),
        z * sourceCriticalRootRatioJoint hp hp1 (z,ψ)) ≠ 0
  have hρ' : (∮ z in C(c,stadiumCornerRadius d ρ),
      z * sourceCriticalRootRatioJoint hp hp1 (z,ψ)) ≠ 0 := by
    simpa [c,d,l,r] using hρ
  exact mul_ne_zero (inv_ne_zero (by exact_mod_cast Real.pi_ne_zero)) hρ'

end NLS.ZakharovShabat
