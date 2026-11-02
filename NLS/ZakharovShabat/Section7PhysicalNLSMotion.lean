import NLS.ZakharovShabat.SmoothNLSData
import NLS.ZakharovShabat.SourceConstantPeriodicSpectrum
import NLS.ZakharovShabat.L2GradientRestrictionFourier
import NLS.ZakharovShabat.SourceSmoothApproximationSolutions
import Mathlib.Analysis.Complex.RealDeriv

/-! Explicit physical NLS motion for spatially constant smooth data. -/
noncomputable section
open Set Complex Filter Topology
open scoped ContDiff ComplexConjugate ENNReal
namespace NLS.ZakharovShabat

/-- A spatial constant is stationary for the renormalized equation with
parameter half its squared amplitude. -/
theorem section7_constant_isClassicalRenormalized (a : ℂ) :
    IsClassicalRenormalizedNLSTrajectory (‖a‖ ^ 2 / 2)
      (fun _ : ℝ => ContinuousMap.const (AddCircle (2 : ℝ)) a) := by
  refine ⟨differentiable_const _, fun _ => contDiff_const, fun _ _ => rfl, ?_⟩
  intro time x
  have ha : a * conj a = (‖a‖ : ℂ) ^ 2 := Complex.mul_conj' a
  simp only [deriv_const, deriv_const', ContinuousMap.zero_apply, ContinuousMap.const_apply,
    scalarClassicalNLSVectorField, classicalNLSCubic, mul_zero, zero_sub]
  push_cast
  rw [ha.symm]
  ring

/-- The inverse mass gauge gives the exact ordinary NLS phase rotation. -/
theorem section7_constant_phase_isClassical (a : ℂ) :
    IsClassicalNLSTrajectory
      (classicalNLSGauge (-(‖a‖ ^ 2 / 2))
        (fun _ : ℝ => ContinuousMap.const (AddCircle (2 : ℝ)) a)) :=
  (section7_constant_isClassicalRenormalized a).ungauge

/-- Every smooth datum whose physical value is constant has this exact
ordinary trajectory, by classical uniqueness. -/
theorem SmoothNLSData.section7_ordinary_eq_constant_phase
    (f : SmoothNLSData) (a : ℂ)
    (hf : f.value = ContinuousMap.const (AddCircle (2 : ℝ)) a) :
    f.ordinary = classicalNLSGauge (-(‖a‖ ^ 2 / 2))
      (fun _ : ℝ => ContinuousMap.const (AddCircle (2 : ℝ)) a) := by
  apply f.ordinary_isClassical.eq_of_eq_at (section7_constant_phase_isClassical a) 0
  simpa only [f.ordinary_zero, classicalNLSGauge_zero_time] using hf

/-- At half a phase period the physical constant has changed sign. -/
theorem section7_constant_phase_half_turn (a : ℂ) (ha : a ≠ 0) :
    classicalNLSGaugePhase (-(‖a‖ ^ 2 / 2)) (Real.pi / (2 * ‖a‖ ^ 2)) = -1 := by
  have hn : ‖a‖ ≠ 0 := norm_ne_zero_iff.mpr ha
  have he : 4 * -(‖a‖ ^ 2 / 2) * (Real.pi / (2 * ‖a‖ ^ 2)) = -Real.pi := by
    field_simp
    ring
  rw [classicalNLSGaugePhase, he, ofReal_neg, neg_mul, Complex.exp_neg,
    Complex.exp_pi_mul_I]
  norm_num

/-- The literal period-one Fourier integrals of a physical constant. -/
theorem section7_periodOneCoefficient_const (a : ℂ) (n : ℤ) :
    NLS.Fourier.periodOneCoefficient (fun _ : ℝ => a) n = if n = 0 then a else 0 := by
  have he : NLS.Fourier.periodOneSynthesis (lp.single 1 0 a) = fun _ : ℝ => a := by
    funext x
    simp [NLS.Fourier.periodOneSynthesis_eq_tsum, lp.single_apply, Pi.single_apply]
  rw [← he, NLS.Fourier.periodOneCoefficient_synthesis]
  simp [lp.single_apply, Pi.single_apply]

/-- The smooth physical source construction preserves spatial constants. -/
theorem section7_smoothPeriodOneSourceAt_const
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (a : ℂ) :
    (smoothPeriodOneSourceAt p (ContinuousMap.const (AddCircle (2 : ℝ)) a)
      contDiff_const (fun _ => rfl)).val = sourceConstantPotential a (conj a) := by
  let s := smoothPeriodOneSourceAt p (ContinuousMap.const (AddCircle (2 : ℝ)) a)
    contDiff_const (fun _ => rfl)
  have hfst (n : ℤ) : s.val.fst n = if n = 0 then a else 0 :=
    (smoothPeriodOneSourceAt_fst _ _ _ n).trans (section7_periodOneCoefficient_const a n)
  apply (CoeffPair.toMax p).injective
  apply Prod.ext
  · ext n
    change s.val.fst n = (sourceConstantPotential a (conj a) : CoeffPair p).fst n
    rw [hfst, sourceConstantPotential_fst]
  · ext n
    change s.val.snd n = (sourceConstantPotential a (conj a) : CoeffPair p).snd n
    have hr : s.val.snd n = conj (s.val.fst (-n)) := s.property n
    rw [hr, hfst, sourceConstantPotential_snd]
    by_cases hn : n = 0 <;> simp [hn]

/-- The ordinary source trajectory of constant smooth data follows the
same exact physical phase at every coefficient exponent. -/
theorem SmoothNLSData.section7_ordinarySource_eq_constant_phase
    (f : SmoothNLSData) (a : ℂ)
    (hf : f.value = ContinuousMap.const (AddCircle (2 : ℝ)) a)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (time : ℝ) :
    (f.ordinarySource p time).val =
      sourceConstantPotential
        (classicalNLSGaugePhase (-(‖a‖ ^ 2 / 2)) time * a)
        (conj (classicalNLSGaugePhase (-(‖a‖ ^ 2 / 2)) time * a)) := by
  have he : f.ordinary time = ContinuousMap.const (AddCircle (2 : ℝ))
      (classicalNLSGaugePhase (-(‖a‖ ^ 2 / 2)) time * a) := by
    rw [f.section7_ordinary_eq_constant_phase a hf]
    rfl
  unfold ordinarySource
  simp only [he]
  exact section7_smoothPeriodOneSourceAt_const p _

/-- At the free source, the central Dirichlet coordinate has derivative
one along the diagonal constant-potential line. -/
theorem section7_hasDerivAt_dirichlet_diagonal_constant
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hp1 : 1 < p) :
    HasDerivAt (fun a : ℂ => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet
      (sourceConstantPotential a a) 0) 1 0 := by
  let F : ℂ →L[ℂ] CoeffPair p := (sourceConstantPotentialCLM (p := p)).comp
    ((ContinuousLinearMap.id ℂ ℂ).prod (ContinuousLinearMap.id ℂ ℂ))
  have hF (a : ℂ) : F a = sourceConstantPotential a a :=
    sourceConstantPotentialCLM_apply a a
  have hreal : IsRealType (CoeffPair.toMax p (0 : CoeffPair p)) := by
    simpa only [map_zero] using (isRealType_zero (p := p))
  have hf := (analyticAt_canonicalPeriodOneBoundaryRoots_of_realType
    hp hp1 .dirichlet 0 hreal 0).differentiableAt.hasFDerivAt
  have he : fderiv ℂ (fun ψ : CoeffPair p =>
      canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ 0) 0 =
      sourceFreeDirichletCotangent p 0 := by
    rcases le_total (2 : ℝ≥0∞) p with h | h
    · exact fderiv_canonicalDirichletRoot_zero_eq_free hp hp1 h 0
    · exact fderiv_canonicalDirichletRoot_zero_eq_free_below_two hp hp1 h 0
  rw [he] at hf
  have hf' : HasFDerivAt (fun ψ : CoeffPair p =>
      canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ 0)
      (sourceFreeDirichletCotangent p 0) (F 0) := by
    simpa only [map_zero] using hf
  have hd := hf'.comp_hasDerivAt 0 F.hasDerivAt
  simpa only [Function.comp_def, hF, sourceFreeDirichletCotangent_apply,
    sourceConstantPotential_fst, sourceConstantPotential_snd, neg_zero, ite_true,
    one_add_one_eq_two, one_div, inv_mul_cancel₀ (by norm_num : (2 : ℂ) ≠ 0)] using hd

/-- Some real constant and its negative have distinct actual central
Dirichlet eigenvalues. -/
theorem section7_exists_constant_dirichlet_pair
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ a : ℝ, a ≠ 0 ∧
      canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet (sourceConstantPotential a a) 0 ≠
      canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet (sourceConstantPotential (-a) (-a)) 0 := by
  let μ : ℝ → ℝ := fun a => (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet
    (sourceConstantPotential a a) 0).re
  have hd : HasDerivAt μ 1 0 := by
    simpa only [ofReal_zero, one_re] using
      (section7_hasDerivAt_dirichlet_diagonal_constant hp hp1).real_of_complex
  have hn : HasDerivAt (fun a : ℝ => μ (-a)) (-1) 0 := by
    have hd' : HasDerivAt μ 1 (-(0 : ℝ)) := by simpa using hd
    have hi : HasDerivAt (fun a : ℝ => -a) (-1) 0 := (hasDerivAt_id (0 : ℝ)).neg
    simpa using! hd'.comp 0 hi
  have hdiff : HasDerivAt (fun a : ℝ => μ a - μ (-a)) 2 0 := by
    simpa only [Pi.sub_def] using!
      (hd.sub hn).congr_deriv (show (1 : ℝ) - (-1) = 2 by norm_num)
  have hex : ∃ a : ℝ, μ a ≠ μ (-a) := by
    by_contra! h
    have hz : (fun a : ℝ => μ a - μ (-a)) = fun _ => 0 := by
      funext a
      exact sub_eq_zero.mpr (h a)
    rw [hz] at hdiff
    have he := hdiff.unique (hasDerivAt_const (0 : ℝ) (0 : ℝ))
    norm_num at he
  obtain ⟨a, ha⟩ := hex
  refine ⟨a, ?_, ?_⟩
  · intro he
    subst a
    exact ha (by rw [neg_zero])
  · intro he
    apply ha
    simpa only [μ, ofReal_neg] using congrArg Complex.re he

/-- A genuine global classical NLS solution changes its actual central
Dirichlet coordinate at a positive time. -/
theorem section7_exists_physicalNLS_dirichlet_motion
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ f : SmoothNLSData, ∃ time : ℝ, 0 < time ∧
      IsClassicalNLSTrajectory f.ordinary ∧
      canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet (f.ordinarySource p time).val 0 ≠
      canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet (f.source p).val 0 := by
  obtain ⟨a, ha, hμ⟩ := section7_exists_constant_dirichlet_pair hp hp1
  let f : SmoothNLSData :=
    ⟨ContinuousMap.const (AddCircle (2 : ℝ)) (a : ℂ), contDiff_const, fun _ => rfl⟩
  let time := Real.pi / (2 * ‖(a : ℂ)‖ ^ 2)
  have ha' : (a : ℂ) ≠ 0 := ofReal_ne_zero.mpr ha
  have htime : 0 < time := div_pos Real.pi_pos (mul_pos (by norm_num) (sq_pos_of_ne_zero
    (norm_ne_zero_iff.mpr ha')))
  have hphase : classicalNLSGaugePhase (-(‖(a : ℂ)‖ ^ 2 / 2)) time = -1 :=
    section7_constant_phase_half_turn a ha'
  have hstart : (f.source p).val = sourceConstantPotential a a := by
    simpa only [SmoothNLSData.source, f, conj_ofReal] using
      section7_smoothPeriodOneSourceAt_const p (a : ℂ)
  have hend : (f.ordinarySource p time).val = sourceConstantPotential (-a) (-a) := by
    have he := f.section7_ordinarySource_eq_constant_phase a rfl p time
    simpa only [hphase, neg_one_mul, map_neg, conj_ofReal, ofReal_neg] using he
  refine ⟨f, time, htime, f.ordinary_isClassical, ?_⟩
  rw [hend, hstart]
  exact Ne.symm hμ

/-- Every smooth ordinary trajectory satisfies the dissertation's
all-smooth-sequence solution definition in the global exponent range. -/
theorem SmoothNLSData.section7_ordinarySource_isSolution
    (f : SmoothNLSData) {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (hp2 : p ≤ 2) :
    IsOrdinaryNLSSolutionOn univ (f.source p) (f.ordinarySource p) := by
  obtain ⟨γ, hγ, _⟩ := existsUnique_global_ordinaryNLSSolution hp hp1 hp2 (f.source p)
  have he : f.ordinarySource p = γ := by
    funext time
    exact tendsto_nhds_unique tendsto_const_nhds
      (hγ.approximation (fun _ => f) tendsto_const_nhds time (mem_univ time))
  rw [he]
  exact hγ

/-- Physical Dirichlet nonconservation also holds in the dissertation's
precise approximation-solution sense, including the real Hilbert space. -/
theorem section7_exists_ordinaryNLSSolution_dirichlet_motion
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hp1 : 1 < p) (hp2 : p ≤ 2) :
    ∃ φ : realTypeSourceSubmodule p, ∃ γ : ℝ → realTypeSourceSubmodule p,
      IsOrdinaryNLSSolutionOn univ φ γ ∧ ∃ time : ℝ, 0 < time ∧
        canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet (γ time).val 0 ≠
        canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ.val 0 := by
  obtain ⟨f, time, ht, _, hm⟩ := section7_exists_physicalNLS_dirichlet_motion hp hp1
  exact ⟨f.source p, f.ordinarySource p,
    f.section7_ordinarySource_isSolution hp hp1 hp2, time, ht, hm⟩

end NLS.ZakharovShabat
