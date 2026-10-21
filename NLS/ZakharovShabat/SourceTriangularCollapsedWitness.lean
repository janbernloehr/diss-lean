import NLS.ZakharovShabat.SourceConstantPeriodicSpectrum
import NLS.ZakharovShabat.TriangularPeriodicSpectrum
import NLS.ZakharovShabat.L2GradientRestrictionFourier
import NLS.ZakharovShabat.SourceLemma8_2
import NLS.ZakharovShabat.CanonicalPeriodicFree

noncomputable section
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The original triangular constant source, as a bounded complex linear curve. -/
def sourceUpperConstantCLM : ℂ →L[ℂ] CoeffPair p :=
  (sourceConstantPotentialCLM (p := p)).comp (ContinuousLinearMap.inl ℂ ℂ ℂ)

@[simp] theorem sourceUpperConstantCLM_apply (a : ℂ) :
    sourceUpperConstantCLM (p := p) a = sourceConstantPotential a 0 := by
  exact sourceConstantPotentialCLM_apply a 0

/-- Near zero both actual central periodic endpoints of the triangular curve vanish. -/
theorem eventually_sourceUpperConstant_endpoints_zero (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∀ᶠ a in 𝓝 (0 : ℂ),
      canonicalPeriodicLeft hp hp1 (periodOnePotential (sourceUpperConstantCLM a))
        (periodOnePotential_mem _) 0 = 0 ∧
      canonicalPeriodicRight hp hp1 (periodOnePotential (sourceUpperConstantCLM a))
        (periodOnePotential_mem _) 0 = 0 := by
  let F := sourceUpperConstantCLM (p := p)
  have hreal : IsRealType (CoeffPair.toMax p (0 : CoeffPair p)) := by
    simpa only [map_zero] using (isRealType_zero (p := p))
  have hL := (continuousAt_canonicalPeriodicLeft_periodOne_of_realType hp hp1 0 hreal 0)
  have hR := (continuousAt_canonicalPeriodicRight_periodOne_of_realType hp hp1 0 hreal 0)
  have hLc : ContinuousAt (fun a : ℂ => canonicalPeriodicLeft hp hp1
      (periodOnePotential (F a)) (periodOnePotential_mem _) 0) 0 := by
    have hf : ContinuousAt F (0 : ℂ) := F.continuous.continuousAt
    have hh : ContinuousAt (fun ψ : CoeffPair p => canonicalPeriodicLeft hp hp1
        (periodOnePotential ψ) (periodOnePotential_mem _) 0) (F 0) := by
      simpa only [map_zero] using hL
    exact hh.comp hf
  have hRc : ContinuousAt (fun a : ℂ => canonicalPeriodicRight hp hp1
      (periodOnePotential (F a)) (periodOnePotential_mem _) 0) 0 := by
    have hh : ContinuousAt (fun ψ : CoeffPair p => canonicalPeriodicRight hp hp1
        (periodOnePotential ψ) (periodOnePotential_mem _) 0) (F 0) := by
      simpa only [map_zero] using hR
    exact hh.comp F.continuous.continuousAt
  have hLe := hLc.norm.eventually (gt_mem_nhds (show
      ‖canonicalPeriodicLeft hp hp1 (periodOnePotential (F 0)) (periodOnePotential_mem _) 0‖ <
        Real.pi / 2 by simp only [map_zero,canonicalPeriodicLeft_zero,Int.cast_zero,mul_zero,norm_zero]; positivity))
  have hRe := hRc.norm.eventually (gt_mem_nhds (show
      ‖canonicalPeriodicRight hp hp1 (periodOnePotential (F 0)) (periodOnePotential_mem _) 0‖ <
        Real.pi / 2 by simp only [map_zero,canonicalPeriodicRight_zero,Int.cast_zero,mul_zero,norm_zero]; positivity))
  filter_upwards [hLe,hRe] with a haL haR
  have hs : periodicSpectrum hp (periodOnePotential (F a)) = freeLattice := by
    change periodicSpectrum hp (periodOnePotential (sourceUpperConstantCLM a)) = _
    rw [sourceUpperConstantCLM_apply,periodOnePotential_sourceConstantPotential]
    simpa only [constantPeriodicPair,lp.single_zero] using periodicSpectrum_triangular hp (lp.single p 0 a)
  have he := canonicalPeriodicEndpoints_mem_spectrum hp hp1
    (periodOnePotential (F a)) (periodOnePotential_mem _) 0
  rw [hs] at he
  have hzero (z : ℂ) (hz : z ∈ freeLattice) (hn : ‖z‖ < Real.pi/2) : z = 0 := by
    have hstrip : z ∈ resonantStrip 0 := by
      change |z.re - Real.pi * (0 : ℤ)| ≤ Real.pi/2
      simp only [Int.cast_zero,mul_zero,sub_zero]
      exact (Complex.abs_re_le_norm z).trans hn.le
    simpa using (mem_freeLattice_iff_eq_center_of_mem_resonantStrip 0 hstrip).mp hz
  exact ⟨hzero _ he.1 haL,hzero _ he.2 haR⟩

/-- The genuine central Dirichlet root moves with derivative one half along this curve. -/
theorem hasDerivAt_dirichlet_sourceUpperConstant_zero (hp : p ≠ ⊤) (hp1 : 1 < p) :
    HasDerivAt (fun a : ℂ => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet
      (sourceUpperConstantCLM a) 0) (1/2 : ℂ) 0 := by
  have hreal : IsRealType (CoeffPair.toMax p (0 : CoeffPair p)) := by
    simpa only [map_zero] using (isRealType_zero (p := p))
  have hf := (analyticAt_canonicalPeriodOneBoundaryRoots_of_realType
    hp hp1 .dirichlet 0 hreal 0).differentiableAt.hasFDerivAt
  have he : fderiv ℂ (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ 0) 0 =
      sourceFreeDirichletCotangent p 0 := by
    rcases le_total (2 : ℝ≥0∞) p with h | h
    · exact fderiv_canonicalDirichletRoot_zero_eq_free hp hp1 h 0
    · exact fderiv_canonicalDirichletRoot_zero_eq_free_below_two hp hp1 h 0
  rw [he] at hf
  have hf' : HasFDerivAt (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ 0)
      (sourceFreeDirichletCotangent p 0) (sourceUpperConstantCLM (p := p) 0) := by
    simpa only [map_zero] using hf
  have h := hf'.comp_hasDerivAt 0 (sourceUpperConstantCLM (p := p)).hasDerivAt
  simpa only [Function.comp_def,sourceFreeDirichletCotangent_apply,sourceUpperConstantCLM_apply,
    sourceConstantPotential_fst,sourceConstantPotential_snd,neg_zero,ite_true,
    add_zero,mul_one] using h

/-- Every original-source neighborhood contains an actual triangular potential whose
central periodic gap is collapsed but whose Dirichlet root is outside it. -/
theorem exists_sourceUpperConstant_collapsed_dirichlet_ne_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p) (V : Set (CoeffPair p)) (hV : V ∈ 𝓝 (0 : CoeffPair p)) :
    ∃ a : ℂ, a ≠ 0 ∧ sourceConstantPotential (p := p) a 0 ∈ V ∧
      canonicalPeriodicLeft hp hp1 (periodOnePotential (sourceConstantPotential a 0))
        (periodOnePotential_mem _) 0 = 0 ∧
      canonicalPeriodicRight hp hp1 (periodOnePotential (sourceConstantPotential a 0))
        (periodOnePotential_mem _) 0 = 0 ∧
      canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet (sourceConstantPotential a 0) 0 ≠ 0 := by
  let F := sourceUpperConstantCLM (p := p)
  let μ := fun a : ℂ => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet (F a) 0
  have hv : ∀ᶠ a in 𝓝 (0 : ℂ), F a ∈ V := by
    apply F.continuous.continuousAt.preimage_mem_nhds
    simpa only [map_zero] using hV
  have he := eventually_sourceUpperConstant_endpoints_zero hp hp1
  by_contra h
  have hz : μ =ᶠ[𝓝 (0 : ℂ)] (fun _ => 0) := by
    filter_upwards [hv,he] with a ha hg
    by_contra hμ
    apply h
    have ha0 : a ≠ 0 := by
      intro e
      apply hμ
      simp only [μ,F,e,map_zero,canonicalPeriodOneBoundaryRoots_zero,Int.cast_zero,mul_zero]
    refine ⟨a,ha0,?_,?_,?_,?_⟩
    · simpa only [F,sourceUpperConstantCLM_apply] using ha
    · simpa only [sourceUpperConstantCLM_apply] using hg.1
    · simpa only [sourceUpperConstantCLM_apply] using hg.2
    · simpa only [μ,F,sourceUpperConstantCLM_apply] using hμ
  have hd : HasDerivAt μ (1/2 : ℂ) 0 := hasDerivAt_dirichlet_sourceUpperConstant_zero hp hp1
  have hc := hd.congr_of_eventuallyEq hz.symm
  have heq := hc.unique (hasDerivAt_const (0 : ℂ) (0 : ℂ))
  norm_num at heq

end NLS.ZakharovShabat
