import NLS.ZakharovShabat.ParitySpectralCutoffs

/-!
# Entire perturbed parity products

The literal even and odd cutoffs converge locally uniformly to entire
functions for every pair with finite-exponent displacements. The proof keeps
the source's cutoff conventions and the corrected normalization constants.
Identifying the central parity spectra of actual potentials is a separate step.
-/

noncomputable section
open Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The correctly normalized even product, including its filled lattice values. -/
def evenSpectralPairProduct (ξ η : ℤ → ℂ) (z : ℂ) : ℂ :=
  entireSpectralPairProduct (parityRescale ξ 0) (parityRescale η 0) (z/2)

/-- The correctly normalized odd product, including its filled lattice values. -/
def oddSpectralPairProduct (ξ η : ℤ → ℂ) (z : ℂ) : ℂ :=
  -entireSpectralPairProduct (parityRescale ξ 1) (parityRescale η 1) ((z-(Real.pi : ℂ))/2)

/-- The even literal cutoffs converge locally uniformly at every spectral parameter. -/
theorem tendstoLocallyUniformlyOn_evenSpectralPairProduct (hp : p ≠ ⊤) (ξ η : ℤ → ℂ)
    (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p)
    (hη : Memℓp (fun n => η n-(Real.pi : ℂ)*n) p) :
    TendstoLocallyUniformlyOn (fun N z => evenSpectralPairCutoff ξ η z N)
      (evenSpectralPairProduct ξ η) atTop Set.univ := by
  have h := (tendstoLocallyUniformlyOn_entireSpectralPairProduct hp _ _
    (memℓp_parityRescale hp ξ hξ 0) (memℓp_parityRescale hp η hη 0)).comp (t := Set.univ)
      (fun z : ℂ => z/2) (fun _ _ => Set.mem_univ _) (by fun_prop)
  exact h.congr (fun N z _ => (evenSpectralPairCutoff_eq ξ η z N).symm)

/-- The even product is entire. -/
theorem analyticOnNhd_evenSpectralPairProduct (hp : p ≠ ⊤) (ξ η : ℤ → ℂ)
    (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p)
    (hη : Memℓp (fun n => η n-(Real.pi : ℂ)*n) p) :
    AnalyticOnNhd ℂ (evenSpectralPairProduct ξ η) Set.univ := by
  intro z _
  exact (analyticOnNhd_entireSpectralPairProduct hp _ _ (memℓp_parityRescale hp ξ hξ 0)
    (memℓp_parityRescale hp η hη 0) (z/2) (Set.mem_univ _)).comp (f := fun z : ℂ => z/2) (by fun_prop)

/-- The odd literal cutoffs converge locally uniformly at every spectral parameter. -/
theorem tendstoLocallyUniformlyOn_oddSpectralPairProduct (hp : p ≠ ⊤) (ξ η : ℤ → ℂ)
    (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p)
    (hη : Memℓp (fun n => η n-(Real.pi : ℂ)*n) p) :
    TendstoLocallyUniformlyOn (fun N z => oddSpectralPairCutoff ξ η z N)
      (oddSpectralPairProduct ξ η) atTop Set.univ := by
  have h := (tendstoLocallyUniformlyOn_entireSpectralPairProduct hp _ _
    (memℓp_parityRescale hp ξ hξ 1) (memℓp_parityRescale hp η hη 1)).comp (t := Set.univ)
      (fun z : ℂ => (z-(Real.pi : ℂ))/2) (fun _ _ => Set.mem_univ _) (by fun_prop)
  have hc := ((tendsto_const_nhds (x := (-1 : ℂ))).div tendsto_rescaledOddReference one_ne_zero).tendstoUniformlyOn_const
    (Set.univ : Set ℂ)
  have ha := analyticOnNhd_entireSpectralPairProduct hp _ _
    (memℓp_parityRescale hp ξ hξ 1) (memℓp_parityRescale hp η hη 1)
  have hcont : ContinuousOn (fun z : ℂ => entireSpectralPairProduct
      (parityRescale ξ 1) (parityRescale η 1) ((z-(Real.pi : ℂ))/2)) Set.univ :=
    ((continuousOn_univ.mp ha.continuousOn).comp (by fun_prop)).continuousOn
  have hh := hc.tendstoLocallyUniformlyOn.mul₀ h continuousOn_const hcont
  have he := hh.congr (G := fun N z => oddSpectralPairCutoff ξ η z N) (fun N z _ => by
    dsimp only [Pi.mul_apply, Pi.div_apply, Function.comp_def]
    rw [oddSpectralPairCutoff_eq]
    ring)
  change TendstoLocallyUniformlyOn (fun N z => oddSpectralPairCutoff ξ η z N)
    (fun z => (-1/1 : ℂ) * entireSpectralPairProduct
      (parityRescale ξ 1) (parityRescale η 1) ((z-(Real.pi : ℂ))/2)) atTop Set.univ at he
  unfold oddSpectralPairProduct
  simpa only [div_one, neg_one_mul] using he

/-- The odd product is entire. -/
theorem analyticOnNhd_oddSpectralPairProduct (hp : p ≠ ⊤) (ξ η : ℤ → ℂ)
    (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p)
    (hη : Memℓp (fun n => η n-(Real.pi : ℂ)*n) p) :
    AnalyticOnNhd ℂ (oddSpectralPairProduct ξ η) Set.univ := by
  intro z _
  exact ((analyticOnNhd_entireSpectralPairProduct hp _ _ (memℓp_parityRescale hp ξ hξ 1)
    (memℓp_parityRescale hp η hη 1) ((z-(Real.pi : ℂ))/2) (Set.mem_univ _)).comp
      (f := fun z : ℂ => (z-(Real.pi : ℂ))/2) (by fun_prop)).neg

/-- Every literal parity cutoff is entire, so derivative limits retain the same cutoff convention. -/
theorem analyticOnNhd_paritySpectralCutoffs (ξ η : ℤ → ℂ) (N : ℕ) :
    AnalyticOnNhd ℂ (fun z => evenSpectralPairCutoff ξ η z N) Set.univ ∧
    AnalyticOnNhd ℂ (fun z => oddSpectralPairCutoff ξ η z N) Set.univ := by
  have he : AnalyticOnNhd ℂ (fun z => ∏ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), spectralPairFactor ξ η z (2*n)) Set.univ :=
    fun z _ => Finset.analyticAt_fun_prod _ (fun n _ => analyticOnNhd_spectralPairFactor ξ η (2*n) Set.univ z (Set.mem_univ _))
  have ho : AnalyticOnNhd ℂ (fun z => ∏ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), spectralPairFactor ξ η z (2*n+1)) Set.univ :=
    fun z _ => Finset.analyticAt_fun_prod _ (fun n _ => analyticOnNhd_spectralPairFactor ξ η (2*n+1) Set.univ z (Set.mem_univ _))
  exact ⟨he.neg,fun z hz => analyticAt_const.mul (ho z hz)⟩

/-- Both parity-product derivative sequences converge locally uniformly, including across the lattice. -/
theorem tendstoLocallyUniformlyOn_deriv_paritySpectralProducts (hp : p ≠ ⊤) (ξ η : ℤ → ℂ)
    (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p)
    (hη : Memℓp (fun n => η n-(Real.pi : ℂ)*n) p) :
    TendstoLocallyUniformlyOn (fun N => deriv (fun z => evenSpectralPairCutoff ξ η z N))
      (deriv (evenSpectralPairProduct ξ η)) atTop Set.univ ∧
    TendstoLocallyUniformlyOn (fun N => deriv (fun z => oddSpectralPairCutoff ξ η z N))
      (deriv (oddSpectralPairProduct ξ η)) atTop Set.univ :=
  ⟨(tendstoLocallyUniformlyOn_evenSpectralPairProduct hp ξ η hξ hη).deriv
    (Filter.Eventually.of_forall (fun N => (analyticOnNhd_paritySpectralCutoffs ξ η N).1.differentiableOn)) isOpen_univ,
    (tendstoLocallyUniformlyOn_oddSpectralPairProduct hp ξ η hξ hη).deriv
    (Filter.Eventually.of_forall (fun N => (analyticOnNhd_paritySpectralCutoffs ξ η N).2.differentiableOn)) isOpen_univ⟩

end NLS.ZakharovShabat
