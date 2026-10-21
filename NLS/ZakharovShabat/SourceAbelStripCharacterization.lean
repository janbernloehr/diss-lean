import NLS.Fourier.PhysicalSobolevStripTraces
import NLS.ZakharovShabat.SourceWeightedInclusion
import NLS.ZakharovShabat.SourcePhysicalL2Equiv

noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory
open scoped ENNReal
namespace NLS.ZakharovShabat
open NLS.Fourier

/-- The original weighted source image is exactly weighted membership of both
raw component sequences, in the original even-frequency normalization. -/
theorem mem_range_originalWeightedSourceCLM_iff {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (w : SpectralWeight) (φ : CoeffPair p) :
    φ ∈ range (originalWeightedSourceCLM (p := p) w) ↔
      Memℓp (fun n => (w (2*n):ℂ)*φ.fst n) p ∧
      Memℓp (fun n => (w (2*n):ℂ)*φ.snd n) p := by
  constructor
  · rintro ⟨b,rfl⟩
    simp only [originalWeightedSourceCLM_fst,originalWeightedSourceCLM_snd]
    exact ⟨b.fst.property,b.snd.property⟩
  · rintro ⟨hfst,hsnd⟩
    let b : WeightedCoeffPair (sourceFrequencyWeight w) p :=
      WithLp.toLp p (⟨φ.fst,hfst⟩,⟨φ.snd,hsnd⟩)
    refine ⟨b,?_⟩
    apply (CoeffPair.toMax p).injective
    apply Prod.ext <;> ext n
    · change (originalWeightedSourceCLM w b).fst n = φ.fst n
      rw [originalWeightedSourceCLM_fst]
      rfl
    · change (originalWeightedSourceCLM w b).snd n = φ.snd n
      rw [originalWeightedSourceCLM_snd]
      rfl

/-- Native weighted source membership and the existing normalized decoder image agree. -/
theorem range_originalWeightedSourceCLM_eq_normalized {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (w : SpectralWeight) :
    range (originalWeightedSourceCLM (p := p) w) = range (normalizedWeightedSource (p := p) w) := by
  ext φ
  constructor
  · rintro ⟨b,rfl⟩
    exact ⟨sourcePairWeightCoordinates w b,rfl⟩
  · rintro ⟨b,rfl⟩
    refine ⟨(sourcePairWeightCoordinates w).symm b,?_⟩
    change normalizedWeightedSource w
      (sourcePairWeightCoordinates w ((sourcePairWeightCoordinates w).symm b)) = _
    rw [LinearIsometryEquiv.apply_symm_apply]

/-- The original Abel Hilbert source has precisely the corrected periodic
holomorphic realizations of both raw components with physical Sobolev norm traces. -/
theorem source_abel_range_iff_strip_extensions (s a : ℝ) (hs : 0 ≤ s) (ha : 0 < a)
    (φ : CoeffPair 2) :
    φ ∈ range (normalizedWeightedSource (p := 2) (SpectralWeight.abel s a hs ha.le)) ↔
      (∃ f : ℂ → ℂ, Function.Periodic f 1 ∧
        AnalyticOnNhd ℂ f {z : ℂ | |z.im| < a/Real.pi} ∧
        (∀ n : ℤ, periodOneCoefficient (fun x : ℝ => f x) n = φ.fst n) ∧
        HasSobolevNormStripTraces s a f) ∧
      (∃ g : ℂ → ℂ, Function.Periodic g 1 ∧
        AnalyticOnNhd ℂ g {z : ℂ | |z.im| < a/Real.pi} ∧
        (∀ n : ℤ, periodOneCoefficient (fun x : ℝ => g x) n = φ.snd n) ∧
        HasSobolevNormStripTraces s a g) := by
  rw [← range_originalWeightedSourceCLM_eq_normalized,mem_range_originalWeightedSourceCLM_iff]
  exact and_congr (memlp_abel_iff_exists_sobolev_strip s a hs ha φ.fst)
    (memlp_abel_iff_exists_sobolev_strip s a hs ha φ.snd)

/-- Actual Fourier coefficients identify the continuous physical source components
with the existing canonical source-to-L2 map. -/
theorem sourcePhysicalL2_representative_of_coefficients (φ : CoeffPair 2)
    (f g : ℝ → ℂ) (hf : Continuous f) (hg : Continuous g)
    (hfc : ∀ n : ℤ, periodOneCoefficient f n = φ.fst n)
    (hgc : ∀ n : ℤ, periodOneCoefficient g n = φ.snd n) :
    intervalL2Representative (sourcePhysicalL2 φ) =ᵐ[volume.restrict (Ioc 0 1)]
      (fun x => (f x,g x)) := by
  have hfm := memLp_two_interval hf 0 1 (by norm_num : (0:ℝ) ≤ 1)
  have hgm := memLp_two_interval hg 0 1 (by norm_num : (0:ℝ) ≤ 1)
  have hfcoef : unitIntervalMemLpCoefficients f hfm = φ.fst := by
    ext n
    rw [unitIntervalMemLpCoefficients_apply,
      intervalFourierCoefficient_eq_fourierCoeffOn (by norm_num)]
    exact hfc n
  have hgcoef : unitIntervalMemLpCoefficients g hgm = φ.snd := by
    ext n
    rw [unitIntervalMemLpCoefficients_apply,
      intervalFourierCoefficient_eq_fourierCoeffOn (by norm_num)]
    exact hgc n
  have hfae : (unitL2SynthesisEquiv φ.fst : ℝ → ℂ) =ᵐ[volume.restrict (Ioc 0 1)] f := by
    rw [← hfcoef,unitL2SynthesisEquiv_memLpCoefficients]
    exact hfm.coeFn_toLp
  have hgae : (unitL2SynthesisEquiv φ.snd : ℝ → ℂ) =ᵐ[volume.restrict (Ioc 0 1)] g := by
    rw [← hgcoef,unitL2SynthesisEquiv_memLpCoefficients]
    exact hgm.coeFn_toLp
  rw [← sourcePhysicalL2Equiv_apply]
  filter_upwards [hfae,hgae] with x hx hy
  exact Prod.ext hx hy

/-- The corrected strip equivalence extends the actual original physical potential,
not just an independently supplied pair of sequences with matching coefficients. -/
theorem source_abel_range_iff_physical_strip_extensions (s a : ℝ) (hs : 0 ≤ s) (ha : 0 < a)
    (φ : CoeffPair 2) :
    φ ∈ range (normalizedWeightedSource (p := 2) (SpectralWeight.abel s a hs ha.le)) ↔
      ∃ f g : ℂ → ℂ, Function.Periodic f 1 ∧ Function.Periodic g 1 ∧
        AnalyticOnNhd ℂ f {z : ℂ | |z.im| < a/Real.pi} ∧
        AnalyticOnNhd ℂ g {z : ℂ | |z.im| < a/Real.pi} ∧
        HasSobolevNormStripTraces s a f ∧ HasSobolevNormStripTraces s a g ∧
        physicalBase (periodOnePotential φ) =ᵐ[volume.restrict (Ioc 0 1)]
          (fun x : ℝ => (f x,g x)) := by
  constructor
  · intro hφ
    obtain ⟨⟨f,hfp,hfa,hfc,hft⟩,⟨g,hgp,hga,hgc,hgt⟩⟩ :=
      (source_abel_range_iff_strip_extensions s a hs ha φ).mp hφ
    have hy : |(0:ℝ)| < a/Real.pi := by simpa only [abs_zero] using div_pos ha Real.pi_pos
    have hff : Continuous (fun x : ℝ => f x) := by
      simpa only [Complex.ofReal_zero,zero_mul,add_zero] using
        continuous_horizontal_of_analytic_strip a f hfa 0 hy
    have hgg : Continuous (fun x : ℝ => g x) := by
      simpa only [Complex.ofReal_zero,zero_mul,add_zero] using
        continuous_horizontal_of_analytic_strip a g hga 0 hy
    exact ⟨f,g,hfp,hgp,hfa,hga,hft,hgt,(sourcePhysicalL2_representative φ).symm.trans
      (sourcePhysicalL2_representative_of_coefficients φ _ _ hff hgg hfc hgc)⟩
  · rintro ⟨f,g,hfp,hgp,hfa,hga,hft,hgt,hphysical⟩
    have hp := (sourcePhysicalL2_representative φ).trans hphysical
    have hf : ((sourcePhysicalL2 φ).ofLp.1 : ℝ → ℂ) =ᵐ[volume.restrict (Ioc 0 1)]
        (fun x : ℝ => f x) := by
      filter_upwards [hp] with x hx
      exact congrArg Prod.fst hx
    have hg : ((sourcePhysicalL2 φ).ofLp.2 : ℝ → ℂ) =ᵐ[volume.restrict (Ioc 0 1)]
        (fun x : ℝ => g x) := by
      filter_upwards [hp] with x hx
      exact congrArg Prod.snd hx
    apply (source_abel_range_iff_strip_extensions s a hs ha φ).mpr
    refine ⟨⟨f,hfp,hfa,fun n => ?_,hft⟩,⟨g,hgp,hga,fun n => ?_,hgt⟩⟩
    · have he := congrFun (fourierCoeffOn_congr_ae (by norm_num) hf) n
      rw [← intervalFourierCoefficient_eq_fourierCoeffOn (by norm_num),
        (sourcePhysicalL2_coefficients φ n).1] at he
      exact he.symm
    · have he := congrFun (fourierCoeffOn_congr_ae (by norm_num) hg) n
      rw [← intervalFourierCoefficient_eq_fourierCoeffOn (by norm_num),
        (sourcePhysicalL2_coefficients φ n).2] at he
      exact he.symm

/-- The forward-only reading of the printed narrower-strip assertion is valid:
original Abel data extend the actual physical source and have Sobolev norm traces there. -/
theorem source_abel_printed_strip_forward (s a : ℝ) (hs : 0 ≤ s) (ha : 0 < a)
    (φ : CoeffPair 2)
    (hφ : φ ∈ range (normalizedWeightedSource (p := 2) (SpectralWeight.abel s a hs ha.le))) :
    ∃ f g : ℂ → ℂ, Function.Periodic f 1 ∧ Function.Periodic g 1 ∧
      AnalyticOnNhd ℂ f {z : ℂ | |z.im| < a/(2*Real.pi)} ∧
      AnalyticOnNhd ℂ g {z : ℂ | |z.im| < a/(2*Real.pi)} ∧
      HasSobolevNormStripTraces s (a/2) f ∧ HasSobolevNormStripTraces s (a/2) g ∧
      physicalBase (periodOnePotential φ) =ᵐ[volume.restrict (Ioc 0 1)]
        (fun x : ℝ => (f x,g x)) := by
  obtain ⟨f,g,hfp,hgp,hfa,hga,hft,hgt,hphys⟩ :=
    (source_abel_range_iff_physical_strip_extensions s a hs ha φ).mp hφ
  have hwidth : a/(2*Real.pi) ≤ a/Real.pi := by
    have he : a/(2*Real.pi) = (a/Real.pi)/2 := by field_simp
    rw [he]
    linarith [div_pos ha Real.pi_pos]
  have narrow (F : ℂ → ℂ) (hF : HasSobolevNormStripTraces s a F) :
      HasSobolevNormStripTraces s (a/2) F := by
    obtain ⟨r,hr,he⟩ := hF
    refine ⟨r,hr,fun y hy => he y ?_⟩
    rw [div_div] at hy
    exact hy.trans_le hwidth
  exact ⟨f,g,hfp,hgp,hfa.mono (fun _ hz => lt_of_lt_of_le hz hwidth),
    hga.mono (fun _ hz => lt_of_lt_of_le hz hwidth),narrow f hft,narrow g hgt,hphys⟩

end NLS.ZakharovShabat
