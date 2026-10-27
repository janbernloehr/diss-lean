import NLS.Fourier.PeriodicSobolevEmbedding
import NLS.Fourier.SmoothPeriodicDistributionDerivative
import NLS.ZakharovShabat.SourceUnboundedOperator
import NLS.ZakharovShabat.ClosedOperator

/-! # The closed Zakharov–Shabat operator on original periodic distributions

The base space and domain consist of actual period-two smooth-test functionals,
with the source's finite component-sum Fourier norms. The inclusion preserves
the underlying distributions, and the operator is the signed distributional
derivative plus the off-diagonal Sobolev–Wiener product. Its graph is closed in
the base-space topology for every finite Banach exponent and every potential.
-/
noncomputable section
set_option autoImplicit false
open scoped ENNReal
namespace NLS.ZakharovShabat.NativePeriodic
open NLS.Fourier SmoothPeriodicTest PeriodicFourierLebesgue

/-- Original period-two distribution pairs with the finite component-sum norm. -/
abbrev Space (p : ℝ≥0∞) := WithLp p
  (PeriodicFourierLebesgue 2 Weight.one p × PeriodicFourierLebesgue 2 Weight.one p)

/-- The full one-derivative domain, with its stronger Fourier norm. -/
abbrev Domain (p : ℝ≥0∞) := WithLp p
  (PeriodicFourierLebesgue 2 (Weight.sobolev 1) p ×
    PeriodicFourierLebesgue 2 (Weight.sobolev 1) p)

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Taking the actual distribution coefficients preserves the source norm exactly. -/
def coefficients (p : ℝ≥0∞) [Fact (1 ≤ p)] : Space p ≃ₗᵢ[ℂ] CoeffPair p :=
  (unweightedCoefficients p).withLpProdCongr p (unweightedCoefficients p)

/-- The corresponding exact isometry on the one-derivative domain. -/
def domainCoefficients (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    Domain p ≃ₗᵢ[ℂ] WeightedCoeffPair (Weight.sobolev 1) p :=
  (coefficientsIsometry (Weight.sobolev 1) p (Weight.hasTemperedInverse_sobolev 1)).withLpProdCongr p
    (coefficientsIsometry (Weight.sobolev 1) p (Weight.hasTemperedInverse_sobolev 1))

@[simp] theorem coefficients_fst (u : Space p) (n : ℤ) :
    (coefficients p u).fst n = u.fst.val (mode (-n)) :=
  unweightedCoefficients_apply p u.fst n

@[simp] theorem coefficients_snd (u : Space p) (n : ℤ) :
    (coefficients p u).snd n = u.snd.val (mode (-n)) :=
  unweightedCoefficients_apply p u.snd n

@[simp] theorem domainCoefficients_fst (u : Domain p) (n : ℤ) :
    (domainCoefficients p u).fst.val n = u.fst.val (mode (-n)) := rfl

@[simp] theorem domainCoefficients_snd (u : Domain p) (n : ℤ) :
    (domainCoefficients p u).snd.val n = u.snd.val (mode (-n)) := rfl

/-- Inclusion into the original distribution base space. -/
def inclusion : Domain p →L[ℂ] Space p :=
  (coefficients p).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (sourceDomainInclusion.comp (domainCoefficients p).toContinuousLinearEquiv.toContinuousLinearMap)

@[simp] theorem coefficients_inclusion (f : Domain p) :
    coefficients p (inclusion f) = sourceDomainInclusion (domainCoefficients p f) := by
  exact (coefficients p).apply_symm_apply _

@[simp] theorem inclusion_fst_val (f : Domain p) : (inclusion f).fst.val = f.fst.val := by
  apply Distribution.ext_coefficients
  intro n
  rw [← coefficients_fst, coefficients_inclusion, sourceDomainInclusion_fst_apply,
    domainCoefficients_fst]

@[simp] theorem inclusion_snd_val (f : Domain p) : (inclusion f).snd.val = f.snd.val := by
  apply Distribution.ext_coefficients
  intro n
  rw [← coefficients_snd, coefficients_inclusion, sourceDomainInclusion_snd_apply,
    domainCoefficients_snd]

theorem inclusion_injective : Function.Injective (inclusion (p := p)) := by
  intro f g h
  apply (domainCoefficients p).injective
  apply sourceDomainInclusion_injective
  simpa only [coefficients_inclusion] using congrArg (coefficients p) h

theorem inclusion_denseRange (hp : p ≠ ⊤) : DenseRange (inclusion (p := p)) := by
  change DenseRange ((coefficients p).symm ∘ sourceDomainInclusion ∘ domainCoefficients p)
  exact (coefficients p).symm.surjective.denseRange.comp
    ((sourceDomainInclusion_denseRange hp).comp (domainCoefficients p).surjective.denseRange
      sourceDomainInclusion.continuous) (coefficients p).symm.continuous

/-- The full operator on the original one-derivative distribution domain. -/
def operator (hp : p ≠ ⊤) (φ : Space p) : Domain p →L[ℂ] Space p :=
  (coefficients p).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((sourceOperator hp (coefficients p φ)).comp
      (domainCoefficients p).toContinuousLinearEquiv.toContinuousLinearMap)

@[simp] theorem coefficients_operator (hp : p ≠ ⊤) (φ : Space p) (f : Domain p) :
    coefficients p (operator hp φ f) = sourceOperator hp (coefficients p φ) (domainCoefficients p f) :=
  (coefficients p).apply_symm_apply _

theorem operator_fst_coefficient (hp : p ≠ ⊤) (φ : Space p) (f : Domain p) (n : ℤ) :
    (operator hp φ f).fst.val (mode (-n)) =
      -(Real.pi : ℂ) * n * f.fst.val (mode (-n)) +
        ∑' k : ℤ, φ.fst.val (mode (-(n-k))) * f.snd.val (mode (-k)) := by
  rw [← coefficients_fst, coefficients_operator]
  change (ZakharovShabat.operator hp (CoeffPair.toMax p (coefficients p φ))
    (WeightedCoeffPair.toMax (Weight.sobolev 1) p (domainCoefficients p f))).1 n = _
  rw [ZakharovShabat.operator_fst_apply]
  change -(Real.pi : ℂ) * n * (domainCoefficients p f).fst.val n +
    ∑' k : ℤ, (coefficients p φ).fst (n-k) * (domainCoefficients p f).snd.val k = _
  simp only [coefficients_fst, domainCoefficients_fst, domainCoefficients_snd]

theorem operator_snd_coefficient (hp : p ≠ ⊤) (φ : Space p) (f : Domain p) (n : ℤ) :
    (operator hp φ f).snd.val (mode (-n)) =
      (Real.pi : ℂ) * n * f.snd.val (mode (-n)) +
        ∑' k : ℤ, φ.snd.val (mode (-(n-k))) * f.fst.val (mode (-k)) := by
  rw [← coefficients_snd, coefficients_operator]
  change (ZakharovShabat.operator hp (CoeffPair.toMax p (coefficients p φ))
    (WeightedCoeffPair.toMax (Weight.sobolev 1) p (domainCoefficients p f))).2 n = _
  rw [ZakharovShabat.operator_snd_apply]
  change (Real.pi : ℂ) * n * (domainCoefficients p f).snd.val n +
    ∑' k : ℤ, (coefficients p φ).snd (n-k) * (domainCoefficients p f).fst.val k = _
  simp only [coefficients_snd, domainCoefficients_fst, domainCoefficients_snd]

/-- The first component is the literal original-distribution differential expression. -/
theorem operator_fst_val (hp : p ≠ ⊤) (φ : Space p) (f : Domain p) :
    (operator hp φ f).fst.val = Complex.I • f.fst.val.derivative +
      (youngProduct (show YoungRelation p 1 p by simp [YoungRelation, add_comm])
        φ.fst (sobolevToWiener hp f.snd)).val := by
  apply Distribution.ext_coefficients
  intro n
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul,
    Distribution.derivative_coefficient, youngProduct_coefficient, sobolevToWiener_coefficient,
    operator_fst_coefficient]
  congr 1
  simp only [Complex.ofReal_ofNat]
  ring_nf
  simp [Complex.I_sq]

/-- The second component retains the opposite derivative sign and off-diagonal factor. -/
theorem operator_snd_val (hp : p ≠ ⊤) (φ : Space p) (f : Domain p) :
    (operator hp φ f).snd.val = -Complex.I • f.snd.val.derivative +
      (youngProduct (show YoungRelation p 1 p by simp [YoungRelation, add_comm])
        φ.snd (sobolevToWiener hp f.fst)).val := by
  apply Distribution.ext_coefficients
  intro n
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul,
    Distribution.derivative_coefficient, youngProduct_coefficient, sobolevToWiener_coefficient,
    operator_snd_coefficient]
  congr 1
  simp only [Complex.ofReal_ofNat]
  ring_nf
  simp [Complex.I_sq]

/-- The exact combined Fourier energy, without replacing the source norm. -/
theorem norm_rpow_eq_tsum (hp : p ≠ ⊤) (f : Space p) :
    ‖f‖ ^ p.toReal = ∑' n : ℤ,
      (‖f.fst.val (mode (-n))‖ ^ p.toReal + ‖f.snd.val (mode (-n))‖ ^ p.toReal) := by
  simpa only [LinearIsometryEquiv.norm_map, coefficients_fst, coefficients_snd] using
    CoeffPair.norm_rpow_eq_tsum hp (coefficients p f)

/-- The actual original-distribution spectral pencil. -/
def pencil (hp : p ≠ ⊤) (φ : Space p) (z : ℂ) : Domain p →L[ℂ] Space p :=
  z • inclusion - operator hp φ

@[simp] theorem coefficients_pencil (hp : p ≠ ⊤) (φ : Space p) (z : ℂ) (f : Domain p) :
    coefficients p (pencil hp φ z f) = sourceSpectralPencil hp (coefficients p φ) z
      (domainCoefficients p f) := by
  change coefficients p (z • inclusion f - operator hp φ f) = _
  rw [map_sub, map_smul, coefficients_inclusion, coefficients_operator, sourceSpectralPencil_eq]
  rfl

/-- The inverse takes values in the full original one-derivative normed space. -/
def resolventToDomain (hp : p ≠ ⊤) (φ : Space p) (z : ℂ) : Space p →L[ℂ] Domain p :=
  (domainCoefficients p).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((sourceResolventToDomain hp (coefficients p φ) z).comp
      (coefficients p).toContinuousLinearEquiv.toContinuousLinearMap)

@[simp] theorem domainCoefficients_resolventToDomain (hp : p ≠ ⊤) (φ : Space p) (z : ℂ)
    (f : Space p) : domainCoefficients p (resolventToDomain hp φ z f) =
      sourceResolventToDomain hp (coefficients p φ) z (coefficients p f) :=
  (domainCoefficients p).apply_symm_apply _

theorem pencil_resolventToDomain (hp : p ≠ ⊤) (φ : Space p) (z : ℂ)
    (hz : z ∈ sourceResolventSet hp (coefficients p φ)) (f : Space p) :
    pencil hp φ z (resolventToDomain hp φ z f) = f := by
  apply (coefficients p).injective
  rw [coefficients_pencil, domainCoefficients_resolventToDomain,
    sourceSpectralPencil_sourceResolventToDomain hp _ z hz]

theorem resolventToDomain_pencil (hp : p ≠ ⊤) (φ : Space p) (z : ℂ)
    (hz : z ∈ sourceResolventSet hp (coefficients p φ)) (f : Domain p) :
    resolventToDomain hp φ z (pencil hp φ z f) = f := by
  apply (domainCoefficients p).injective
  rw [domainCoefficients_resolventToDomain, coefficients_pencil,
    sourceResolventToDomain_sourceSpectralPencil hp _ z hz]

/-- Bounded two-sided invertibility, defined directly on the native distribution spaces. -/
def resolventSet (hp : p ≠ ⊤) (φ : Space p) : Set ℂ :=
  {z | ∃ R : Space p →L[ℂ] Domain p,
    (∀ f, pencil hp φ z (R f) = f) ∧ (∀ f, R (pencil hp φ z f) = f)}

/-- Both directions use the full domain; no spectral condition is built into the definition. -/
theorem resolventSet_eq (hp : p ≠ ⊤) (φ : Space p) :
    resolventSet hp φ = sourceResolventSet hp (coefficients p φ) := by
  ext z
  constructor
  · rintro ⟨R, hleft, hright⟩
    have hb : Function.Bijective (pencil hp φ z) :=
      ⟨Function.LeftInverse.injective hright, Function.RightInverse.surjective hleft⟩
    have he : coefficients p ∘ pencil hp φ z =
        sourceSpectralPencil hp (coefficients p φ) z ∘ domainCoefficients p :=
      funext (coefficients_pencil hp φ z)
    have hc := (coefficients p).bijective.comp hb
    rw [he, Function.Bijective.of_comp_iff _ (domainCoefficients p).bijective] at hc
    exact hc
  · intro hz
    exact ⟨resolventToDomain hp φ z, pencil_resolventToDomain hp φ z hz,
      resolventToDomain_pencil hp φ z hz⟩

/-- The graph is a submodule of two copies of the original base space. -/
def graph (hp : p ≠ ⊤) (φ : Space p) : Submodule ℂ (Space p × Space p) :=
  LinearMap.range (inclusion.prod (operator hp φ)).toLinearMap

@[simp] theorem mem_graph (hp : p ≠ ⊤) (φ : Space p) (x y : Space p) :
    (x,y) ∈ graph hp φ ↔ ∃ f : Domain p, inclusion f = x ∧ operator hp φ f = y := by
  simp [graph, LinearMap.mem_range, Prod.ext_iff]

private theorem graph_fst_zero (hp : p ≠ ⊤) (φ : Space p) (v : Space p × Space p)
    (hv : v ∈ graph hp φ) (hzero : v.1 = 0) : v.2 = 0 := by
  obtain ⟨f, hf, hL⟩ := (mem_graph hp φ v.1 v.2).mp hv
  have hf0 : f = 0 := inclusion_injective (hf.trans (hzero.trans (map_zero _).symm))
  simpa only [hf0, map_zero] using hL.symm

/-- The closed unbounded operator with its actual domain inside the distribution base space. -/
def unboundedOperator (hp : p ≠ ⊤) (φ : Space p) : Space p →ₗ.[ℂ] Space p :=
  (graph hp φ).toLinearPMap

@[simp] theorem unboundedOperator_graph (hp : p ≠ ⊤) (φ : Space p) :
    (unboundedOperator hp φ).graph = graph hp φ :=
  Submodule.toLinearPMap_graph_eq _ (graph_fst_zero hp φ)

/-- Its domain consists of exactly all one-derivative periodic distributions. -/
@[simp] theorem mem_unboundedOperator_domain (hp : p ≠ ⊤) (φ : Space p) (x : Space p) :
    x ∈ (unboundedOperator hp φ).domain ↔ ∃ f : Domain p, inclusion f = x := by
  rw [LinearPMap.mem_domain_iff, unboundedOperator_graph]
  simp only [mem_graph]
  constructor
  · rintro ⟨y, f, hf, _⟩
    exact ⟨f, hf⟩
  · rintro ⟨f, rfl⟩
    exact ⟨operator hp φ f, f, rfl, rfl⟩

theorem unboundedOperator_domain (hp : p ≠ ⊤) (φ : Space p) :
    (unboundedOperator hp φ).domain = LinearMap.range (inclusion (p := p)).toLinearMap := by
  ext x
  exact mem_unboundedOperator_domain hp φ x

@[simp] theorem unboundedOperator_apply_inclusion (hp : p ≠ ⊤) (φ : Space p)
    (f : Domain p) (hf : inclusion f ∈ (unboundedOperator hp φ).domain) :
    unboundedOperator hp φ ⟨inclusion f, hf⟩ = operator hp φ f := by
  symm
  rw [LinearPMap.image_iff hf, unboundedOperator_graph, mem_graph]
  exact ⟨f, rfl, rfl⟩

theorem unboundedOperator_dense_domain (hp : p ≠ ⊤) (φ : Space p) :
    Dense ((unboundedOperator hp φ).domain : Set (Space p)) := by
  rw [unboundedOperator_domain]
  exact inclusion_denseRange hp

/-- Closedness in the base norm, with no smallness or finite-support restriction. -/
theorem isClosed_graph (hp : p ≠ ⊤) (φ : Space p) :
    IsClosed (graph hp φ : Set (Space p × Space p)) := by
  obtain ⟨z, hz⟩ := ZakharovShabat.resolventSet_nonempty hp (CoeffPair.toMax p (coefficients p φ))
  have hz' : z ∈ resolventSet hp φ := by
    rwa [resolventSet_eq, sourceResolventSet_eq]
  obtain ⟨R, hleft, hright⟩ := hz'
  have he : (graph hp φ : Set (Space p × Space p)) =
      {v | inclusion (R (z • v.1 - v.2)) = v.1} := by
    ext v
    change (v.1, v.2) ∈ graph hp φ ↔ inclusion (R (z • v.1 - v.2)) = v.1
    rw [mem_graph]
    constructor
    · rintro ⟨f, hf, hL⟩
      rw [← hf, ← hL]
      change inclusion (R (pencil hp φ z f)) = inclusion f
      rw [hright]
    · intro h
      refine ⟨R (z • v.1 - v.2), h, ?_⟩
      have hP := hleft (z • v.1 - v.2)
      change z • inclusion (R (z • v.1 - v.2)) - operator hp φ (R (z • v.1 - v.2)) = _ at hP
      rw [h] at hP
      exact sub_right_inj.mp hP
  rw [he]
  exact isClosed_eq
    ((inclusion (p := p)).continuous.comp (R.continuous.comp
      ((continuous_fst.const_smul z).sub continuous_snd))) continuous_fst

theorem unboundedOperator_isClosed (hp : p ≠ ⊤) (φ : Space p) :
    (unboundedOperator hp φ).IsClosed := by
  unfold LinearPMap.IsClosed
  rw [unboundedOperator_graph]
  exact isClosed_graph hp φ

/-- Limits in the base space preserve the domain and the actual distributional equation. -/
theorem exists_domain_of_tendsto (hp : p ≠ ⊤) (φ : Space p)
    {ι : Type*} {l : Filter ι} [l.NeBot] (f : ι → Domain p) {x y : Space p}
    (hx : Filter.Tendsto (fun i => inclusion (f i)) l (nhds x))
    (hy : Filter.Tendsto (fun i => operator hp φ (f i)) l (nhds y)) :
    ∃ g : Domain p, inclusion g = x ∧ operator hp φ g = y := by
  apply (mem_graph hp φ x y).mp
  apply (isClosed_graph hp φ).mem_of_tendsto (hx.prodMk_nhds hy)
  exact Filter.Eventually.of_forall fun i => (mem_graph hp φ _ _).mpr ⟨f i, rfl, rfl⟩

/-- The base-space inverse of the actual native pencil. -/
def resolvent (hp : p ≠ ⊤) (φ : Space p) (z : ℂ) : Space p →L[ℂ] Space p :=
  inclusion.comp (resolventToDomain hp φ z)

theorem resolvent_eq_conjugate (hp : p ≠ ⊤) (φ : Space p) (z : ℂ) :
    resolvent hp φ z = (coefficients p).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
      ((sourceResolvent hp (coefficients p φ) z).comp
        (coefficients p).toContinuousLinearEquiv.toContinuousLinearMap) := by
  ext f : 1
  apply (coefficients p).injective
  change coefficients p (inclusion (resolventToDomain hp φ z f)) =
    coefficients p ((coefficients p).symm (sourceResolvent hp (coefficients p φ) z (coefficients p f)))
  rw [coefficients_inclusion, domainCoefficients_resolventToDomain,
    LinearIsometryEquiv.apply_symm_apply, sourceResolvent_eq_inclusion_comp]
  rfl

theorem isCompactOperator_resolvent (hp : p ≠ ⊤) (φ : Space p) (z : ℂ) :
    IsCompactOperator (resolvent hp φ z) := by
  rw [resolvent_eq_conjugate]
  exact ((isCompactOperator_sourceResolvent hp _ z).comp_clm
    (coefficients p).toContinuousLinearEquiv.toContinuousLinearMap).clm_comp
      (coefficients p).symm.toContinuousLinearEquiv.toContinuousLinearMap

/-- The native bounded-inverse spectrum. -/
def spectrum (hp : p ≠ ⊤) (φ : Space p) : Set ℂ := (resolventSet hp φ)ᶜ

theorem spectrum_eq (hp : p ≠ ⊤) (φ : Space p) :
    spectrum hp φ = periodicSpectrum hp (CoeffPair.toMax p (coefficients p φ)) := by
  rw [spectrum, resolventSet_eq, sourceResolventSet_eq]
  rfl

theorem discreteTopology_spectrum (hp : p ≠ ⊤) (φ : Space p) :
    DiscreteTopology ↥(spectrum hp φ) := by
  rw [spectrum, resolventSet_eq]
  exact discreteTopology_sourceResolventSet_compl hp _

end NLS.ZakharovShabat.NativePeriodic
