import NLS.ZakharovShabat.SampledDiscriminantLp
import NLS.ZakharovShabat.PeriodOneEmbedding

/-!
# Lemma 8.4 in the original source space

The errors in the sampled discriminant and its spectral derivative are
actual ℓp sequences. One original open convex neighborhood and one bound
work for every sampling sequence in the closed quarter-pi disks, including
central and negative indices. The sampling choices need no regularity.
A majorant is chosen for each potential before choosing any sample points.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual sampled discriminant error, as an element of the source coefficient space. -/
def sourceDiscriminantSampleError (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (z : ℤ → ℂ) (hz : ∀ n : ℤ, ‖z n-(Real.pi : ℂ)*n‖ ≤ Real.pi/4) : Coeff p :=
  ⟨_,(memℓp_sampled_discriminant_errors hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) z hz).1⟩

/-- The actual sampled spectral-derivative error, with the free sign retained. -/
def sourceDiscriminantDerivativeSampleError (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (z : ℤ → ℂ) (hz : ∀ n : ℤ, ‖z n-(Real.pi : ℂ)*n‖ ≤ Real.pi/4) : Coeff p :=
  ⟨_,(memℓp_sampled_discriminant_errors hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) z hz).2⟩

/-- Evaluation recovers the actual value error at each signed sample index. -/
@[simp] theorem sourceDiscriminantSampleError_apply (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (z : ℤ → ℂ) (hz : ∀ n : ℤ, ‖z n-(Real.pi : ℂ)*n‖ ≤ Real.pi/4) (n : ℤ) :
    sourceDiscriminantSampleError hp hp1 φ z hz n = canonicalDiscriminant hp (periodOnePotential φ) (z n)-2*cos (z n) := rfl

/-- Evaluation recovers the actual derivative error at each signed sample index. -/
@[simp] theorem sourceDiscriminantDerivativeSampleError_apply (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (z : ℤ → ℂ) (hz : ∀ n : ℤ, ‖z n-(Real.pi : ℂ)*n‖ ≤ Real.pi/4) (n : ℤ) :
    sourceDiscriminantDerivativeSampleError hp hp1 φ z hz n = deriv (canonicalDiscriminant hp (periodOnePotential φ)) (z n)+2*sin (z n) := rfl

/-- Uniform disc majorants and actual sampled ℓp norm bounds on one source neighborhood. -/
structure SourceLemma8_4Data (hp : p ≠ ⊤) (hp1 : 1 < p) (U : Set (CoeffPair p)) (K : ℝ) : Prop where
  disc_majorants : ∀ ψ ∈ U, ∃ A : Coeff p, ‖A‖ ≤ K ∧
    ∀ (n : ℤ) (w : ℂ), ‖w-(Real.pi : ℂ)*n‖ ≤ Real.pi/4 →
      ‖canonicalDiscriminant hp (periodOnePotential ψ) w-2*cos w‖ ≤ ‖A n‖ ∧
      ‖deriv (canonicalDiscriminant hp (periodOnePotential ψ)) w+2*sin w‖ ≤ (4/Real.pi)*‖A n‖
  sampled_norms : ∀ ψ ∈ U, ∀ z : ℤ → ℂ, ∀ hz : ∀ n : ℤ, ‖z n-(Real.pi : ℂ)*n‖ ≤ Real.pi/4,
    ‖sourceDiscriminantSampleError hp hp1 ψ z hz‖ ≤ K ∧
    ‖sourceDiscriminantDerivativeSampleError hp hp1 ψ z hz‖ ≤ (4/Real.pi)*K

/-- Lemma 8.4, uniformly over all samples and nearby original complex potentials. -/
theorem sourceLemma8_4 (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∃ K : ℝ, 0 ≤ K ∧ SourceLemma8_4Data hp hp1 U K := by
  obtain ⟨U,ho,hc,hφ,h0,K,hK,hb⟩ :=
    exists_uniform_discriminant_value_derivative_majorants hp hp1 (periodOnePotential φ)
  refine ⟨periodOnePotential ⁻¹' U,ho.preimage (periodOnePotential (p := p)).continuous,
    hc.linear_preimage ((periodOnePotential (p := p)).restrictScalars ℝ).toLinearMap,
    hφ,by simpa only [mem_preimage,map_zero] using h0,K,hK,?_⟩
  have hmajor (ψ : CoeffPair p) (hψ : periodOnePotential ψ ∈ U) := hb _ hψ (periodOnePotential_mem ψ)
  refine ⟨hmajor,?_⟩
  intro ψ hψ z hz
  obtain ⟨A,hA,hbound⟩ := hmajor ψ hψ
  have hv (n : ℤ) : ‖sourceDiscriminantSampleError hp hp1 ψ z hz n‖ ≤ ‖A n‖ :=
    (hbound n (z n) (hz n)).1
  let B : Coeff p := ((4/Real.pi : ℝ) : ℂ) • A
  have hd (n : ℤ) : ‖sourceDiscriminantDerivativeSampleError hp hp1 ψ z hz n‖ ≤ ‖B n‖ := by
    simpa only [sourceDiscriminantDerivativeSampleError_apply,B,lp.coeFn_smul,Pi.smul_apply,norm_smul,
      Complex.norm_real,Real.norm_of_nonneg (by positivity : 0 ≤ 4/Real.pi)] using (hbound n (z n) (hz n)).2
  refine ⟨(lp.norm_mono ((zero_lt_one.trans hp1).ne') hv).trans hA,
    (lp.norm_mono ((zero_lt_one.trans hp1).ne') hd).trans ?_⟩
  change ‖((4/Real.pi : ℝ) : ℂ) • A‖ ≤ (4/Real.pi)*K
  rw [norm_smul,Complex.norm_real,Real.norm_of_nonneg (by positivity : 0 ≤ 4/Real.pi)]
  exact mul_le_mul_of_nonneg_left hA (by positivity)

/-- The first literal asymptotic identity, with the actual ℓp error sequence. -/
theorem sourceLemma8_4_value (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (z : ℤ → ℂ) (hz : ∀ n : ℤ, ‖z n-(Real.pi : ℂ)*n‖ ≤ Real.pi/4) (n : ℤ) :
    canonicalDiscriminant hp (periodOnePotential φ) (z n) =
      2*cos (z n)+sourceDiscriminantSampleError hp hp1 φ z hz n := by
  rw [sourceDiscriminantSampleError_apply]
  ring

/-- The second literal asymptotic identity, with the actual ℓp error sequence. -/
theorem sourceLemma8_4_derivative (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (z : ℤ → ℂ) (hz : ∀ n : ℤ, ‖z n-(Real.pi : ℂ)*n‖ ≤ Real.pi/4) (n : ℤ) :
    deriv (canonicalDiscriminant hp (periodOnePotential φ)) (z n) =
      -2*sin (z n)+sourceDiscriminantDerivativeSampleError hp hp1 φ z hz n := by
  rw [sourceDiscriminantDerivativeSampleError_apply]
  ring

/-- Every admissible sampler has exactly zero value error at the free source. -/
@[simp] theorem sourceDiscriminantSampleError_zero (hp : p ≠ ⊤) (hp1 : 1 < p)
    (z : ℤ → ℂ) (hz : ∀ n : ℤ, ‖z n-(Real.pi : ℂ)*n‖ ≤ Real.pi/4) :
    sourceDiscriminantSampleError hp hp1 (0 : CoeffPair p) z hz = 0 := by
  ext n
  simp only [sourceDiscriminantSampleError_apply,map_zero,canonicalDiscriminant_zero_finite,
    freeDiscriminant,lp.coeFn_zero,Pi.zero_apply,sub_self]

/-- Every admissible sampler has exactly zero derivative error at the free source. -/
@[simp] theorem sourceDiscriminantDerivativeSampleError_zero (hp : p ≠ ⊤) (hp1 : 1 < p)
    (z : ℤ → ℂ) (hz : ∀ n : ℤ, ‖z n-(Real.pi : ℂ)*n‖ ≤ Real.pi/4) :
    sourceDiscriminantDerivativeSampleError hp hp1 (0 : CoeffPair p) z hz = 0 := by
  ext n
  simp only [sourceDiscriminantDerivativeSampleError_apply,map_zero,lp.coeFn_zero,Pi.zero_apply]
  rw [show canonicalDiscriminant hp (0 : PairSpace p) = freeDiscriminant from
    funext (canonicalDiscriminant_zero_finite hp), (hasDerivAt_freeDiscriminant (z n)).deriv]
  ring

end NLS.ZakharovShabat
