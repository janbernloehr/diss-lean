import NLS.ZakharovShabat.SourceAntiDiscriminantCentralLp
import NLS.ZakharovShabat.SourceAntiDiscriminantIdentity
import NLS.ZakharovShabat.L2SourceCharacteristics

/-!
# Lemma 9.2: the anti-discriminant and its actual Dirichlet samples

The normalized anti-discriminant is jointly analytic on the original source
space. Its shifted-discriminant-square identity holds at every Dirichlet
root, without a simplicity assumption. On one original neighborhood, the
full actual value and spectral-derivative sample sequences have a common
ℓp norm bound, including all central indices.

One ℓp majorant per nearby source controls the value on every closed half-pi
disk and the derivative on every closed quarter-pi disk. Physical Hilbert
agreement and continuous-extension uniqueness fix the normalization.
-/

noncomputable section
open Set Filter
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual anti-discriminant values at every canonical Dirichlet root. -/
def sourceDirichletAntiDiscriminantSamples (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) : Coeff p :=
  ⟨fun n => sourceAntiDiscriminantCandidate hp hp1 φ (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ n),
    (memℓp_sourceAntiDiscriminant_at_dirichletRoots hp hp1 φ).1⟩

/-- The actual spectral-derivative values at every canonical Dirichlet root. -/
def sourceDirichletAntiDiscriminantDerivativeSamples (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) : Coeff p :=
  ⟨fun n => deriv (sourceAntiDiscriminantCandidate hp hp1 φ) (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ n),
    (memℓp_sourceAntiDiscriminant_at_dirichletRoots hp hp1 φ).2⟩

/-- Evaluation of the actual value sequence. -/
@[simp] theorem sourceDirichletAntiDiscriminantSamples_apply (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (n : ℤ) :
    sourceDirichletAntiDiscriminantSamples hp hp1 φ n =
      sourceAntiDiscriminantCandidate hp hp1 φ (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ n) := rfl

/-- Evaluation of the actual derivative sequence. -/
@[simp] theorem sourceDirichletAntiDiscriminantDerivativeSamples_apply (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (n : ℤ) :
    sourceDirichletAntiDiscriminantDerivativeSamples hp hp1 φ n =
      deriv (sourceAntiDiscriminantCandidate hp hp1 φ) (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ n) := rfl

/-- All three clauses, with one original neighborhood and full sequence-norm bounds. -/
structure SourceLemma9_2Data (hp : p ≠ ⊤) (hp1 : 1 < p) (U : Set (CoeffPair p)) (K : ℝ) : Prop where
  analytic : AnalyticOnNhd ℂ (fun q : ℂ × CoeffPair p => sourceAntiDiscriminantCandidate hp hp1 q.2 q.1) univ
  identity : ∀ ψ : CoeffPair p, ∀ n : ℤ,
    (canonicalDiscriminant hp (periodOnePotential ψ) (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n))^2-4 =
      (sourceDirichletAntiDiscriminantSamples hp hp1 ψ n)^2
  value_norm : ∀ ψ ∈ U, ‖sourceDirichletAntiDiscriminantSamples hp hp1 ψ‖ ≤ K
  derivative_norm : ∀ ψ ∈ U, ‖sourceDirichletAntiDiscriminantDerivativeSamples hp hp1 ψ‖ ≤ K
  disc_majorant : ∀ ψ ∈ U, ∃ A : Coeff p, ‖A‖ ≤ K ∧
    (∀ (n : ℤ) (z : ℂ), ‖z-(Real.pi : ℂ)*n‖ ≤ Real.pi/2 →
      ‖sourceAntiDiscriminantCandidate hp hp1 ψ z‖ ≤ ‖A n‖) ∧
    (∀ (n : ℤ) (z : ℂ), ‖z-(Real.pi : ℂ)*n‖ ≤ Real.pi/4 →
      ‖deriv (sourceAntiDiscriminantCandidate hp hp1 ψ) z‖ ≤ (4/Real.pi)*‖A n‖)

/-- Lemma 9.2 at arbitrary complex original sources, for every finite p > 1. -/
theorem sourceLemma9_2 (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ φ ∈ U ∧ ∃ K : ℝ, 0 ≤ K ∧ SourceLemma9_2Data hp hp1 U K := by
  obtain ⟨U,hU,hφ,K,hK,h⟩ := exists_local_uniform_sampled_sourceAntiDiscriminant_at_dirichletRoots hp hp1 φ
  obtain ⟨V,hV,_,hφV,_,C,_,hdisc⟩ := exists_uniform_sourceAntiDiscriminant_disc_majorants hp hp1 φ
  refine ⟨U ∩ V,hU.inter hV,⟨hφ,hφV⟩,max K C,hK.trans (le_max_left _ _),
    analyticOnNhd_sourceAntiDiscriminantCandidate_joint hp hp1,
    sourceDiscriminant_sq_sub_four_at_canonicalDirichletRoot hp hp1,?_,?_,?_⟩
  · intro ψ hψ
    obtain ⟨a,b,ha,_,hv,_⟩ := h ψ hψ.1
    have he : sourceDirichletAntiDiscriminantSamples hp hp1 ψ = a := by
      ext n
      exact (hv n).symm
    rw [he]
    exact ha.trans (le_max_left _ _)
  · intro ψ hψ
    obtain ⟨a,b,_,hb,_,hd⟩ := h ψ hψ.1
    have he : sourceDirichletAntiDiscriminantDerivativeSamples hp hp1 ψ = b := by
      ext n
      exact (hd n).symm
    rw [he]
    exact hb.trans (le_max_left _ _)
  · intro ψ hψ
    obtain ⟨A,hA,hv,hd⟩ := hdisc ψ hψ.2
    exact ⟨A,hA.trans (le_max_right _ _),hv,hd⟩

/-- Every free anti-discriminant sample vanishes, including central indices. -/
@[simp] theorem sourceDirichletAntiDiscriminantSamples_zero (hp : p ≠ ⊤) (hp1 : 1 < p) :
    sourceDirichletAntiDiscriminantSamples hp hp1 (0 : CoeffPair p) = 0 := by
  ext n
  simp only [sourceDirichletAntiDiscriminantSamples_apply,sourceAntiDiscriminantCandidate_zero,
    lp.coeFn_zero,Pi.zero_apply]

/-- The entire free derivative sample sequence vanishes. -/
@[simp] theorem sourceDirichletAntiDiscriminantDerivativeSamples_zero (hp : p ≠ ⊤) (hp1 : 1 < p) :
    sourceDirichletAntiDiscriminantDerivativeSamples hp hp1 (0 : CoeffPair p) = 0 := by
  have hf : sourceAntiDiscriminantCandidate hp hp1 (0 : CoeffPair p) = fun _ : ℂ => 0 :=
    funext (sourceAntiDiscriminantCandidate_zero hp hp1)
  ext n
  simp only [sourceDirichletAntiDiscriminantDerivativeSamples_apply,hf,deriv_const,
    lp.coeFn_zero,Pi.zero_apply]

/-- Above two, the analytic extension agrees with the physical Hilbert anti-trace. -/
theorem sourceAntiDiscriminant_eq_l2_of_two_le (hp : p ≠ ⊤) (hp1 : 1 < p)
    (h2p : 2 ≤ p) (φ : CoeffPair 2) (z : ℂ) :
    sourceAntiDiscriminantCandidate hp hp1 (CoeffPair.exponentInclusion h2p φ) z =
      l2AntiDiscriminant (sourcePhysicalL2 φ) z :=
  (congrFun (sourceAntiDiscriminantCandidate_exponent (by simp) hp (by norm_num) hp1 h2p φ) z).symm.trans
    (sourceAntiDiscriminantCandidate_eq_l2 φ z)

/-- Below two, it restricts the physical Hilbert anti-trace along the inclusion. -/
theorem sourceAntiDiscriminant_eq_l2_of_le_two (hp : p ≠ ⊤) (hp1 : 1 < p)
    (hp2 : p ≤ 2) (φ : CoeffPair p) (z : ℂ) :
    sourceAntiDiscriminantCandidate hp hp1 φ z =
      l2AntiDiscriminant (sourcePhysicalL2 (CoeffPair.exponentInclusion hp2 φ)) z :=
  (congrFun (sourceAntiDiscriminantCandidate_exponent hp (by simp) hp1 (by norm_num) hp2 φ) z).trans
    (sourceAntiDiscriminantCandidate_eq_l2 _ z)

/-- Finite Fourier agreement determines the jointly continuous extension uniquely. -/
theorem sourceAntiDiscriminant_unique_joint_continuous (hp : p ≠ ⊤) (hp1 : 1 < p)
    (F : ℂ × CoeffPair p → ℂ) (hF : Continuous F)
    (hfinite : ∀ z : ℂ, ∀ a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ),
      F (z,CoeffPair.ofFinsupp (p := p) a) = classicalAntiDiscriminant (finiteSourceCurve a) z) :
    F = fun q => sourceAntiDiscriminantCandidate hp hp1 q.2 q.1 := by
  funext q
  exact congrFun (sourceAntiDiscriminantCandidate_unique_continuous hp hp1 q.1
    (fun φ => F (q.1,φ)) (hF.comp (continuous_const.prodMk continuous_id)) (hfinite q.1)) q.2

/-- The square identity applies to every actual Dirichlet zero, including multiple zeros. -/
theorem sourceLemma9_2_identity (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (z : ℂ) (hz : periodOneBoundaryCharacteristic hp hp1 .dirichlet φ z = 0) :
    (canonicalDiscriminant hp (periodOnePotential φ) z)^2-4 =
      (sourceAntiDiscriminantCandidate hp hp1 φ z)^2 :=
  sourceDiscriminant_sq_sub_four_at_dirichlet_zero hp hp1 φ z hz

end NLS.ZakharovShabat
