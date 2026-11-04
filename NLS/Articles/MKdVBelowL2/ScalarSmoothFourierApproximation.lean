import NLS.Articles.MKdVBelowL2.PhysicalScalarSmoothFourth
import NLS.ZakharovShabat.SourceWeightedFiniteSupport

/-! # Actual smooth scalar approximants in the original Fourier norm

Finite physical Fourier support supplies native representatives at every
Sobolev order. Fourier uniqueness and physical reality identify a smooth
real periodic representative of the original scalar distribution. Thus the
original scalar cutoffs form genuine smooth approximants, and their actual
smooth PDE lifts converge in the uniform scalar trajectory norm.
-/
noncomputable section
set_option autoImplicit false
open Set Filter Topology Complex NLS.Fourier NLS.Fourier.SmoothPeriodicTest
open scoped ContDiff ENNReal
namespace NLS.Articles.MKdVBelowL2
open NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem isSmoothPhysicalScalarInput_of_finiteSupport (u : PhysicalScalarRealInput p)
    (hf : Coeff.HasFiniteSupport ((PeriodicFourierLebesgue.unweightedCoefficients p) u.val)) :
    IsSmoothPhysicalScalarInput u := by
  let φ := physicalRealCoefficientsCL (physicalScalarPairCLM u)
  have hfst : Coeff.HasFiniteSupport φ.val.fst := hf
  have hsnd : Coeff.HasFiniteSupport φ.val.snd := hf
  have hφ : φ.val.fst = φ.val.snd := by
    ext k
    exact (physicalCoefficients_apply (physicalScalarPairCLM u).val k).1.trans
      (physicalCoefficients_apply (physicalScalarPairCLM u).val k).2.symm
  obtain ⟨a,ha⟩ := exists_weightedRealSource_of_finiteSupport (q := 2)
    (sourceSobolevSpectralWeight (4:ℕ) (Nat.cast_nonneg 4)) φ hfst hsnd
  have hdiag : (originalWeightedRealSource _ a).val.fst = (originalWeightedRealSource _ a).val.snd := by
    ext k
    exact (ha k).1.trans ((congrArg (fun c : Coeff p => c k) hφ).trans (ha k).2.symm)
  let f := fun x => (fourthClassicalPhysicalValue a 0 x).1
  have hcf (k : ℤ) : periodOneCoefficient f k = (originalWeightedRealSource _ a).val.fst k := by
    simpa only [fourthClassicalSourceFlow_zero] using
      (periodOneCoefficient_fourthClassicalPhysicalValue a 0 k).1
  have hcont : Continuous f := ((fourthClassicalPhysicalFlow a 0).1).continuous.comp continuous_quotient_mk'
  have hsmooth : ContDiff ℝ ∞ f := by
    apply contDiff_of_all_nativeSobolev_representations f hcont (fourthClassicalPhysicalValue_periodic a 0).1
    intro n
    obtain ⟨b,hb⟩ := exists_weightedRealSource_of_finiteSupport (q := 2)
      (sourceSobolevSpectralWeight (n+1 : ℕ) (Nat.cast_nonneg (n+1))) φ hfst hsnd
    exact ⟨b,fun k => (hb k).1.trans ((ha k).1.symm.trans (hcf k).symm)⟩
  refine ⟨f,hsmooth,(fourthClassicalPhysicalValue_periodic a 0).1,
    fun x => fourthClassicalPhysicalValue_im_eq_zero a hdiag 0 x,fun k => ?_⟩
  exact (physicalCoefficients_apply (physicalScalarPairCLM u).val k).1.symm.trans
    ((ha k).1.symm.trans (hcf k).symm)

/-- The original symmetric scalar Fourier cutoffs are actual smooth real
periodic distributions; no spectral finite-gap assertion is used. -/
theorem isSmoothPhysicalScalarInput_truncate (N : ℕ) (u : PhysicalScalarRealInput p) :
    IsSmoothPhysicalScalarInput (physicalScalarTruncate N u) :=
  isSmoothPhysicalScalarInput_of_finiteSupport _ (physicalScalarTruncate_finite N u)

theorem dense_smoothPhysicalScalarInput (hp : p ≠ ⊤) :
    Dense {u : PhysicalScalarRealInput p | IsSmoothPhysicalScalarInput u} := by
  intro u
  apply mem_closure_of_tendsto (tendsto_physicalScalarTruncate hp u)
  exact Eventually.of_forall (fun N => isSmoothPhysicalScalarInput_truncate N u)

/-- Every original scalar datum has an actual smooth norm-convergent
sequence of initial data. -/
theorem exists_smoothPhysicalScalar_sequence (hp : p ≠ ⊤) (u : PhysicalScalarRealInput p) :
    ∃ v : ℕ → PhysicalScalarRealInput p, (∀ N, IsSmoothPhysicalScalarInput (v N)) ∧
      Tendsto v atTop (𝓝 u) :=
  ⟨fun N => physicalScalarTruncate N u,fun N => isSmoothPhysicalScalarInput_truncate N u,
    tendsto_physicalScalarTruncate hp u⟩

/-- Every convergent family of smooth scalar inputs has globally admissible
smooth physical lifts and uniformly convergent actual scalar trajectories
on each common admissible compact interval of the limiting datum. -/
theorem tendstoUniformly_fourthScalarImageFlow_of_smooth
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : 2 ≤ p) (T : ℝ)
    {ι : Type*} {l : Filter ι} (u : ι → PhysicalScalarRealInput p) (v : PhysicalScalarRealInput p)
    (hs : ∀ i, IsSmoothPhysicalScalarInput (u i))
    (hv : v ∈ fourthScalarTrajectoryDomain hp hp1 T) (hu : Tendsto u l (𝓝 v)) :
    TendstoUniformly (fun i (time : Icc (-T) T) => fourthScalarImageFlow hp hp1 (u i) time.val)
      (fun time => fourthScalarImageFlow hp hp1 v time.val) l ∧
      ∀ i, ∀ time : ℝ, (time,u i) ∈ fourthScalarImageDomain hp hp1 :=
  ⟨tendstoUniformly_fourthScalarImageFlow hp hp1 T u v hv hu,
    fun i time => fourthScalarImageDomain_of_smooth hp hp1 h2p (u i) (hs i) time⟩

/-- A curve with the article's all-smooth-sequences limit property for the
constructed smooth physical flow is uniquely the actual scalar lift. Genuine
smooth approximation sequences exist at every original finite-p datum. -/
theorem fourthScalarImageFlow_unique_smooth_approximation
    (hp : p ≠ ⊤) (hp1 : 1 < p) (T : ℝ) (u : PhysicalScalarRealInput p)
    (hu : u ∈ fourthScalarTrajectoryDomain hp hp1 T)
    (γ : Icc (-T) T → PhysicalScalarRealInput p)
    (hγ : ∀ v : ℕ → PhysicalScalarRealInput p, (∀ N, IsSmoothPhysicalScalarInput (v N)) →
      Tendsto v atTop (𝓝 u) → ∀ time : Icc (-T) T,
        Tendsto (fun N => fourthScalarImageFlow hp hp1 (v N) time.val) atTop (𝓝 (γ time))) :
    γ = fun time => fourthScalarImageFlow hp hp1 u time.val := by
  obtain ⟨v,hv,hlim⟩ := exists_smoothPhysicalScalar_sequence hp u
  exact fourthScalarImageFlow_limit_unique hp hp1 T v u hu hlim γ (hγ v hv hlim)

end NLS.Articles.MKdVBelowL2
