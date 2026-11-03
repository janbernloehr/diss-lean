import NLS.Articles.MKdVBelowL2.FourthFrequencySwap
import NLS.Articles.MKdVBelowL2.PhysicalFourthImageFlow
import NLS.ZakharovShabat.SourceActionPhaseSwap
import NLS.ZakharovShabat.SourceActionPhaseExponent
import NLS.ZakharovShabat.SourceActionPhaseDiagonalApproximation

/-! # The actual physical fourth-frequency lift preserves the mKdV diagonal

Hamiltonian covariance gives Hilbert diagonal preservation. Coefficient-preserving
finite Fourier representatives and exact exponent compatibility transfer it to
all finite exponents. Norm approximation on the actual open image domain then
proves preservation for every rough physical mKdV input.
-/
noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped ENNReal
namespace NLS.Articles.MKdVBelowL2
open NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual Hilbert fourth source flow preserves the original equal fields,
by its verified Hamiltonian component-swap covariance. -/
theorem fourthHilbertImageFlow_preserves_diagonal (φ : realTypeSourceSubmodule 2)
    (hφ : φ.val.fst = φ.val.snd) (τ : ℝ) :
    ((fourthSourcePhaseFrequency (p := 2) (by simp) (by norm_num)).imageFlow
      (originalBirkhoffChart (p := 2) (by simp) (by norm_num)).data.complex φ τ).val.fst =
    ((fourthSourcePhaseFrequency (p := 2) (by simp) (by norm_num)).imageFlow
      (originalBirkhoffChart (p := 2) (by simp) (by norm_num)).data.complex φ τ).val.snd :=
  SourceActionFrequency.imageFlow_preserves_diagonal _ _ le_rfl le_rfl
    (fourthSourcePhaseFrequency_componentSwap (by simp) (by norm_num)) φ hφ τ

/-- Every finite Fourier diagonal source has diagonal actual fourth flow at
each admissible time, without a spectral finite-gap assumption. -/
theorem fourthImageFlow_preserves_diagonal_of_finiteSupport
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceSubmodule p)
    (hf : Coeff.HasFiniteSupport φ.val.fst ∧ Coeff.HasFiniteSupport φ.val.snd)
    (hφ : φ.val.fst = φ.val.snd) (τ : ℝ)
    (hτ : (τ,φ) ∈ (fourthSourcePhaseFrequency hp hp1).imageDomain (originalBirkhoffChart hp hp1).data.complex) :
    ((fourthSourcePhaseFrequency hp hp1).imageFlow (originalBirkhoffChart hp hp1).data.complex φ τ).val.fst =
      ((fourthSourcePhaseFrequency hp hp1).imageFlow (originalBirkhoffChart hp hp1).data.complex φ τ).val.snd := by
  let F := fourthSourcePhaseFrequency hp hp1
  let D := (originalBirkhoffChart hp hp1).data.complex
  let G := fourthSourcePhaseFrequency (p := 2) (by simp) (by norm_num)
  let E := (originalBirkhoffChart (p := 2) (by simp) (by norm_num)).data.complex
  obtain ⟨a,ha⟩ := exists_weightedRealSource_of_finiteSupport (q := 2)
    fourthSobolevSpectralWeight φ hf.1 hf.2
  let ψ := originalWeightedRealSource fourthSobolevSpectralWeight a
  have hψ : ψ.val.fst = ψ.val.snd := by
    ext n
    exact (ha n).1.trans ((congrArg (fun c : Coeff p => c n) hφ).trans (ha n).2.symm)
  have hout : (G.imageFlow E ψ τ).val.fst = (G.imageFlow E ψ τ).val.snd :=
    fourthHilbertImageFlow_preserves_diagonal ψ hψ τ
  rcases le_total p 2 with hp2 | h2p
  · have heq : realTypeSourceExponentInclusion hp2 φ = ψ := by
      apply Subtype.ext
      apply (CoeffPair.toMax 2).injective
      apply Prod.ext <;> ext n
      · exact (ha n).1.symm
      · exact (ha n).2.symm
    have he := F.imageFlow_exponent G D E hp2 φ
      (fourthSourcePhaseFrequency_exponent hp hp1 (by simp) (by norm_num) hp2 φ) τ hτ
      (G.mem_imageDomain_of_le_two E le_rfl _ τ)
    rw [heq] at he
    ext n
    exact (congrArg (fun v : realTypeSourceSubmodule 2 => v.val.fst n) he).trans
      ((congrArg (fun c : Coeff 2 => c n) hout).trans
        (congrArg (fun v : realTypeSourceSubmodule 2 => v.val.snd n) he).symm)
  · have heq : realTypeSourceExponentInclusion h2p ψ = φ := by
      apply Subtype.ext
      apply (CoeffPair.toMax p).injective
      apply Prod.ext <;> ext n
      · exact (ha n).1
      · exact (ha n).2
    have ht : (τ,realTypeSourceExponentInclusion h2p ψ) ∈ F.imageDomain D := heq.symm ▸ hτ
    have he := G.imageFlow_exponent F E D h2p ψ
      (fourthSourcePhaseFrequency_exponent (by simp) (by norm_num) hp hp1 h2p ψ) τ
      (G.mem_imageDomain_of_le_two E le_rfl ψ τ) ht
    rw [heq] at he
    ext n
    exact (congrArg (fun v : realTypeSourceSubmodule p => v.val.fst n) he).symm.trans
      ((congrArg (fun c : Coeff 2 => c n) hout).trans
        (congrArg (fun v : realTypeSourceSubmodule p => v.val.snd n) he))

/-- The exact fourth source image lift preserves the original diagonal at
every finite p>1 and every time in its actual open image domain. -/
theorem fourthImageFlow_preserves_diagonal
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceSubmodule p)
    (hφ : φ.val.fst = φ.val.snd) (τ : ℝ)
    (hτ : (τ,φ) ∈ (fourthSourcePhaseFrequency hp hp1).imageDomain (originalBirkhoffChart hp hp1).data.complex) :
    ((fourthSourcePhaseFrequency hp hp1).imageFlow (originalBirkhoffChart hp hp1).data.complex φ τ).val.fst =
      ((fourthSourcePhaseFrequency hp hp1).imageFlow (originalBirkhoffChart hp hp1).data.complex φ τ).val.snd := by
  apply SourceActionFrequency.imageFlow_preserves_diagonal_of_fourier_approx _ _
    (fun ψ hf hψ r hr => fourthImageFlow_preserves_diagonal_of_finiteSupport hp hp1 ψ hf hψ r hr)
    φ hφ τ hτ

/-- The actual physical fourth lift stays in the closed equal-distribution
mKdV subspace at every admissible time, throughout the rough finite-p domain. -/
theorem fourthPhysicalImageFlow_preserves_mKdV
    (hp : p ≠ ⊤) (hp1 : 1 < p) (u : PhysicalMKdVInput p) (τ : ℝ)
    (hτ : (τ,u.val) ∈ fourthPhysicalImageDomain hp hp1) :
    fourthPhysicalImageFlow hp hp1 u.val τ ∈ physicalMKdVSubspace p := by
  rw [mem_physicalMKdVSubspace_iff_source]
  change (physicalRealCoefficientsCL (physicalRealCoefficientsCL.symm _)).val.fst =
    (physicalRealCoefficientsCL (physicalRealCoefficientsCL.symm _)).val.snd
  rw [ContinuousLinearEquiv.apply_symm_apply]
  exact fourthImageFlow_preserves_diagonal hp hp1 (physicalRealCoefficientsCL u.val)
    ((mem_physicalMKdVSubspace_iff_source u.val).mp u.property) τ hτ

end NLS.Articles.MKdVBelowL2
