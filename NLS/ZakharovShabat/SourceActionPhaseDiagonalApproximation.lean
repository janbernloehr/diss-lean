import NLS.ZakharovShabat.SourceActionPhaseFlow
import NLS.ZakharovShabat.SourceComponentSwapRealTopology
import NLS.ZakharovShabat.SourceSymmetricTruncate

/-! # Diagonal preservation by original Fourier approximation on the open image -/
noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceActionFrequency
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
variable {W₀ B X : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- Preservation on original diagonal finite Fourier sources extends to
every diagonal source, at every admissible time in the actual open image. -/
theorem imageFlow_preserves_diagonal_of_fourier_approx (F : SourceActionFrequency hp hp1)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X s)
    (hfinite : ∀ ψ : realTypeSourceSubmodule p,
      Coeff.HasFiniteSupport ψ.val.fst ∧ Coeff.HasFiniteSupport ψ.val.snd →
      ψ.val.fst = ψ.val.snd → ∀ τ : ℝ, (τ,ψ) ∈ F.imageDomain D →
      (F.imageFlow D ψ τ).val.fst = (F.imageFlow D ψ τ).val.snd)
    (φ : realTypeSourceSubmodule p) (hφ : φ.val.fst = φ.val.snd) (τ : ℝ)
    (hτ : (τ,φ) ∈ F.imageDomain D) :
    (F.imageFlow D φ τ).val.fst = (F.imageFlow D φ τ).val.snd := by
  let φN : ℕ → realTypeSourceSubmodule p := fun N =>
    ⟨sourceSymmetricTruncate N φ.val,sourceSymmetricTruncate_realType N φ.val φ.property⟩
  have hlim : Tendsto φN atTop (𝓝 φ) :=
    tendsto_subtype_rng.mpr (tendsto_sourceSymmetricTruncate hp φ.val)
  have hpair : Tendsto (fun N => (τ,φN N)) atTop (𝓝 (τ,φ)) := tendsto_const_nhds.prodMk_nhds hlim
  have hev : ∀ᶠ N in atTop, (τ,φN N) ∈ F.imageDomain D :=
    hpair.eventually ((F.isOpen_imageDomain D).mem_nhds hτ)
  have hc : ContinuousAt (fun x : ℝ × realTypeSourceSubmodule p => F.imageFlow D x.2 x.1) (τ,φ) :=
    (F.continuousOn_imageFlow D).continuousAt ((F.isOpen_imageDomain D).mem_nhds hτ)
  have hout := hc.tendsto.comp hpair
  simp only [Function.comp_def] at hout
  have hclosed : IsClosed {v : realTypeSourceSubmodule p | realSourceComponentSwap v = v} :=
    isClosed_eq (continuous_realSourceComponentSwap (p := p)) continuous_id
  have hfixed : realSourceComponentSwap (F.imageFlow D φ τ) = F.imageFlow D φ τ := by
    apply hclosed.mem_of_tendsto hout
    filter_upwards [hev] with N hN
    have hdiag : (φN N).val.fst = (φN N).val.snd := by
      change Coeff.truncate (Finset.Icc (-(N:ℤ)) N) φ.val.fst =
        Coeff.truncate (Finset.Icc (-(N:ℤ)) N) φ.val.snd
      rw [hφ]
    exact Subtype.ext ((sourceComponentSwap_eq_self_iff _).mpr
      (hfinite (φN N) (sourceSymmetricTruncate_finite N φ.val) hdiag τ hN))
  exact (sourceComponentSwap_eq_self_iff _).mp (congrArg Subtype.val hfixed)

end NLS.ZakharovShabat.SourceActionFrequency
