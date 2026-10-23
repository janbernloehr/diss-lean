import NLS.FunctionalAnalysis.FiniteCircleProductManifold
import NLS.ZakharovShabat.SourceHilbertIsospectralTorus

/-! # The manifold dimension of actual finite-gap Hilbert isospectral sets

The established finite-torus homeomorphism transports its standard charts
to the actual isospectral set, with its inherited Hilbert topology. Its
Euclidean model has exactly one real dimension per actual open gap.
This is a topological manifold statement; no compatibility of these charts
with a differentiable structure on the ambient source space is asserted.
-/
noncomputable section
open Set Manifold
namespace NLS.ZakharovShabat

/-- An atlas on the actual finite-gap isospectral set with one real coordinate per open gap. -/
@[instance_reducible]
def sourceHilbertFiniteGapChartedSpace (φ : realTypeSourceSubmodule 2)
    (hφ : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) :
    ChartedSpace (EuclideanSpace ℝ (Fin (Nat.card (sourceHilbertOpenGapIndex φ))))
      (sourceIsospectralSet ENNReal.ofNat_ne_top φ) := by
  letI := FunctionalAnalysis.finiteCircleProductChartedSpace
    (Nat.card (sourceHilbertOpenGapIndex φ))
  exact (sourceHilbertIsospectralSet_homeomorphic_finiteTorus φ hφ).some.symm.chartedSpace

/-- Every actual finite-gap Hilbert isospectral set is a topological manifold without boundary. -/
theorem sourceHilbertFiniteGap_isManifold (φ : realTypeSourceSubmodule 2)
    (hφ : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) :
    letI := sourceHilbertFiniteGapChartedSpace φ hφ
    IsManifold (𝓡 (Nat.card (sourceHilbertOpenGapIndex φ))) 0
      (sourceIsospectralSet ENNReal.ofNat_ne_top φ) := by
  let := sourceHilbertFiniteGapChartedSpace φ hφ
  infer_instance

/-- The original topology on a finite-gap isospectral set is Hausdorff. -/
theorem sourceHilbertFiniteGap_t2Space (φ : realTypeSourceSubmodule 2)
    (hφ : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) :
    T2Space (sourceIsospectralSet ENNReal.ofNat_ne_top φ) :=
  (sourceHilbertIsospectralSet_homeomorphic_finiteTorus φ hφ).some.symm.t2Space

/-- The original topology on a finite-gap isospectral set is second countable. -/
theorem sourceHilbertFiniteGap_secondCountableTopology (φ : realTypeSourceSubmodule 2)
    (hφ : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) :
    SecondCountableTopology (sourceIsospectralSet ENNReal.ofNat_ne_top φ) :=
  (sourceHilbertIsospectralSet_homeomorphic_finiteTorus φ hφ).some.secondCountableTopology

/-- The real dimension of the manifold model equals the number of actual open gaps. -/
theorem sourceHilbertFiniteGap_model_finrank (φ : realTypeSourceSubmodule 2) :
    Module.finrank ℝ (EuclideanSpace ℝ (Fin (Nat.card (sourceHilbertOpenGapIndex φ)))) =
      Nat.card (sourceHilbertOpenGapIndex φ) :=
  FunctionalAnalysis.finiteCircleProduct_model_finrank _

end NLS.ZakharovShabat
