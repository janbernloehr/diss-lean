import NLS.FunctionalAnalysis.IntegralCurveUniqueness
import NLS.ZakharovShabat.SourceDirichletSpectralVectorField

/-! # Compatibility of actual indexed spectral curves

The actual field is analytic near every real source, hence locally
Lipschitz there as a real field. Two actual solutions with a common
initial source agree throughout their overlapping time intervals. The
first curve is real; no reality hypothesis is needed on the second.
-/

noncomputable section
open Set NLS.FunctionalAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A real actual indexed spectral curve determines any other actual
solution with the same initial value throughout their overlap. -/
theorem sourceDirichletSpectral_integralCurves_eqOn_overlap
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p) (k : ℤ)
    (γ η : ℝ → CoeffPair p) (a b c d : ℝ)
    (hreal : ∀ t ∈ Ioo a b, IsRealType (CoeffPair.toMax p (γ t)))
    (hγ : ∀ t ∈ Ioo a b, HasDerivAt γ (sourceDirichletSpectralVector hp hp1 h2p k (γ t)) t)
    (hη : ∀ t ∈ Ioo c d, HasDerivAt η (sourceDirichletSpectralVector hp hp1 h2p k (η t)) t)
    (u : ℝ) (hu : u ∈ Ioo a b ∩ Ioo c d) (heq : γ u = η u) :
    EqOn γ η (Ioo a b ∩ Ioo c d) := by
  apply eqOn_integralCurves_of_contDiffAt _ γ η (Ioo a b ∩ Ioo c d)
    (isOpen_Ioo.inter isOpen_Ioo) ((convex_Ioo a b).inter (convex_Ioo c d)).isPreconnected
    (fun t ht => hγ t ht.1) (fun t ht => hη t ht.2) _ u hu heq
  intro t ht
  exact (analyticAt_sourceDirichletSpectralVector_of_realType hp hp1 h2p k
    ⟨γ t,hreal t ht.1⟩).contDiffAt.restrict_scalars ℝ

end NLS.ZakharovShabat
