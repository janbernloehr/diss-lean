import NLS.ZakharovShabat.SourceDirichletSpectralVectorField
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.MeanValue

/-! # Constructed local real isospectral integral curves

The actual indexed spectral vector field is continuously differentiable
on the complete real source Banach space. Picard-Lindelof therefore
constructs a local flow and local real integral curves through every
real source. Embedding these curves back into the source coefficient
space preserves their actual vector-field derivatives. Every actual
discriminant is constant on each curve, by its proved zero derivative.
No trajectory or flow-existence assumption is supplied.
-/

noncomputable section
open Set Metric Complex Filter Topology NLS.Poisson
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Picard-Lindelof constructs a local flow of the actual indexed field
on the complete real-type source space, for all nearby initial points. -/
theorem exists_sourceRealDirichletSpectral_localFlow
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (n : ℤ) (φ : realTypeSourceSubmodule p) :
    ∃ α : realTypeSourceSubmodule p → ℝ → realTypeSourceSubmodule p,
      ∀ᶠ xt in 𝓝 φ ×ˢ 𝓝 (0:ℝ),
        α xt.1 0 = xt.1 ∧
          HasDerivAt (α xt.1) (sourceRealDirichletSpectralVector hp hp1 h2p n (α xt.1 xt.2)) xt.2 :=
  (contDiff_sourceRealDirichletSpectralVector hp hp1 h2p n).contDiffAt.exists_eventually_eq_hasDerivAt 0

/-- Every actual indexed integral curve conserves the discriminant
at every spectral parameter throughout its open time interval. -/
theorem canonicalDiscriminant_eq_on_sourceDirichletSpectral_integralCurve
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p) (n : ℤ)
    (γ : ℝ → CoeffPair p) (a b : ℝ)
    (hγ : ∀ t ∈ Ioo a b, HasDerivAt γ (sourceDirichletSpectralVector hp hp1 h2p n (γ t)) t)
    (u v : ℝ) (hu : u ∈ Ioo a b) (hv : v ∈ Ioo a b) (w : ℂ) :
    canonicalDiscriminant hp (periodOnePotential (γ u)) w =
      canonicalDiscriminant hp (periodOnePotential (γ v)) w := by
  have hd (t : ℝ) (ht : t ∈ Ioo a b) :
      HasDerivAt (fun τ => canonicalDiscriminant hp (periodOnePotential (γ τ)) w) 0 t := by
    have hD := (analyticOnNhd_sourceDiscriminant_section hp hp1 w (γ t) (mem_univ _)).differentiableAt
    have hc := (hD.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t (hγ t ht)
    change HasDerivAt (fun τ => canonicalDiscriminant hp (periodOnePotential (γ τ)) w)
      ((sourceDiscriminantCotangent hp w (γ t)) (sourceDirichletSpectralVector hp hp1 h2p n (γ t))) t at hc
    rw [sourceDirichletSpectralVector_isospectral hp hp1 h2p n (γ t) w] at hc
    exact hc
  exact isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo a b).isPreconnected
    (fun t ht => (hd t ht).differentiableAt.differentiableWithinAt)
    (fun t ht => (hd t ht).deriv) hu hv

/-- Through every real source there is an actual real indexed integral
curve on an open interval, conserving every actual discriminant. -/
theorem exists_sourceDirichletSpectral_isospectral_integralCurve
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (n : ℤ) (φ : realTypeSourceLocus p) :
    ∃ γ : ℝ → CoeffPair p, γ 0 = φ.val ∧
      (∀ t : ℝ, IsRealType (CoeffPair.toMax p (γ t))) ∧
      ∃ ε : ℝ, 0 < ε ∧
        (∀ t ∈ Ioo (-ε) ε, HasDerivAt γ (sourceDirichletSpectralVector hp hp1 h2p n (γ t)) t) ∧
        ∀ t ∈ Ioo (-ε) ε, ∀ w : ℂ,
          canonicalDiscriminant hp (periodOnePotential (γ t)) w =
            canonicalDiscriminant hp (periodOnePotential φ.val) w := by
  let φ₀ : realTypeSourceSubmodule p := ⟨φ.val,φ.property⟩
  have hC : ContDiffAt ℝ 1 (sourceRealDirichletSpectralVector hp hp1 h2p n) φ₀ :=
    (contDiff_sourceRealDirichletSpectralVector hp hp1 h2p n).contDiffAt
  obtain ⟨α,hα,ε,hε,hder⟩ :=
    hC.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ 0
  let γ : ℝ → CoeffPair p := fun t => (α t : CoeffPair p)
  have hγ₀ : γ 0 = φ.val := by
    change (α 0 : CoeffPair p) = φ.val
    rw [hα]
  have hγ (t : ℝ) (ht : t ∈ Ioo (-ε) ε) :
      HasDerivAt γ (sourceDirichletSpectralVector hp hp1 h2p n (γ t)) t := by
    have hc := (realTypeSourceSubmodule p).subtypeL.hasFDerivAt.comp_hasDerivAt t
      (hder t (by simpa only [zero_sub,zero_add] using ht))
    change HasDerivAt γ (sourceRealDirichletSpectralVector hp hp1 h2p n (α t) : CoeffPair p) t at hc
    simpa only [γ,sourceRealDirichletSpectralVector_val] using hc
  refine ⟨γ,hγ₀,fun t => (α t).property,ε,hε,hγ,?_⟩
  intro t ht w
  have h0 : (0:ℝ) ∈ Ioo (-ε) ε := ⟨by linarith, hε⟩
  simpa only [hγ₀] using canonicalDiscriminant_eq_on_sourceDirichletSpectral_integralCurve
    hp hp1 h2p n γ (-ε) ε hγ t 0 ht h0 w

end NLS.ZakharovShabat
