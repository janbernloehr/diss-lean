import NLS.ZakharovShabat.SourceHilbertMassDiscriminant
import NLS.ZakharovShabat.SourceDirichletSpectralLocalFlow

/-! # Conservation of the original source norm along actual Hilbert flows

Mass/discriminant commutation fixes the actual holomorphic source mass
along every complex indexed Hilbert integral curve. On real source
curves the exact mass/norm identity conserves the original coefficient
pair norm, including a zero initial source. The constructed local real
isospectral curves therefore remain on the initial source norm sphere.
Global continuation still needs uniform source vector-field estimates.
-/

noncomputable section
open Set Metric Complex Filter Topology NLS.Poisson
open scoped ENNReal
namespace NLS.ZakharovShabat
local instance : Fact ((1:ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

/-- Every actual indexed Hilbert spectral direction fixes mass,
including at arbitrary complex sources and periodic terminals. -/
theorem fderiv_sourceHilbertMass_sourceDirichletSpectralVector_eq_zero
    (k : ℤ) (φ : CoeffPair 2) :
    (fderiv ℂ sourceHilbertMass φ)
      (sourceDirichletSpectralVector (by simp) (by norm_num) (by norm_num) k φ) = 0 := by
  rw [sourceDirichletSpectralVector,apply_sourceHamiltonianDirection]
  exact sourceBivector_mass_discriminant_eq_zero φ _

/-- The actual mass is conserved along the entire interval of every
complex indexed Hilbert integral curve. -/
theorem sourceHilbertMass_eq_on_sourceDirichletSpectral_integralCurve
    (k : ℤ) (γ : ℝ → CoeffPair 2) (a b : ℝ)
    (hγ : ∀ t ∈ Ioo a b, HasDerivAt γ
      (sourceDirichletSpectralVector (by simp) (by norm_num) (by norm_num) k (γ t)) t)
    (u v : ℝ) (hu : u ∈ Ioo a b) (hv : v ∈ Ioo a b) :
    sourceHilbertMass (γ u) = sourceHilbertMass (γ v) := by
  have hd (t : ℝ) (ht : t ∈ Ioo a b) : HasDerivAt (fun τ => sourceHilbertMass (γ τ)) 0 t := by
    have hc := ((analyticOnNhd_sourceHilbertMass (γ t) (mem_univ _)).differentiableAt.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t (hγ t ht)
    change HasDerivAt (fun τ => sourceHilbertMass (γ τ))
      ((fderiv ℂ sourceHilbertMass (γ t))
        (sourceDirichletSpectralVector (by simp) (by norm_num) (by norm_num) k (γ t))) t at hc
    rw [fderiv_sourceHilbertMass_sourceDirichletSpectralVector_eq_zero] at hc
    exact hc
  exact isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo a b).isPreconnected
    (fun t ht => (hd t ht).differentiableAt.differentiableWithinAt)
    (fun t ht => (hd t ht).deriv) hu hv

/-- The original coefficient-space norm is conserved throughout every
real indexed Hilbert curve. No positive-norm assumption is needed. -/
theorem norm_eq_on_sourceDirichletSpectral_integralCurve
    (k : ℤ) (γ : ℝ → CoeffPair 2) (a b : ℝ)
    (hreal : ∀ t ∈ Ioo a b, IsRealType (CoeffPair.toMax 2 (γ t)))
    (hγ : ∀ t ∈ Ioo a b, HasDerivAt γ
      (sourceDirichletSpectralVector (by simp) (by norm_num) (by norm_num) k (γ t)) t)
    (u v : ℝ) (hu : u ∈ Ioo a b) (hv : v ∈ Ioo a b) : ‖γ u‖ = ‖γ v‖ := by
  have he := sourceHilbertMass_eq_on_sourceDirichletSpectral_integralCurve k γ a b hγ u v hu hv
  rw [sourceHilbertMass_eq_half_norm_sq_of_realType _ (hreal u hu),
    sourceHilbertMass_eq_half_norm_sq_of_realType _ (hreal v hv)] at he
  have hre := congrArg Complex.re he
  simp only [Complex.ofReal_re] at hre
  nlinarith [norm_nonneg (γ u),norm_nonneg (γ v)]

/-- Picard-Lindelof constructs an actual local real isospectral Hilbert
curve remaining on the original source norm sphere throughout its ODE
interval. The norm bound is proved, rather than supplied. -/
theorem exists_sourceDirichletSpectral_norm_conserved_integralCurve
    (k : ℤ) (φ : realTypeSourceLocus 2) :
    ∃ γ : ℝ → CoeffPair 2, γ 0 = φ.val ∧
      (∀ t : ℝ, IsRealType (CoeffPair.toMax 2 (γ t))) ∧
      ∃ ε : ℝ, 0 < ε ∧
        (∀ t ∈ Ioo (-ε) ε, HasDerivAt γ
          (sourceDirichletSpectralVector (by simp) (by norm_num) (by norm_num) k (γ t)) t) ∧
        (∀ t ∈ Ioo (-ε) ε, ‖γ t‖ = ‖φ.val‖) ∧
        ∀ t ∈ Ioo (-ε) ε, ∀ w : ℂ,
          canonicalDiscriminant (by simp) (periodOnePotential (γ t)) w =
            canonicalDiscriminant (by simp) (periodOnePotential φ.val) w := by
  obtain ⟨γ,hγ₀,hreal,ε,hε,hder,hD⟩ :=
    exists_sourceDirichletSpectral_isospectral_integralCurve (by simp) (by norm_num) (by norm_num) k φ
  refine ⟨γ,hγ₀,hreal,ε,hε,hder,?_,hD⟩
  intro t ht
  have h0 : (0:ℝ) ∈ Ioo (-ε) ε := ⟨by linarith,hε⟩
  simpa only [hγ₀] using norm_eq_on_sourceDirichletSpectral_integralCurve
    k γ (-ε) ε (fun t _ => hreal t) hder t 0 ht h0

end NLS.ZakharovShabat
