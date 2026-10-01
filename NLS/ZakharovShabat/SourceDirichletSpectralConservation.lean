import NLS.ZakharovShabat.SourceDirichletSpectralLocalFlow
import NLS.ZakharovShabat.SourcePeriodicIsospectral

/-! # Spectral conservation along actual indexed integral curves

Every periodic midpoint, squared gap, oriented real gap and endpoint is
constant throughout an actual real indexed spectral integral curve.
Every other Dirichlet root and terminal anti-discriminant is constant
as well. The selected terminal solves the two-dimensional sheet ODE
of the fixed initial discriminant, including at periodic endpoints.
These are conservation laws on the whole supplied time interval, with
no nonzero-gap or chart assumptions.
-/

noncomputable section
open Set Complex Filter Topology NLS.Poisson
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

private theorem functional_eq_on_indexedCurve
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p) (k : ℤ)
    (γ : ℝ → CoeffPair p) (a b : ℝ)
    (hγ : ∀ t ∈ Ioo a b, HasDerivAt γ (sourceDirichletSpectralVector hp hp1 h2p k (γ t)) t)
    (F : CoeffPair p → ℂ)
    (hF : ∀ t ∈ Ioo a b, DifferentiableAt ℂ F (γ t))
    (hzero : ∀ t ∈ Ioo a b,
      (fderiv ℂ F (γ t)) (sourceDirichletSpectralVector hp hp1 h2p k (γ t)) = 0)
    (u v : ℝ) (hu : u ∈ Ioo a b) (hv : v ∈ Ioo a b) : F (γ u) = F (γ v) := by
  have hd (t : ℝ) (ht : t ∈ Ioo a b) : HasDerivAt (fun τ => F (γ τ)) 0 t := by
    have hc := ((hF t ht).hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t (hγ t ht)
    change HasDerivAt (fun τ => F (γ τ))
      ((fderiv ℂ F (γ t)) (sourceDirichletSpectralVector hp hp1 h2p k (γ t))) t at hc
    rw [hzero t ht] at hc
    exact hc
  exact isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo a b).isPreconnected
    (fun t ht => (hd t ht).differentiableAt.differentiableWithinAt)
    (fun t ht => (hd t ht).deriv) hu hv

/-- Both symmetric periodic coordinates are conserved on the whole
real integral-curve interval, including collapsed gaps. -/
theorem canonicalPeriodicMidpoint_squaredGap_eq_on_sourceDirichletSpectral_integralCurve
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p) (k n : ℤ)
    (γ : ℝ → CoeffPair p) (a b : ℝ)
    (hreal : ∀ t ∈ Ioo a b, IsRealType (CoeffPair.toMax p (γ t)))
    (hγ : ∀ t ∈ Ioo a b, HasDerivAt γ (sourceDirichletSpectralVector hp hp1 h2p k (γ t)) t)
    (u v : ℝ) (hu : u ∈ Ioo a b) (hv : v ∈ Ioo a b) :
    canonicalPeriodicMidpoint hp hp1 (periodOnePotential (γ u)) (periodOnePotential_mem (γ u)) n =
      canonicalPeriodicMidpoint hp hp1 (periodOnePotential (γ v)) (periodOnePotential_mem (γ v)) n ∧
    (canonicalPeriodicGap hp hp1 (periodOnePotential (γ u)) (periodOnePotential_mem (γ u)) n)^2 =
      (canonicalPeriodicGap hp hp1 (periodOnePotential (γ v)) (periodOnePotential_mem (γ v)) n)^2 := by
  obtain ⟨W,_,_,hWreal,hA⟩ := exists_global_source_analytic_midpoint_squaredGap hp hp1
  have hz (t : ℝ) (ht : t ∈ Ioo a b) :=
    fderiv_canonicalPeriodicMidpoint_squaredGap_isospectral_eq_zero hp hp1 (γ t) (hreal t ht)
      _ (sourceDirichletSpectralVector_isospectral hp hp1 h2p k (γ t)) n
  constructor
  · exact functional_eq_on_indexedCurve hp hp1 h2p k γ a b hγ _
      (fun t ht => (hA (γ t) (hWreal (hreal t ht)) n).1.differentiableAt)
      (fun t ht => (hz t ht).1) u v hu hv
  · exact functional_eq_on_indexedCurve hp hp1 h2p k γ a b hγ _
      (fun t ht => (hA (γ t) (hWreal (hreal t ht)) n).2.differentiableAt)
      (fun t ht => (hz t ht).2) u v hu hv

/-- Reality and canonical endpoint ordering remove the square-root
sign ambiguity: the oriented gap itself is conserved. -/
theorem canonicalPeriodicGap_eq_on_sourceDirichletSpectral_integralCurve
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p) (k n : ℤ)
    (γ : ℝ → CoeffPair p) (a b : ℝ)
    (hreal : ∀ t ∈ Ioo a b, IsRealType (CoeffPair.toMax p (γ t)))
    (hγ : ∀ t ∈ Ioo a b, HasDerivAt γ (sourceDirichletSpectralVector hp hp1 h2p k (γ t)) t)
    (u v : ℝ) (hu : u ∈ Ioo a b) (hv : v ∈ Ioo a b) :
    canonicalPeriodicGap hp hp1 (periodOnePotential (γ u)) (periodOnePotential_mem (γ u)) n =
      canonicalPeriodicGap hp hp1 (periodOnePotential (γ v)) (periodOnePotential_mem (γ v)) n := by
  have hsq := (canonicalPeriodicMidpoint_squaredGap_eq_on_sourceDirichletSpectral_integralCurve
    hp hp1 h2p k n γ a b hreal hγ u v hu hv).2
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with he | he
  · exact he
  · have him (t : ℝ) (ht : t ∈ Ioo a b) :
        (canonicalPeriodicGap hp hp1 (periodOnePotential (γ t)) (periodOnePotential_mem (γ t)) n).im = 0 := by
      obtain ⟨hl,hr⟩ := canonicalPeriodicEndpoints_im_eq_zero_of_realType hp hp1 _
        (periodOnePotential_mem (γ t)) (isRealType_periodOnePotential (γ t) (hreal t ht)) n
      simp only [canonicalPeriodicGap,sub_im,hl,hr,sub_self]
    have hnonneg (t : ℝ) :
        0 ≤ (canonicalPeriodicGap hp hp1 (periodOnePotential (γ t)) (periodOnePotential_mem (γ t)) n).re := by
      exact sub_nonneg.mpr (NLS.ComplexAnalysis.re_le_of_complexLexLE
        ((canonicalPeriodicEndpoints_spec hp hp1 (periodOnePotential (γ t)) (periodOnePotential_mem (γ t))).2.1 n))
    apply Complex.ext
    · have hre := congrArg Complex.re he
      simp only [neg_re] at hre
      linarith [hnonneg u,hnonneg v]
    · rw [him u hu,him v hv]

/-- Every canonical periodic endpoint is fixed, so the actual indexed
spectral curve keeps its original compact real periodic segment. -/
theorem canonicalPeriodicEndpoints_eq_on_sourceDirichletSpectral_integralCurve
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p) (k n : ℤ)
    (γ : ℝ → CoeffPair p) (a b : ℝ)
    (hreal : ∀ t ∈ Ioo a b, IsRealType (CoeffPair.toMax p (γ t)))
    (hγ : ∀ t ∈ Ioo a b, HasDerivAt γ (sourceDirichletSpectralVector hp hp1 h2p k (γ t)) t)
    (u v : ℝ) (hu : u ∈ Ioo a b) (hv : v ∈ Ioo a b) :
    canonicalPeriodicLeft hp hp1 (periodOnePotential (γ u)) (periodOnePotential_mem (γ u)) n =
      canonicalPeriodicLeft hp hp1 (periodOnePotential (γ v)) (periodOnePotential_mem (γ v)) n ∧
    canonicalPeriodicRight hp hp1 (periodOnePotential (γ u)) (periodOnePotential_mem (γ u)) n =
      canonicalPeriodicRight hp hp1 (periodOnePotential (γ v)) (periodOnePotential_mem (γ v)) n := by
  have hM := (canonicalPeriodicMidpoint_squaredGap_eq_on_sourceDirichletSpectral_integralCurve
    hp hp1 h2p k n γ a b hreal hγ u v hu hv).1
  have hG := canonicalPeriodicGap_eq_on_sourceDirichletSpectral_integralCurve
    hp hp1 h2p k n γ a b hreal hγ u v hu hv
  simp only [canonicalPeriodicMidpoint] at hM
  simp only [canonicalPeriodicGap] at hG
  constructor
  · linear_combination hM-hG/2
  · linear_combination hM+hG/2

/-- All other Dirichlet roots and their full terminal sheet data are
fixed throughout the actual real indexed flow interval. -/
theorem other_dirichletTerminals_eq_on_sourceDirichletSpectral_integralCurve
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p) (k m : ℤ) (hmk : m ≠ k)
    (γ : ℝ → CoeffPair p) (a b : ℝ)
    (hreal : ∀ t ∈ Ioo a b, IsRealType (CoeffPair.toMax p (γ t)))
    (hγ : ∀ t ∈ Ioo a b, HasDerivAt γ (sourceDirichletSpectralVector hp hp1 h2p k (γ t)) t)
    (u v : ℝ) (hu : u ∈ Ioo a b) (hv : v ∈ Ioo a b) :
    canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet (γ u) m =
      canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet (γ v) m ∧
    sourceBoundaryTerminalAntiDiscriminant hp hp1 .dirichlet m (γ u) =
      sourceBoundaryTerminalAntiDiscriminant hp hp1 .dirichlet m (γ v) := by
  constructor
  · exact functional_eq_on_indexedCurve hp hp1 h2p k γ a b hγ _
      (fun t ht => (analyticAt_canonicalPeriodOneBoundaryRoots_of_realType hp hp1 .dirichlet (γ t) (hreal t ht) m).differentiableAt)
      (fun t ht => by simpa only [if_neg hmk] using
        fderiv_dirichletRoot_sourceDirichletSpectralVector hp hp1 h2p k m ⟨γ t,hreal t ht⟩)
      u v hu hv
  · exact functional_eq_on_indexedCurve hp hp1 h2p k γ a b hγ _
      (fun t ht => (analyticAt_sourceBoundaryTerminalAntiDiscriminant_of_realType hp hp1 .dirichlet m (γ t) (hreal t ht)).differentiableAt)
      (fun t ht => by simpa only [if_neg hmk] using
        fderiv_dirichletTerminalAnti_sourceDirichletSpectralVector hp hp1 h2p k m ⟨γ t,hreal t ht⟩)
      u v hu hv

/-- The selected actual terminal solves the fixed initial spectral-curve
ODE. The frozen discriminant and its spectral derivative are taken at
any reference time in the interval; no endpoint is excluded. -/
theorem hasDerivAt_dirichletTerminal_fixedDiscriminant_on_sourceDirichletSpectral_integralCurve
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p) (k : ℤ)
    (γ : ℝ → CoeffPair p) (a b : ℝ)
    (hreal : ∀ t ∈ Ioo a b, IsRealType (CoeffPair.toMax p (γ t)))
    (hγ : ∀ t ∈ Ioo a b, HasDerivAt γ (sourceDirichletSpectralVector hp hp1 h2p k (γ t)) t)
    (u t : ℝ) (hu : u ∈ Ioo a b) (ht : t ∈ Ioo a b) :
    let μ := fun τ => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet (γ τ) k;
    let S := fun τ => sourceBoundaryTerminalAntiDiscriminant hp hp1 .dirichlet k (γ τ);
    let Δ := canonicalDiscriminant hp (periodOnePotential (γ u));
    HasDerivAt μ (-S t/2) t ∧ HasDerivAt S (-Δ (μ t)*deriv Δ (μ t)/2) t := by
  dsimp only
  have hD : canonicalDiscriminant hp (periodOnePotential (γ t)) =
      canonicalDiscriminant hp (periodOnePotential (γ u)) := by
    funext w
    exact canonicalDiscriminant_eq_on_sourceDirichletSpectral_integralCurve hp hp1 h2p k γ a b hγ t u ht hu w
  constructor
  · have hc := ((analyticAt_canonicalPeriodOneBoundaryRoots_of_realType hp hp1 .dirichlet
      (γ t) (hreal t ht) k).differentiableAt.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t (hγ t ht)
    change HasDerivAt (fun τ => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet (γ τ) k)
      ((fderiv ℂ (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ k) (γ t))
        (sourceDirichletSpectralVector hp hp1 h2p k (γ t))) t at hc
    simpa using hc.congr_deriv (fderiv_dirichletRoot_sourceDirichletSpectralVector hp hp1 h2p k k ⟨γ t,hreal t ht⟩)
  · have hc := ((analyticAt_sourceBoundaryTerminalAntiDiscriminant_of_realType hp hp1 .dirichlet k
      (γ t) (hreal t ht)).differentiableAt.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t (hγ t ht)
    change HasDerivAt (fun τ => sourceBoundaryTerminalAntiDiscriminant hp hp1 .dirichlet k (γ τ))
      ((fderiv ℂ (sourceBoundaryTerminalAntiDiscriminant hp hp1 .dirichlet k) (γ t))
        (sourceDirichletSpectralVector hp hp1 h2p k (γ t))) t at hc
    have he := fderiv_dirichletTerminalAnti_sourceDirichletSpectralVector hp hp1 h2p k k ⟨γ t,hreal t ht⟩
    simp only [ite_true] at he
    rw [hD] at he
    exact hc.congr_deriv he

end NLS.ZakharovShabat
