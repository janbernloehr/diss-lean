import NLS.ZakharovShabat.SourceDirichletSpectralConservation

/-! # Actual local isospectral transport of the angle/angle bracket

The proved zero source derivative gives constancy along actual indexed
spectral integral curves while the two angle gaps stay open. The local
ODE theorem constructs such a real curve through every real open-gap
source. Conservation of the actual periodic gaps keeps the whole ODE
interval in the actual common angle domain. The resulting curve preserves
both every discriminant and the full actual angle/angle bracket, with
no supplied trajectory, chart or stationarity premise. Global source
continuation remains separate.
-/

noncomputable section
open Set Metric Complex Filter Topology NLS.Poisson
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceAngularThetaCommonDomainData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
  {s : (j : ℤ) → CoeffPair p → DeletedCoeff p j}

/-- Actual indexed integral curves transport the actual angle/angle
bracket unchanged throughout any real open-gap time interval. -/
theorem thetaTheta_eq_on_sourceDirichletSpectral_integralCurve
    (D : SourceAngularThetaCommonDomainData hp hp1 W₀ B W s)
    (h2p : (2 : ℝ≥0∞) ≤ p) (k n m : ℤ) (γ : ℝ → CoeffPair p) (a b : ℝ)
    (hreal : ∀ t ∈ Ioo a b, IsRealType (CoeffPair.toMax p (γ t)))
    (hγ : ∀ t ∈ Ioo a b, HasDerivAt γ (sourceDirichletSpectralVector hp hp1 h2p k (γ t)) t)
    (hn : ∀ t ∈ Ioo a b,
      canonicalPeriodicGap hp hp1 (periodOnePotential (γ t)) (periodOnePotential_mem (γ t)) n ≠ 0)
    (hm : ∀ t ∈ Ioo a b,
      canonicalPeriodicGap hp hp1 (periodOnePotential (γ t)) (periodOnePotential_mem (γ t)) m ≠ 0)
    (u v : ℝ) (hu : u ∈ Ioo a b) (hv : v ∈ Ioo a b) :
    sourceAngularThetaThetaBracket hp hp1 h2p n m s (γ u) =
      sourceAngularThetaThetaBracket hp hp1 h2p n m s (γ v) := by
  let F := sourceAngularThetaThetaBracket hp hp1 h2p n m s
  have hd (t : ℝ) (ht : t ∈ Ioo a b) : HasDerivAt (fun τ => F (γ τ)) 0 t := by
    have hφ := D.real_subset (hreal t ht)
    have hF := (D.analyticOnNhd_thetaThetaBracket h2p n m (γ t)
      ⟨⟨hφ,hn t ht⟩,⟨hφ,hm t ht⟩⟩).differentiableAt
    have hc := (hF.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t (hγ t ht)
    change HasDerivAt (fun τ => F (γ τ))
      ((fderiv ℂ F (γ t)) (sourceDirichletSpectralVector hp hp1 h2p k (γ t))) t at hc
    rw [D.fderiv_thetaTheta_sourceDirichletSpectralVector_eq_zero h2p k n m
      ⟨γ t,hreal t ht⟩ (hn t ht) (hm t ht)] at hc
    exact hc
  exact isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo a b).isPreconnected
    (fun t ht => (hd t ht).differentiableAt.differentiableWithinAt)
    (fun t ht => (hd t ht).deriv) hu hv

/-- Open gaps at one reference time stay open on the whole real
indexed integral-curve interval, so the actual angle/angle bracket is
transported with no additional gap-preservation assumption. -/
theorem thetaTheta_eq_on_sourceDirichletSpectral_integralCurve_of_initial_open
    (D : SourceAngularThetaCommonDomainData hp hp1 W₀ B W s)
    (h2p : (2 : ℝ≥0∞) ≤ p) (k n m : ℤ) (γ : ℝ → CoeffPair p) (a b : ℝ)
    (hreal : ∀ t ∈ Ioo a b, IsRealType (CoeffPair.toMax p (γ t)))
    (hγ : ∀ t ∈ Ioo a b, HasDerivAt γ (sourceDirichletSpectralVector hp hp1 h2p k (γ t)) t)
    (u v : ℝ) (hu : u ∈ Ioo a b) (hv : v ∈ Ioo a b)
    (hn : canonicalPeriodicGap hp hp1 (periodOnePotential (γ u)) (periodOnePotential_mem (γ u)) n ≠ 0)
    (hm : canonicalPeriodicGap hp hp1 (periodOnePotential (γ u)) (periodOnePotential_mem (γ u)) m ≠ 0) :
    sourceAngularThetaThetaBracket hp hp1 h2p n m s (γ u) =
      sourceAngularThetaThetaBracket hp hp1 h2p n m s (γ v) := by
  apply D.thetaTheta_eq_on_sourceDirichletSpectral_integralCurve h2p k n m γ a b hreal hγ _ _ u v hu hv
  · intro t ht
    rw [canonicalPeriodicGap_eq_on_sourceDirichletSpectral_integralCurve hp hp1 h2p k n γ a b hreal hγ t u ht hu]
    exact hn
  · intro t ht
    rw [canonicalPeriodicGap_eq_on_sourceDirichletSpectral_integralCurve hp hp1 h2p k m γ a b hreal hγ t u ht hu]
    exact hm

/-- A constructed local real indexed spectral curve through every
actual open-gap source preserves every discriminant and the full
angle/angle bracket throughout its original ODE interval. The open
gaps are conserved, so no further shrinking of that interval is needed. -/
theorem exists_sourceDirichletSpectral_integralCurve_thetaTheta_stationary
    (D : SourceAngularThetaCommonDomainData hp hp1 W₀ B W s)
    (h2p : (2 : ℝ≥0∞) ≤ p) (k n m : ℤ) (φ : realTypeSourceLocus p)
    (hn : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0)
    (hm : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) m ≠ 0) :
    ∃ γ : ℝ → CoeffPair p, γ 0 = φ.val ∧
      (∀ t : ℝ, IsRealType (CoeffPair.toMax p (γ t))) ∧
      ∃ ε : ℝ, 0 < ε ∧
        (∀ t ∈ Ioo (-ε) ε, HasDerivAt γ (sourceDirichletSpectralVector hp hp1 h2p k (γ t)) t) ∧
        (∀ t ∈ Ioo (-ε) ε,
          canonicalPeriodicGap hp hp1 (periodOnePotential (γ t)) (periodOnePotential_mem (γ t)) n ≠ 0 ∧
          canonicalPeriodicGap hp hp1 (periodOnePotential (γ t)) (periodOnePotential_mem (γ t)) m ≠ 0) ∧
        (∀ t ∈ Ioo (-ε) ε, ∀ w : ℂ,
          canonicalDiscriminant hp (periodOnePotential (γ t)) w =
            canonicalDiscriminant hp (periodOnePotential φ.val) w) ∧
        ∀ t ∈ Ioo (-ε) ε,
          sourceAngularThetaThetaBracket hp hp1 h2p n m s (γ t) =
            sourceAngularThetaThetaBracket hp hp1 h2p n m s φ.val := by
  obtain ⟨γ,hγ₀,hreal,ε,hε,hder,hDis⟩ :=
    exists_sourceDirichletSpectral_isospectral_integralCurve hp hp1 h2p k φ
  have h0 : (0:ℝ) ∈ Ioo (-ε) ε := ⟨by linarith,hε⟩
  have hgap (j : ℤ) (t : ℝ) (ht : t ∈ Ioo (-ε) ε) :
      canonicalPeriodicGap hp hp1 (periodOnePotential (γ t)) (periodOnePotential_mem (γ t)) j =
        canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) j := by
    simpa only [hγ₀] using canonicalPeriodicGap_eq_on_sourceDirichletSpectral_integralCurve
      hp hp1 h2p k j γ (-ε) ε (fun t _ => hreal t) hder t 0 ht h0
  refine ⟨γ,hγ₀,hreal,ε,hε,hder,?_,hDis,?_⟩
  · intro t ht
    rw [hgap n t ht,hgap m t ht]
    exact ⟨hn,hm⟩
  · intro t ht
    simpa only [hγ₀] using D.thetaTheta_eq_on_sourceDirichletSpectral_integralCurve_of_initial_open
      h2p k n m γ (-ε) ε (fun t _ => hreal t) hder 0 t h0 ht
      (by simpa only [hγ₀] using hn) (by simpa only [hγ₀] using hm) |>.symm

end SourceAngularThetaCommonDomainData
end NLS.ZakharovShabat
