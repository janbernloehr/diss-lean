import NLS.ZakharovShabat.SourceDirichletSpectralLocalFlow

/-! # Actual local isospectral transport of the angle/angle bracket

The proved zero source derivative gives constancy along actual indexed
spectral integral curves while the two angle gaps stay open. The local
ODE theorem constructs such a real curve through every real open-gap
source. Continuity shrinks its time interval into the actual common
angle domain. The resulting curve preserves both every discriminant
and the full actual angle/angle bracket, with no supplied trajectory,
chart or stationarity premise. Global transport remains separate.
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

/-- A constructed local real indexed spectral curve through every
actual open-gap source preserves every discriminant and the full
angle/angle bracket. The open-gap time interval is constructed too. -/
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
  let V : Set (CoeffPair p) :=
    {ψ | ψ ∈ W ∧ canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n ≠ 0} ∩
    {ψ | ψ ∈ W ∧ canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m ≠ 0}
  have hV : IsOpen V := (D.open_gap n).inter (D.open_gap m)
  have hφV : φ.val ∈ V := ⟨⟨D.real_subset φ.property,hn⟩,⟨D.real_subset φ.property,hm⟩⟩
  have h0 : (0:ℝ) ∈ Ioo (-ε) ε := ⟨by linarith,hε⟩
  have hcont : Tendsto γ (𝓝 0) (𝓝 φ.val) := by
    simpa only [hγ₀] using (hder 0 h0).continuousAt.tendsto
  have ht : {t : ℝ | γ t ∈ V} ∈ 𝓝 0 := hcont.eventually (hV.mem_nhds hφV)
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp ht
  let δ := min ε r
  have hδ : 0 < δ := lt_min hε hr
  have hsub (t : ℝ) (ht : t ∈ Ioo (-δ) δ) : t ∈ Ioo (-ε) ε := by
    have hle : δ ≤ ε := min_le_left _ _
    exact ⟨by linarith [ht.1],by linarith [ht.2]⟩
  have hmem (t : ℝ) (ht : t ∈ Ioo (-δ) δ) : γ t ∈ V := by
    apply hball
    have hle : δ ≤ r := min_le_right _ _
    rw [Real.ball_eq_Ioo]
    exact ⟨by linarith [ht.1],by linarith [ht.2]⟩
  refine ⟨γ,hγ₀,hreal,δ,hδ,fun t ht => hder t (hsub t ht),
    fun t ht => ⟨(hmem t ht).1.2,(hmem t ht).2.2⟩,
    fun t ht => hDis t (hsub t ht),?_⟩
  intro t ht
  have h0δ : (0:ℝ) ∈ Ioo (-δ) δ := ⟨by linarith,hδ⟩
  simpa only [hγ₀] using D.thetaTheta_eq_on_sourceDirichletSpectral_integralCurve h2p k n m γ (-δ) δ
    (fun t _ => hreal t) (fun t ht => hder t (hsub t ht))
    (fun t ht => (hmem t ht).1.2) (fun t ht => (hmem t ht).2.2) t 0 ht h0δ

end SourceAngularThetaCommonDomainData
end NLS.ZakharovShabat
