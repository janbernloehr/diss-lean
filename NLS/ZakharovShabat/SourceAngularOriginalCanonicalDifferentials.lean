import NLS.ZakharovShabat.SourceAngularOriginalThetaDomain
import NLS.ZakharovShabat.SourceCorollary13_2Regular

/-!
# The differentials of the literal original angle and indexed action

Local analytic representatives of the literal theta sum have the exact
cotangent used by the canonical bracket library. At real sources, the
indexed action has the same complex germ as the earlier action charts.
-/

noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceLemma12_12Data
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

theorem theta_original_local_differential_representative (H : SourceLemma12_12Data hp hp1 W₀ W s)
    (φ : CoeffPair p) (hφ : φ ∈ W) (n : ℤ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n ≠ 0) :
    ∃ U : Set (CoeffPair p), ∃ f : CoeffPair p → ℂ,
      IsOpen U ∧ φ ∈ U ∧ U ⊆ W ∧
      AnalyticOnNhd ℂ f U ∧
      (∀ ψ ∈ U, IsRealType (CoeffPair.toMax p ψ) → (f ψ).im = 0) ∧
      ∀ ψ ∈ U, (∃ k : ℤ, sourceAngularOriginalTheta hp hp1 n s ψ-f ψ = (k:ℂ)*Real.pi) ∧
        sourceAngularThetaDifferential hp hp1 n s ψ = fderiv ℂ f ψ := by
  obtain ⟨V,U,c,T,r,R,z₀,ρ,δ,ε,hφU,hUW,E,ha,hr⟩ :=
    H.original_theta_common_domain.exists_local_analytic_real_representative n φ hφ hgap
  refine ⟨U,sourceAngularThetaCauchyRepresentative hp hp1 n s (c n) r R z₀ ρ ε,
    E.angle.source_open,hφU,hUW,ha,hr,?_⟩
  intro ψ hψ
  refine ⟨?_,E.thetaDifferential_eq_fderiv_representative
    ((H.beta_original_series.analytic_correction n).mono hUW) ψ hψ⟩
  obtain ⟨P,hμ,Q,γ,hQ,hγ,hnorm,hi,hm,he⟩ := H.eta_original_integral_mem ψ (hUW hψ) n (E.gap_ne_zero ψ hψ)
  have hv := H.eta_original_pathIntegral_sub_representative E ψ hψ P hμ Q γ hQ hnorm hγ hi hm
  rw [he] at hv
  simpa only [sourceAngularOriginalTheta,sourceAngularThetaCauchyRepresentative,
    add_sub_add_right_eq_sub] using hv

/-- Complex germ agreement identifies the original indexed-action derivative at real sources. -/
theorem action_original_fderiv_eq_complexAction (H : SourceLemma12_12Data hp hp1 W₀ W s)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (hreal : IsRealType (CoeffPair.toMax p ψ)) (n : ℤ) :
    fderiv ℂ (sourceIndexedAction hp hp1 n) ψ = fderiv ℂ (sourceComplexAction hp hp1 n) ψ := by
  have A : SourceEquation2_16Data hp hp1 W₀ :=
    H.previous.previous.psi.previous.previous.previous.previous.previous
  obtain ⟨U,hU,hψU,_,he⟩ := A.complex_germs n ψ hreal (H.previous.previous.subset hψ)
  have hevent : sourceIndexedAction hp hp1 n =ᶠ[𝓝 ψ] sourceComplexAction hp hp1 n :=
    Filter.Eventually.mono (hU.mem_nhds hψU) (fun _ h => he h)
  exact hevent.fderiv_eq

/-- A regular cotangent whose underlying functional is the indexed action's actual derivative. -/
def originalActionCotangent (H : SourceLemma12_12Data hp hp1 W₀ W s)
    (n : ℤ) (φ : realTypeSourceLocus p) : NLS.Poisson.RegularSourceCotangent p where
  toCotangent := fderiv ℂ (sourceIndexedAction hp hp1 n) φ.val
  coefficients := (sourceActionRegularCotangent hp hp1 n φ).coefficients
  fst_eq := by
    intro k
    rw [H.action_original_fderiv_eq_complexAction φ.val
      (H.original_theta_common_domain.real_subset φ.property) φ.property n]
    simpa only [sourceActionRegularCotangent_toCotangent] using (sourceActionRegularCotangent hp hp1 n φ).fst_eq k
  snd_eq := by
    intro k
    rw [H.action_original_fderiv_eq_complexAction φ.val
      (H.original_theta_common_domain.real_subset φ.property) φ.property n]
    simpa only [sourceActionRegularCotangent_toCotangent] using (sourceActionRegularCotangent hp hp1 n φ).snd_eq k

@[simp] theorem originalActionCotangent_toCotangent (H : SourceLemma12_12Data hp hp1 W₀ W s)
    (n : ℤ) (φ : realTypeSourceLocus p) :
    (H.originalActionCotangent n φ).toCotangent = fderiv ℂ (sourceIndexedAction hp hp1 n) φ.val := rfl

/-- The angle's regular Fourier witness is the derivative of a local literal theta representative. -/
theorem theta_original_regularCotangent_representative (H : SourceLemma12_12Data hp hp1 W₀ W s)
    (n : ℤ) (φ : realTypeSourceLocus p)
    (hn : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0) :
    ∃ U : Set (CoeffPair p), ∃ f : CoeffPair p → ℂ,
      IsOpen U ∧ φ.val ∈ U ∧ U ⊆ W ∧ AnalyticOnNhd ℂ f U ∧
      (∀ ψ ∈ U, ∃ k : ℤ, sourceAngularOriginalTheta hp hp1 n s ψ-f ψ = (k:ℂ)*Real.pi) ∧
      (H.original_theta_common_domain.thetaRegularCotangent n φ hn).toCotangent = fderiv ℂ f φ.val := by
  obtain ⟨U,f,ho,hφU,hUW,ha,_,hd⟩ := H.theta_original_local_differential_representative
    φ.val (H.original_theta_common_domain.real_subset φ.property) n hn
  exact ⟨U,f,ho,hφU,hUW,ha,fun ψ hψ => (hd ψ hψ).1,
    (H.original_theta_common_domain.thetaRegularCotangent_toCotangent n φ hn).trans (hd φ.val hφU).2⟩

end SourceLemma12_12Data
end NLS.ZakharovShabat
