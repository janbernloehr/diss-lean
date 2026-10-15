import NLS.ZakharovShabat.SourceAngularOriginalTheta
import NLS.ZakharovShabat.SourceAngularThetaTheorem13_1

/-!
# All angular data for exactly the original domain and normalized family

The existing angular interfaces are constructed on W itself. The same W
serves as each ambient and working domain; no additional shrink or unrelated
normalized root family enters the canonical bracket results.
-/

noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceLemma12_12Data
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

theorem original_theta_common_domain (H : SourceLemma12_12Data hp hp1 W₀ W s) :
    SourceAngularThetaCommonDomainData hp hp1 W W W s := by
  have hW : IsOpen W := by
    obtain ⟨A,hW,_⟩ := H.previous.previous.atlas
    exact hW ▸ A.toSourcePsiComplexRootAtlas.isOpen_domain
  have hrealW : realTypeSourceLocus p ⊆ W := by
    obtain ⟨A,hW,_⟩ := H.previous.previous.atlas
    exact hW ▸ A.toSourcePsiComplexRootAtlas.realType_subset_domain
  let H2 := H.previous.previous.psi.previous.quotients.roots.roots.symmetric
  have hsym (ψ : CoeffPair p) (hψ : ψ ∈ W) (m : ℤ) :
      AnalyticAt ℂ (fun χ : CoeffPair p => canonicalPeriodicMidpoint hp hp1
        (periodOnePotential χ) (periodOnePotential_mem χ) m) ψ ∧
      AnalyticAt ℂ (fun χ : CoeffPair p => (canonicalPeriodicGap hp hp1
        (periodOnePotential χ) (periodOnePotential_mem χ) m)^2) ψ :=
    ⟨H2.midpoint m ψ (H.previous.previous.subset hψ),
      H2.squared_gap m ψ (H.previous.previous.subset hψ)⟩
  have hD : SourceAngularEtaLocalCommonDomainData hp hp1 W W s := by
    refine {
      psi := H.angular_extension
      roots_analytic := fun b m ψ hψ => (H2.simplicity.boundary ψ (H.previous.previous.subset hψ) b m).1
      boundary_analytic := H.boundary_original_displacement_analytic
      symmetric_analytic := hsym
      beta_values := ?_
      beta_analytic := H.beta_original_analytic
      beta_bound := H.beta_original_uniform_bound
      beta_series := H.beta_original_series
      eta_local_real := ?_
    }
    · intro ψ hψ n m hmn
      exact ⟨H.beta_original_mem_values ψ hψ n m hmn,fun b hb =>
        (H.beta_original_value_unique ψ hψ n m hmn).unique hb (H.beta_original_mem_values ψ hψ n m hmn)⟩
    · intro φ m hgap
      obtain ⟨hO,hP⟩ := sourceStandardRootOmittedJointProduct_analyticOnNhd_of_symmetric hp hp1 W hW hsym m
      obtain ⟨V,Ω,c,R,hφV,C⟩ :=
        H.angular_extension.toSourcePsiIsolatingComplexExtension.exists_local_canonical_cosine_angular_primitives
          W hW (Subset.refl _) φ.val (hrealW φ.property) φ.property m hgap hO hP
      obtain ⟨U,hU,hφU,hUV,ε,κ,hκ,hε,he,hterminal,hη⟩ :=
        C.exists_local_analytic_real_eta_cosine_representative φ.val hφV φ.property
      exact ⟨V,U,Ω,c,R,ε,κ,hφU,he,⟨C,hU,hUV,hκ,hε,
        (fun ψ hψ => ⟨(hterminal ψ hψ).1,(hterminal ψ hψ).2.1,(hterminal ψ hψ).2.2.1⟩),
        (fun ψ hψ => (hterminal ψ hψ).2.2.2),hη⟩⟩
  refine {
    toSourceAngularEtaLocalCommonDomainData := hD
    source_open := hW
    real_subset := hrealW
    source_subset := Subset.refl _
    beta_real := H.beta_original_im_eq_zero
    correction_real := H.beta_original_correction_im_eq_zero
    open_gap := fun m => (H.eta_original_phase_analytic m).1
    eta_phase_analytic := fun m => (H.eta_original_phase_analytic m).2.1
    theta_phase_analytic := H.theta_original_phase_analytic
    theta_phase_ne_zero := ?_
    theta_phase_norm_real := ?_
    local_charts := ?_
  }
  · intro ψ hψ m hgap
    rw [← H.theta_original_phase ψ hψ m hgap]
    exact Complex.exp_ne_zero _
  · intro ψ hψ hreal m hgap
    rw [← H.theta_original_phase ψ hψ m hgap,Complex.norm_exp]
    simp [Complex.mul_re,H.theta_original_im_eq_zero ψ hψ hreal m hgap]
  · intro m φ hφ hgap
    obtain ⟨V,U,c,T,r,R,z₀,ρ,δ,ε,hφU,hUW,hbase,E,_⟩ := H.eta_original_analytic_chart φ hφ m hgap
    exact ⟨V,U,c,T,r,R,z₀,ρ,δ,ε,hφU,hUW,hbase,E⟩

end SourceLemma12_12Data
end NLS.ZakharovShabat
