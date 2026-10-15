import NLS.ZakharovShabat.SourceAngularOriginalEtaImproperRemainder
import NLS.ComplexAnalysis.ImproperCurveIntegral

/-!
# Original eta values for arbitrary admissible paths

Every interior C¹ admissible continuation has a joint improper integral.
Its value agrees modulo 2π with the original eta chosen from constructed
integrable paths. This also compares different original disks and covers
periodic terminals without a terminal sign prescription.
-/

noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal unitInterval
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceLemma12_12Data
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- Every admissible path converges to a representative of the original eta class. -/
theorem eta_original_admissible_improper_limit (H : SourceLemma12_12Data hp hp1 W₀ W s)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (n : ℤ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n ≠ 0)
    (P : SourceCriticalRootPeriodCircle hp hp1 ψ n)
    (hμ : canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n ∈ ball (P.center:ℂ) P.radius)
    (Q : ℂ × CoeffPair p → ℂ)
    (γ : Path (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)
      (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n))
    (hQ : SourceAngularAdmissiblePathRootData hp hp1 n ψ (P.center:ℂ) P.radius Q γ)
    (hnorm : sourceAntiDiscriminantCandidate hp hp1 ψ (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n) ≠ 0 →
      Q (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n,ψ) =
        sourceAntiDiscriminantCandidate hp hp1 ψ (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n))
    (hγ : ContDiffOn ℝ 1 γ.extend (Ioo 0 1)) :
    ∃ L : ℂ, Tendsto (fun u : ℝ × ℝ => truncatedPathIntegral
      (fun z => sourceAngularIntegrand n s Q (z,ψ)) γ u.1 u.2)
      ((𝓝[>] (0:ℝ)) ×ˢ (𝓝[<] (1:ℝ))) (𝓝 L) ∧
      ∃ k : ℤ, L-sourceAngularOriginalEta hp hp1 n s ψ = (k:ℂ)*(2*Real.pi) := by
  have hgap' : canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n ≠
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n := by
    intro h
    exact hgap (by simp only [canonicalPeriodicGap,h,sub_self])
  obtain ⟨B,hB⟩ := H.eta_original_common_improper_remainder ψ hψ n P hgap' hμ
  have hdata := H.angular_endpoint_data ψ hψ n
  have hmodel := (hQ.improper_model_integral_spec P.closedBall_subset_omittedDomain hdata hgap
    (P.gap (left_mem_segment ℝ _ _)) hμ (by simp) hγ).1
  let M := improperPathIntegral (sourceAngularEtaPathModelIntegrand hp hp1 n ψ Q) γ
  have hL : Tendsto (fun u : ℝ × ℝ => truncatedPathIntegral
      (fun z => sourceAngularIntegrand n s Q (z,ψ)) γ u.1 u.2)
      ((𝓝[>] (0:ℝ)) ×ˢ (𝓝[<] (1:ℝ))) (𝓝 (M+B)) := by
    have hl := (hB Q γ hQ hnorm hγ).add hmodel
    simp only [sub_add_cancel] at hl
    simpa only [M,add_comm] using hl
  obtain ⟨Q',γ',hQ',hγ',hnorm',_,hi⟩ := H.original_dirichlet_integral_path ψ hψ n P hμ
  obtain ⟨hi',hm'⟩ := hi hgap'
  have hγi' := hγ'.mono Ioo_subset_Icc_self
  have hmodel' := (hQ'.improper_model_integral_spec P.closedBall_subset_omittedDomain hdata hgap
    (P.gap (left_mem_segment ℝ _ _)) hμ (by simp) hγi').1
  let M' := improperPathIntegral (sourceAngularEtaPathModelIntegrand hp hp1 n ψ Q') γ'
  have hL' : Tendsto (fun u : ℝ × ℝ => truncatedPathIntegral
      (fun z => sourceAngularIntegrand n s Q' (z,ψ)) γ' u.1 u.2)
      ((𝓝[>] (0:ℝ)) ×ˢ (𝓝[<] (1:ℝ))) (𝓝 (M'+B)) := by
    have hl := (hB Q' γ' hQ' (fun _ => hnorm') hγi').add hmodel'
    simp only [sub_add_cancel] at hl
    simpa only [M',add_comm] using hl
  have heval : M'+B = sourceAngularPathIntegral n s Q' ψ γ' :=
    tendsto_nhds_unique hL' (tendsto_truncatedPathIntegral_of_curveIntegrable _ γ' hi')
  have hterminal : Q (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n,ψ) =
      Q' (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n,ψ) := by
    rw [hnorm']
    by_cases hw : sourceAntiDiscriminantCandidate hp hp1 ψ (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n) ≠ 0
    · exact hnorm hw
    · have hw0 := not_ne_iff.mp hw
      rw [hw0]
      exact sourceAngularPathRoot_eq_zero_at_periodic_endpoint hp hp1 n ψ Q _
        (by simpa only [Path.extend_one] using hQ.square_root 1 (by norm_num))
        (P.closedBall_subset_omittedDomain (ball_subset_closedBall hμ))
        (sourceDirichletRoot_mem_periodicEndpoints_of_antiDiscriminant_eq_zero hp hp1 ψ n
          (P.closedBall_subset_omittedDomain (ball_subset_closedBall hμ)) hw0)
  obtain ⟨k,hk⟩ := hQ.improper_model_integral_periods γ' hQ' P.closedBall_subset_omittedDomain
    hdata hgap (P.gap (left_mem_segment ℝ _ _)) hμ (by simp) hterminal hγ hγi'
  have hv : sourceAngularPathIntegral n s Q' ψ γ' ∈ sourceAngularOriginalEtaIntegralValues hp hp1 n s ψ :=
    ⟨P,hμ,Q',γ',hQ',hγ',(fun _ => hnorm'),hi',hm',rfl⟩
  obtain ⟨j,hj⟩ := H.eta_original_integral_values_period ψ hψ n hgap hv
    (H.eta_original_integral_mem ψ hψ n hgap)
  refine ⟨M+B,hL,k+j,?_⟩
  change M-M' = (k:ℂ)*(2*Real.pi) at hk
  push_cast
  linear_combination hk + hj + heval

/-- The actual limit-defined eta integral lies in the existing 2π class. -/
theorem eta_original_improperIntegral_spec (H : SourceLemma12_12Data hp hp1 W₀ W s)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (n : ℤ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n ≠ 0)
    (P : SourceCriticalRootPeriodCircle hp hp1 ψ n)
    (hμ : canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n ∈ ball (P.center:ℂ) P.radius)
    (Q : ℂ × CoeffPair p → ℂ)
    (γ : Path (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)
      (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n))
    (hQ : SourceAngularAdmissiblePathRootData hp hp1 n ψ (P.center:ℂ) P.radius Q γ)
    (hnorm : sourceAntiDiscriminantCandidate hp hp1 ψ (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n) ≠ 0 →
      Q (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n,ψ) =
        sourceAntiDiscriminantCandidate hp hp1 ψ (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n))
    (hγ : ContDiffOn ℝ 1 γ.extend (Ioo 0 1)) :
    let L := improperPathIntegral (fun z => sourceAngularIntegrand n s Q (z,ψ)) γ
    Tendsto (fun u : ℝ × ℝ => truncatedPathIntegral
      (fun z => sourceAngularIntegrand n s Q (z,ψ)) γ u.1 u.2)
      ((𝓝[>] (0:ℝ)) ×ˢ (𝓝[<] (1:ℝ))) (𝓝 L) ∧
      ∃ k : ℤ, L-sourceAngularOriginalEta hp hp1 n s ψ = (k:ℂ)*(2*Real.pi) := by
  obtain ⟨L,hL,hperiod⟩ := H.eta_original_admissible_improper_limit ψ hψ n hgap P hμ Q γ hQ hnorm hγ
  have hv : improperPathIntegral (fun z => sourceAngularIntegrand n s Q (z,ψ)) γ = L := hL.limUnder_eq
  simpa only [hv] using And.intro hL hperiod

end SourceLemma12_12Data
end NLS.ZakharovShabat
