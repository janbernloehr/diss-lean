import NLS.ZakharovShabat.SourceAngularOriginalEtaRemainderValue
import NLS.ZakharovShabat.SourceAngularOriginalThetaDomain
import NLS.ZakharovShabat.SourceGapWeightedEta
import NLS.ComplexAnalysis.ImproperCurveIntegral

/-!
# Exact gap-weighted original eta phases

The canonical gap times exp(±i eta) agrees exactly with the gap-weighted
coordinate. The proof fixes the sign through the left endpoint model
normalization; equality of doubled phases alone would not suffice.
-/

noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal unitInterval
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceLemma12_12Data
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- The plus gap-weighted coordinate has the exact literal eta phase. -/
theorem gapWeightedEta_original_plus (H : SourceLemma12_12Data hp hp1 W₀ W s)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (n : ℤ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n ≠ 0) :
    sourceGapWeightedEtaCoordinate hp hp1 n s 1 ψ =
      canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n *
        Complex.exp (Complex.I*sourceAngularOriginalEta hp hp1 n s ψ) := by
  have hgap' : canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n ≠
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n := by
    intro h
    exact hgap (by simp only [canonicalPeriodicGap,h,sub_self])
  obtain ⟨Ps,hμs⟩ := H.angular_original_circles ψ hψ
  let P := Ps n
  have hμ := hμs n
  obtain ⟨Q,γ,hQ,hγ,hnorm,_,hi⟩ := H.original_dirichlet_integral_path ψ hψ n P hμ
  obtain ⟨hi,hm⟩ := hi hgap'
  let μ := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n
  let M := improperPathIntegral (sourceAngularEtaPathModelIntegrand hp hp1 n ψ Q) γ
  let η := sourceAngularPathIntegral n s Q ψ γ
  let R := sourceAngularEtaRemainder hp hp1 n s ψ
  have hM := hQ.improper_model_integral_spec P.closedBall_subset_omittedDomain
    (H.angular_endpoint_data ψ hψ n) hgap (P.gap (left_mem_segment ℝ _ _)) hμ (by simp)
    (hγ.mono Ioo_subset_Icc_self)
  have hR := H.eta_original_improper_remainder_eq_global ψ hψ n P hgap' hμ Q γ hQ
    (fun _ => hnorm) (hγ.mono Ioo_subset_Icc_self)
  have hlim := hR.add hM.1
  simp only [sub_add_cancel] at hlim
  have hη : η = M+R := by
    have he := tendsto_nhds_unique (tendsto_truncatedPathIntegral_of_curveIntegrable _ γ hi) hlim
    simpa only [M,R,η,sourceAngularPathIntegral,add_comm] using he
  have hleft : canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n -
      sourceStandardRootMidpoint hp hp1 ψ n =
        -(canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n/2) := by
    dsimp only [sourceStandardRootMidpoint,canonicalPeriodicMidpoint,canonicalPeriodicGap]
    ring
  have hroot : sourceAngularEtaSelectedPathRoot hp hp1 n ψ Q μ =
      -Complex.I*sourceDirichletEtaSineNumerator hp hp1 n ψ := by
    dsimp only [sourceAngularEtaSelectedPathRoot,sourceDirichletEtaSineNumerator,μ]
    rw [hnorm]
    simp only [div_eq_mul_inv,mul_inv_rev,inv_I]
    ring
  have hexp : sourceGapWeightedEtaCoordinate hp hp1 n s 1 ψ =
      canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n * Complex.exp (Complex.I*η) := by
    have he := hM.2
    rw [hleft,hroot] at he
    unfold sourceGapWeightedEtaCoordinate
    simp only [one_mul]
    rw [hη,mul_add Complex.I M R,Complex.exp_add]
    change -2*(μ-sourceStandardRootMidpoint hp hp1 ψ n + Complex.I*sourceDirichletEtaSineNumerator hp hp1 n ψ)*
      Complex.exp (Complex.I*R) = _
    change Complex.exp (Complex.I*M)*(-(_/2)) = _ at he
    linear_combination 2*Complex.exp (Complex.I*R)*he
  have hv : η ∈ sourceAngularOriginalEtaIntegralValues hp hp1 n s ψ :=
    ⟨P,hμ,Q,γ,hQ,hγ,(fun _ => hnorm),hi,hm,rfl⟩
  obtain ⟨k,hk⟩ := H.eta_original_integral_values_period ψ hψ n hgap hv
    (H.eta_original_integral_mem ψ hψ n hgap)
  have hphase : Complex.exp (Complex.I*η) = Complex.exp (Complex.I*sourceAngularOriginalEta hp hp1 n s ψ) := by
    apply Complex.exp_eq_exp_iff_exists_int.mpr
    exact ⟨k,by linear_combination Complex.I*hk⟩
  exact hexp.trans (congrArg (fun z => _*z) hphase)

/-- Both signs have the exact original integral phase. -/
theorem gapWeightedEta_original_signed (H : SourceLemma12_12Data hp hp1 W₀ W s)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (n : ℤ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n ≠ 0)
    (sign : ℂ) (hsign : sign = 1 ∨ sign = -1) :
    sourceGapWeightedEtaCoordinate hp hp1 n s sign ψ =
      canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n *
        Complex.exp (sign*Complex.I*sourceAngularOriginalEta hp hp1 n s ψ) := by
  have hplus := H.gapWeightedEta_original_plus ψ hψ n hgap
  rcases hsign with rfl | rfl
  · simpa only [one_mul] using hplus
  · obtain ⟨P,hμ⟩ := H.angular_original_circles ψ hψ
    have hprod := sourceGapWeightedEtaCoordinate_mul hp hp1 n s ψ
      ((P n).closedBall_subset_omittedDomain (ball_subset_closedBall (hμ n)))
    rw [hplus] at hprod
    apply mul_left_cancel₀ (mul_ne_zero hgap (Complex.exp_ne_zero _))
    rw [hprod]
    have he : Complex.exp (Complex.I*sourceAngularOriginalEta hp hp1 n s ψ)*
        Complex.exp (-1*Complex.I*sourceAngularOriginalEta hp hp1 n s ψ) = 1 := by
      rw [← Complex.exp_add]
      have hz : Complex.I*sourceAngularOriginalEta hp hp1 n s ψ +
          -1*Complex.I*sourceAngularOriginalEta hp hp1 n s ψ = 0 := by ring
      rw [hz,Complex.exp_zero]
    calc
      _ = (canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)^2 * 1 := by ring
      _ = (canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)^2 *
          (Complex.exp (Complex.I*sourceAngularOriginalEta hp hp1 n s ψ)*
            Complex.exp (-1*Complex.I*sourceAngularOriginalEta hp hp1 n s ψ)) := congrArg (fun z => _*z) he.symm
      _ = _ := by ring

/-- The original family already has analytic gap-weighted coordinates at all complex gaps. -/
theorem gapWeightedEta_original_analytic (H : SourceLemma12_12Data hp hp1 W₀ W s)
    (n : ℤ) (sign : ℂ) : AnalyticOnNhd ℂ (sourceGapWeightedEtaCoordinate hp hp1 n s sign) W := by
  intro ψ hψ
  obtain ⟨V,c,T,r,R,z₀,hψV,D,_⟩ := H.angular_original_annulus_chart ψ hψ n
  let ρ := (r+R)/2
  have hrρ : r < ρ := by dsimp [ρ]; linarith [D.inner_lt_outer]
  have hρR : ρ < R := by dsimp [ρ]; linarith [D.inner_lt_outer]
  exact D.analyticOnNhd_gapWeightedEtaCoordinate ρ hrρ hρR
    ((H.original_theta_common_domain.roots_analytic .dirichlet n).mono D.source_subset)
    (fun χ hχ => (H.original_theta_common_domain.symmetric_analytic χ (D.source_subset hχ) n).1) sign ψ hψV


end SourceLemma12_12Data
end NLS.ZakharovShabat
