import NLS.ZakharovShabat.SourceBirkhoffSequence
import NLS.ZakharovShabat.SourceBirkhoffCoordinateBound
import NLS.ZakharovShabat.SourceAngularBetaCorrectionBound

/-! # Constructed local analytic Birkhoff sequence maps

The actual beta sum, normalized-action root, and gap-weighted eta
bounds give a bounded `ℓᵖ × ℓᵖ` realization on a full complex
neighborhood of every real source. All scalar evaluations are retained.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceAngularEtaLocalCommonDomainData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

theorem exists_local_birkhoffSequence_analytic
    (D : SourceAngularEtaLocalCommonDomainData hp hp1 W₀ B s)
    (Z : Set (CoeffPair p)) (hZ : IsOpen Z) (hZB : Z ⊆ B)
    (hz : ∀ n : ℤ, ∀ sign : ℂ, AnalyticOnNhd ℂ (sourceGapWeightedEtaCoordinate hp hp1 n s sign) Z)
    (Cz : ℝ) (hCz : 0 ≤ Cz)
    (hzbound : ∀ ψ ∈ Z, ∀ n : ℤ, ∀ sign : ℂ, ‖sign‖ ≤ 1 →
      ‖sourceGapWeightedEtaCoordinate hp hp1 n s sign ψ‖ ≤ Cz*
        (‖sourcePeriodicGapDisplacement hp hp1 ψ n‖+
          ‖canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n-sourceStandardRootMidpoint hp hp1 ψ n‖))
    (φ : CoeffPair p) (hφ : φ ∈ Z) (hreal : IsRealType (CoeffPair.toMax p φ)) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ φ ∈ U ∧ U ⊆ Z ∧
      AnalyticOnNhd ℂ (sourceBirkhoffMap hp hp1 s) U ∧
      ∃ M : ℝ, 0 ≤ M ∧ ∀ ψ ∈ U, ‖sourceBirkhoffMap hp hp1 s ψ‖ ≤ M ∧ ∀ n : ℤ,
        ((sourceBirkhoffMap hp hp1 s ψ).1 n = sourceBirkhoffX hp hp1 n s ψ ∧
          (sourceBirkhoffMap hp hp1 s ψ).2 n = sourceBirkhoffY hp hp1 n s ψ) ∧
        (sourceNormalizedActionRoot hp hp1 n ψ)^2 = 4*sourceNormalizedActionComplexExtension hp hp1 n ψ ∧
        sourceComplexAction hp hp1 n ψ =
          (sourcePeriodicGapDisplacement hp hp1 ψ n)^2 * sourceNormalizedActionComplexExtension hp hp1 n ψ := by
  obtain ⟨Vr,hVr,hφr,A,hA,hroot⟩ := exists_local_uniform_sourceNormalizedActionRoot_bound hp hp1 φ hreal
  obtain ⟨Va,hVa,hφa,hrootA,hfactor⟩ := exists_local_sourceNormalizedActionRoot_allIndices_analytic hp hp1 φ hreal
  obtain ⟨Vb,hVb,hφb,_,G,H,hG,hH,hbeta⟩ := D.exists_local_uniform_betaCorrection_bound φ (hZB hφ)
  let U := ((Z ∩ Vr) ∩ Va) ∩ Vb
  have hU : IsOpen U := ((hZ.inter hVr).inter hVa).inter hVb
  let C := 2*A*Cz*Real.exp H
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hcoord (n : ℤ) : AnalyticOnNhd ℂ (sourceBirkhoffX hp hp1 n s) U ∧
      AnalyticOnNhd ℂ (sourceBirkhoffY hp hp1 n s) U := by
    have hlocal ψ (hψ : ψ ∈ U) := analyticAt_sourceBirkhoffXY hp hp1 n s ψ
      (hrootA n ψ hψ.1.2) (fun sign => hz n sign ψ hψ.1.1.1)
      (D.beta_series.analytic_correction n ψ (hZB hψ.1.1.1))
    exact ⟨fun ψ hψ => (hlocal ψ hψ).1,fun ψ hψ => (hlocal ψ hψ).2⟩
  have hbound (ψ : CoeffPair p) (hψ : ψ ∈ U) (n : ℤ) :
      ‖sourceBirkhoffX hp hp1 n s ψ‖ ≤ C*(‖sourcePeriodicGapDisplacement hp hp1 ψ n‖+
        ‖sourceDirichletMidpointDisplacement hp hp1 ψ n‖) ∧
      ‖sourceBirkhoffY hp hp1 n s ψ‖ ≤ C*(‖sourcePeriodicGapDisplacement hp hp1 ψ n‖+
        ‖sourceDirichletMidpointDisplacement hp hp1 ψ n‖) := by
    rw [sourceDirichletMidpointDisplacement_apply]
    exact norm_sourceBirkhoffXY_le hp hp1 n s ψ A H Cz _ hA.le hCz (by positivity)
      (hroot ψ hψ.1.1.2 n) ((hbeta ψ hψ.2).2 n) (hzbound ψ hψ.1.1.1 n)
  obtain ⟨hmap,hdata⟩ := sourceBirkhoffSequence_analytic_of_uniform_bound hp hp1 s U hU C G hC
    hcoord hbound (fun ψ hψ => (hbeta ψ hψ.2).1)
  refine ⟨U,hU,⟨⟨⟨hφ,hφr⟩,hφa⟩,hφb⟩,(fun ψ hψ => hψ.1.1.1),hmap,C*G,mul_nonneg hC hG,?_⟩
  intro ψ hψ
  exact ⟨(hdata ψ hψ).1,fun n => ⟨(hdata ψ hψ).2 n,hfactor ψ hψ.1.2 n⟩⟩

end SourceAngularEtaLocalCommonDomainData
end NLS.ZakharovShabat
