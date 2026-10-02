import NLS.ZakharovShabat.SourceAngularThetaTheorem13_1

/-! # Real angle charts for a fixed normalized root family

Any open part of the common angular domain admits actual eta charts
at its real open gaps. This preserves the chosen root family when the
angular construction is used by a later sequence map.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceAngularEtaLocalCommonDomainData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B : Set (CoeffPair p)}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}

/-- Construct an actual eta chart for the existing family at a real
open gap, inside any given open subset of its angular domain. -/
theorem exists_real_analytic_eta_chart
    (D : SourceAngularEtaLocalCommonDomainData hp hp1 W₀ B s)
    (W : Set (CoeffPair p)) (hW : IsOpen W) (hWB : W ⊆ B)
    (φ : CoeffPair p) (hφ : φ ∈ W) (hreal : IsRealType (CoeffPair.toMax p φ))
    (n : ℤ) (hgap : canonicalPeriodicGap hp hp1
      (periodOnePotential φ) (periodOnePotential_mem φ) n ≠ 0) :
    ∃ O V U : Set (CoeffPair p), ∃ c : ℤ → ℂ, ∃ T : ℤ → ℝ,
      ∃ r R : ℝ, ∃ z₀ : ℂ, ∃ ρ : ℝ, ∃ δ ε : CoeffPair p → ℂ,
        φ ∈ U ∧ U ⊆ W ∧
        δ φ = canonicalPeriodicGap hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n/2 ∧
        SourceAngularEtaAnalyticChartData hp hp1 n s O V U c T r R z₀ ρ δ ε := by
  obtain ⟨a,ha,_,_,_,_,hball,_⟩ := D.psi.isolation ⟨φ,hreal⟩
  obtain ⟨A,hA,_,hAreal,hprod⟩ := exists_global_source_analytic_omittedJointProduct hp hp1
  let O := (W ∩ ball φ a) ∩ A
  have hO : IsOpen O := (hW.inter isOpen_ball).inter hA
  have hOW : O ⊆ W := fun _ h => h.1.1
  have hOW₀ : O ⊆ W₀ := fun _ h => hball h.1.2
  have hφO : φ ∈ O := ⟨⟨hφ,mem_ball_self ha⟩,hAreal hreal⟩
  obtain ⟨V,c,T,r,R,z₀,hφV,C⟩ :=
    D.psi.toSourcePsiIsolatingComplexExtension.exists_local_joint_angular_annulus_primitives
      O hO hOW₀ (fun ψ hψ => D.symmetric_analytic ψ (hWB (hOW hψ))) φ hφO hreal n
  have hVA : V ⊆ A := fun _ h => (C.source_subset h).2
  have heq : sourceStandardRootOmittedJointDomain hp hp1 V n =
      sourceStandardRootOmittedJointDomain hp hp1 A n ∩ (univ ×ˢ V) := by
    ext t
    exact ⟨fun ht => ⟨⟨hVA ht.1,ht.2⟩,mem_univ _,ht.1⟩,
      fun ht => ⟨ht.2.2,ht.1.2⟩⟩
  have hDom : IsOpen (sourceStandardRootOmittedJointDomain hp hp1 V n) := by
    rw [heq]
    exact (hprod n).1.inter (isOpen_univ.prod C.source_open)
  have hP : AnalyticOnNhd ℂ (sourceStandardRootOmittedJointProduct hp hp1 n)
      (sourceStandardRootOmittedJointDomain hp hp1 V n) :=
    (hprod n).2.1.mono (fun _ ht => ⟨hVA ht.1,ht.2⟩)
  let ρ := (r+R)/2
  have hrρ : r < ρ := by dsimp only [ρ]; linarith [C.inner_lt_outer]
  have hρR : ρ < R := by dsimp only [ρ]; linarith [C.inner_lt_outer]
  obtain ⟨U,δ,ε,hφU,hδ,E⟩ := C.exists_local_analytic_eta_chart ρ hrρ hρR φ hφV hgap
    (D.symmetric_analytic φ (hWB hφ) n).1 (D.symmetric_analytic φ (hWB hφ) n).2
    ((D.roots_analytic .dirichlet n).mono (C.source_subset.trans (hOW.trans hWB))) hDom hP
  exact ⟨O,V,U,c,T,r,R,z₀,ρ,δ,ε,hφU,E.angle.source_subset.trans (C.source_subset.trans hOW),hδ,E⟩

/-- Every off-diagonal beta is real on the real part of an open angular domain. -/
theorem beta_im_eq_zero_of_realType
    (D : SourceAngularEtaLocalCommonDomainData hp hp1 W₀ B s)
    (W : Set (CoeffPair p)) (hW : IsOpen W) (hWB : W ⊆ B)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n m : ℤ) (hmn : m ≠ n) : (sourceAngularBeta hp hp1 n m s ψ).im = 0 := by
  by_cases hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m = 0
  · rw [sourceAngularBeta_eq_zero_of_real_collapsed_gap hp hp1 n m s ψ hreal
      (by simpa only [sourcePeriodicGapDisplacement_apply] using hgap)]
    rfl
  · obtain ⟨O,V,U,c,T,r,R,z₀,ρ,δ,ε,hψU,_,_,E⟩ :=
      D.exists_real_analytic_eta_chart W hW hWB ψ hψ hreal m hgap
    exact E.beta_im_eq_zero_of_realType D.psi.toSourcePsiIsolatingComplexExtension ψ hψU hreal n hmn

/-- The convergent beta correction remains real for the fixed root family. -/
theorem correction_im_eq_zero_of_realType
    (D : SourceAngularEtaLocalCommonDomainData hp hp1 W₀ B s)
    (W : Set (CoeffPair p)) (hW : IsOpen W) (hWB : W ⊆ B)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (hreal : IsRealType (CoeffPair.toMax p ψ)) (n : ℤ) :
    (sourceAngularBetaCorrection hp hp1 n s ψ).im = 0 :=
  D.beta_series.toSourceAngularBetaSeriesAnalyticData.correction_im_eq_zero_of_terms ψ (hWB hψ) n
    (D.beta_im_eq_zero_of_realType W hW hWB ψ hψ hreal n)

end SourceAngularEtaLocalCommonDomainData
end NLS.ZakharovShabat
