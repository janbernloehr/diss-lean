import NLS.ZakharovShabat.SourceAngularOriginalBetaPaths

/-!
# Diagonal eta path periods in every original disk

The actual original diagonal normalization constructs its remainder
primitive. Any two integrable admissible continuations to the Dirichlet
root differ by an integer multiple of 2π. Only regular terminal roots
are prescribed; at a periodic terminal either sign is allowed.
-/

noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal unitInterval
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceLemma12_12Data
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- Actual eta integrals on any original disk agree modulo 2π. -/
theorem eta_original_dirichlet_path_periods (H : SourceLemma12_12Data hp hp1 W₀ W s)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (n : ℤ)
    (P : SourceCriticalRootPeriodCircle hp hp1 ψ n)
    (hgap : canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n ≠
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)
    (hμ : canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n ∈ ball (P.center:ℂ) P.radius) :
    let μ := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n
    let w := sourceAntiDiscriminantCandidate hp hp1 ψ μ
    ∀ Q Q' : ℂ × CoeffPair p → ℂ,
    ∀ (γ κ : Path
      (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n) μ),
      SourceAngularAdmissiblePathRootData hp hp1 n ψ (P.center:ℂ) P.radius Q γ →
      SourceAngularAdmissiblePathRootData hp hp1 n ψ (P.center:ℂ) P.radius Q' κ →
      (w ≠ 0 → Q (μ,ψ) = w) → (w ≠ 0 → Q' (μ,ψ) = w) →
      ContDiffOn ℝ 1 γ.extend (Icc 0 1) → ContDiffOn ℝ 1 κ.extend (Icc 0 1) →
      CurveIntegrable (holomorphicOneForm (fun z => sourceAngularIntegrand n s Q (z,ψ))) γ →
      CurveIntegrable (holomorphicOneForm (fun z => sourceAngularIntegrand n s Q' (z,ψ))) κ →
      CurveIntegrable (holomorphicOneForm (sourceAngularEtaPathModelIntegrand hp hp1 n ψ Q)) γ →
      CurveIntegrable (holomorphicOneForm (sourceAngularEtaPathModelIntegrand hp hp1 n ψ Q')) κ →
      ∃ k : ℤ, sourceAngularPathIntegral n s Q ψ γ-sourceAngularPathIntegral n s Q' ψ κ =
        k*(2*Real.pi) := by
  intro μ w Q Q' γ κ hQ hQ' hnorm hnorm' hγ hκ hint hint' hmodel hmodel'
  have hdata := H.angular_endpoint_data ψ hψ n
  have hgap' : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n ≠ 0 :=
    sub_ne_zero.mpr (Ne.symm hgap)
  by_cases hw : w ≠ 0
  · obtain ⟨F,E,hE⟩ := H.eta_original_sheet_primitive ψ hψ n P hgap w hw
    have hbase := sourceAngularRootSheet_dirichlet_base hp hp1 ψ n hw
    exact hE.admissible_pathIntegral_sub_eq_int_two_pi P.gap P.closedBall_subset_omittedDomain
      hdata hgap' hw ⟨hμ,hbase.1⟩ Q Q' γ κ hQ hQ' ((hnorm hw).trans hbase.2.symm)
      ((hnorm' hw).trans hbase.2.symm) hγ hκ hint hint' hmodel hmodel'
  · have hzero : sourceAntiDiscriminantCandidate hp hp1 ψ μ = 0 := not_ne_iff.mp hw
    have hend := sourceDirichletRoot_mem_periodicEndpoints_of_antiDiscriminant_eq_zero hp hp1 ψ n
      (P.closedBall_subset_omittedDomain (ball_subset_closedBall hμ)) hzero
    obtain ⟨F,E,hE⟩ := H.eta_original_sheet_primitive ψ hψ n P hgap 1 one_ne_zero
    exact hE.admissible_periodic_terminal_pathIntegral_sub_eq_int_two_pi P.gap
      P.closedBall_subset_omittedDomain hdata hgap' hμ hend Q Q' γ κ hQ hQ' hγ hκ hint hint' hmodel hmodel'

/-- Original isolating disks already contain the actual Dirichlet terminals. -/
theorem original_dirichlet_mem_circle
    {V : Set (CoeffPair p)} {D : ℤ → Set ℂ} {c : ℝ}
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (ψ : CoeffPair p) (hψ : ψ ∈ V) (m : ℤ) (a r : ℝ)
    (hr : 0 < r) (he : D m = ball (a:ℂ) r) :
    canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m ∈
      ball ((hD.periodCircle ψ hψ m a r hr he).center:ℂ) (hD.periodCircle ψ hψ m a r hr he).radius := by
  change canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m ∈ ball (a:ℂ) r
  rw [← he]
  exact hD.cluster ψ hψ m (Or.inr (Or.inr (Or.inl rfl)))

end SourceLemma12_12Data
end NLS.ZakharovShabat
