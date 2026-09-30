import NLS.ZakharovShabat.SourceAngularEtaCauchyTerminal

/-!
# Actual eta remainder formulas from either periodic anchor

Both canonical endpoint limits of the Cauchy remainder are zero.
The spectral integral decomposition therefore holds with either
periodic starting endpoint and any admissible continued root.
-/

noncomputable section
open Set Filter Topology Metric Complex NLS.ComplexAnalysis
open scoped ENNReal unitInterval
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceAngularJointAnnulusChartData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {m : ℤ}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}
  {W V : Set (CoeffPair p)} {c : ℤ → ℂ} {T : ℤ → ℝ} {r R : ℝ} {z₀ : ℂ}

/-- The same analytic remainder occurs with either periodic endpoint
as the initial anchor. At periodic terminals either root sign is allowed. -/
theorem eta_periodic_anchor_pathIntegral_eq_model_add_cauchy_remainder
    (D : SourceAngularJointAnnulusChartData hp hp1 m s W V c T r R z₀)
    (ψ : CoeffPair p) (hψ : ψ ∈ V) (ρ : ℝ) (hrρ : r < ρ) (hρR : ρ < R)
    {a : ℂ}
    (ha : a ∈ ({canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m,
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m} : Set ℂ))
    (Q : ℂ × CoeffPair p → ℂ)
    (γ : Path a (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m))
    (hQ : SourceAngularAdmissiblePathRootData hp hp1 m ψ (c m) r Q γ)
    (hnorm : sourceAntiDiscriminantCandidate hp hp1 ψ
      (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m) ≠ 0 →
      Q (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m,ψ) =
        sourceAntiDiscriminantCandidate hp hp1 ψ
          (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m))
    (hγ : ContDiffOn ℝ 1 γ.extend (Icc 0 1))
    (hint : CurveIntegrable (holomorphicOneForm (fun z => sourceAngularIntegrand m s Q (z,ψ))) γ)
    (hmodel : CurveIntegrable (holomorphicOneForm (sourceAngularEtaPathModelIntegrand hp hp1 m ψ Q)) γ) :
    sourceAngularPathIntegral m s Q ψ γ =
      (∫ᶜ z in γ, holomorphicOneForm (sourceAngularEtaPathModelIntegrand hp hp1 m ψ Q) z) +
        sourceAngularEtaRemainderCauchyCandidate hp hp1 m s (c m) r R z₀ ρ ψ := by
  have hother : closedBall (c m) r ⊆ sourceStandardRootOmittedDomain hp hp1 ψ m :=
    (closedBall_subset_closedBall (D.inner_lt_outer.trans D.outer_lt_assigned).le).trans
      ((D.disc_family ψ hψ).contour_family.2 m).2.2.1
  let μ := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m
  let w := sourceAntiDiscriminantCandidate hp hp1 ψ μ
  let H : ℂ → ℂ := fun z => sourceAngularEtaQuotientCauchyCandidate hp hp1 m s (c m) r R z₀ ρ (z,ψ)
  let F : ℂ → ℂ := fun z => sourceStandardRoot hp hp1 ψ m z*H z
  have hFdata := D.eta_cauchy_sheet_primitive_data ψ hψ ρ hrρ hρR 1 one_ne_zero
  have hstartF : Tendsto F (𝓝[ball (c m) r \ sourcePeriodicSegment hp hp1 ψ m] a) (𝓝 0) := by
    simp only [mem_insert_iff,mem_singleton_iff] at ha
    rcases ha with rfl | rfl
    · exact hFdata.tendsto_left_exterior
    · exact hFdata.tendsto_right_exterior
  obtain ⟨κ,hκ,hfixed⟩ := hQ.exists_fixed_sign hother
  have hend : Tendsto ((fun z => κ*F z) ∘ γ.extend) (𝓝[<] (1:ℝ))
      (𝓝 (sourceAngularEtaRemainderCauchyCandidate hp hp1 m s (c m) r R z₀ ρ ψ)) := by
    by_cases hw : w = 0
    · have hterminal := sourceDirichletRoot_mem_periodicEndpoints_of_antiDiscriminant_eq_zero
        hp hp1 ψ m (hother (ball_subset_closedBall (D.terminal_enclosed ψ hψ))) hw
      have hzero := D.etaRemainderCauchyCandidate_eq_zero_of_endpoint ψ hψ ρ
        (by simpa only [SourceAngularDirichletTerminalIsEndpoint,mem_insert_iff,mem_singleton_iff] using hterminal)
      rw [hzero]
      have hbound : Tendsto F (𝓝[ball (c m) r \ sourcePeriodicSegment hp hp1 ψ m] μ) (𝓝 0) := by
        simp only [mem_insert_iff,mem_singleton_iff] at hterminal
        rcases hterminal with hleft | hright
        · rw [show μ = _ from hleft]; exact hFdata.tendsto_left_exterior
        · rw [show μ = _ from hright]; exact hFdata.tendsto_right_exterior
      have hγend : Tendsto γ.extend (𝓝[<] (1:ℝ))
          (𝓝[ball (c m) r \ sourcePeriodicSegment hp hp1 ψ m] μ) := by
        apply tendsto_nhdsWithin_iff.mpr
        constructor
        · simpa only [Path.extend_one] using
            (γ.continuous_extend.continuousAt (x := (1:ℝ))).tendsto.mono_left nhdsWithin_le_nhds
        · filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0:ℝ) < 1)] with t ht
          exact hQ.interior t ht
      simpa only [Function.comp_def,mul_zero] using (hbound.comp hγend).const_mul κ
    · have hbase := sourceAngularRootSheet_dirichlet_base hp hp1 ψ m hw
      have hC := D.eta_cauchy_sheet_primitive_data ψ hψ ρ hrρ hρR w hw
      have hlim := hQ.signed_primitive_terminal_limit hC hother hw
        ⟨D.terminal_enclosed ψ hψ,hbase.1⟩ ((hnorm hw).trans hbase.2.symm) κ hκ hfixed
      dsimp only at hlim
      rw [hbase.2] at hlim
      exact hlim
  exact hQ.pathIntegral_decomposition_of_remainder_limits s hother F hFdata.hasDerivAt_exterior
    hstartF κ hκ hfixed _ hend hγ hint hmodel

end SourceAngularJointAnnulusChartData
end NLS.ZakharovShabat
