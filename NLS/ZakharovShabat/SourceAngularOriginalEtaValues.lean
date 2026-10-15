import NLS.ZakharovShabat.SourceAngularOriginalEtaComparison
import NLS.ZakharovShabat.SourceAngularOriginalEtaAnalytic

/-!
# Literal eta integrals and analytic representatives on the original domain

Every normalized integrable eta path in every original disk has the same
analytic phase. Local analytic representatives are real at real-type
sources and differ from all these literal integrals by integer multiples
of π. The disk, path, and terminal sheet need not vary continuously with
the source. Actual integrals exist by the endpoint construction.
-/

noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal unitInterval
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceLemma12_12Data
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- Every original-disk eta integral realizes the unique analytic phase. -/
theorem eta_original_pathIntegral_phase (H : SourceLemma12_12Data hp hp1 W₀ W s)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (m : ℤ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m ≠ 0)
    (P : SourceCriticalRootPeriodCircle hp hp1 ψ m)
    (hμ : canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m ∈ ball (P.center:ℂ) P.radius)
    (Q : ℂ × CoeffPair p → ℂ)
    (γ : Path (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m)
      (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m))
    (hQ : SourceAngularAdmissiblePathRootData hp hp1 m ψ (P.center:ℂ) P.radius Q γ)
    (hnorm : sourceAntiDiscriminantCandidate hp hp1 ψ
      (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m) ≠ 0 →
      Q (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m,ψ) =
        sourceAntiDiscriminantCandidate hp hp1 ψ (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m))
    (hγ : ContDiffOn ℝ 1 γ.extend (Icc 0 1))
    (hi : CurveIntegrable (holomorphicOneForm (fun z => sourceAngularIntegrand m s Q (z,ψ))) γ)
    (hm : CurveIntegrable (holomorphicOneForm (sourceAngularEtaPathModelIntegrand hp hp1 m ψ Q)) γ) :
    Complex.exp (2*Complex.I*sourceAngularPathIntegral m s Q ψ γ) =
      sourceAngularEtaAnalyticPhase hp hp1 m s ψ := by
  obtain ⟨P',hμ',Q',κ,hQ',hκ,hnorm',hi',hm',he⟩ := H.eta_original_exists_phase_integral ψ hψ m hgap
  have hgap' : canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m ≠
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m := by
    intro h
    apply hgap
    simp only [canonicalPeriodicGap,h,sub_self]
  obtain ⟨k,hk⟩ := H.eta_original_dirichlet_path_periods_across_circles ψ hψ m P P' hgap' hμ hμ'
    Q Q' γ κ hQ hQ' hnorm (fun _ => hnorm') hγ hκ hi hi' hm hm'
  rw [← he]
  apply Complex.exp_eq_exp_iff_exists_int.mpr
  refine ⟨2*k,?_⟩
  push_cast
  linear_combination 2*Complex.I*hk

/-- A local chart identifies all original-disk eta integrals, even outside its inner disk. -/
theorem eta_original_pathIntegral_sub_representative
    (H : SourceLemma12_12Data hp hp1 W₀ W s)
    {m : ℤ} {V U : Set (CoeffPair p)} {c : ℤ → ℂ} {T : ℤ → ℝ}
    {r R : ℝ} {z₀ : ℂ} {ρ : ℝ} {δ ε : CoeffPair p → ℂ}
    (E : SourceAngularEtaAnalyticChartData hp hp1 m s W V U c T r R z₀ ρ δ ε)
    (ψ : CoeffPair p) (hψ : ψ ∈ U)
    (P : SourceCriticalRootPeriodCircle hp hp1 ψ m)
    (hμ : canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m ∈ ball (P.center:ℂ) P.radius)
    (Q : ℂ × CoeffPair p → ℂ)
    (γ : Path (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m)
      (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m))
    (hQ : SourceAngularAdmissiblePathRootData hp hp1 m ψ (P.center:ℂ) P.radius Q γ)
    (hnorm : sourceAntiDiscriminantCandidate hp hp1 ψ
      (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m) ≠ 0 →
      Q (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m,ψ) =
        sourceAntiDiscriminantCandidate hp hp1 ψ (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m))
    (hγ : ContDiffOn ℝ 1 γ.extend (Icc 0 1))
    (hi : CurveIntegrable (holomorphicOneForm (fun z => sourceAngularIntegrand m s Q (z,ψ))) γ)
    (hm : CurveIntegrable (holomorphicOneForm (sourceAngularEtaPathModelIntegrand hp hp1 m ψ Q)) γ) :
    ∃ k : ℤ, sourceAngularPathIntegral m s Q ψ γ-
      sourceAngularEtaCauchyRepresentative hp hp1 m s (c m) r R z₀ ρ ε ψ = (k:ℂ)*Real.pi := by
  have he := H.eta_original_pathIntegral_phase ψ
    (E.annulus.source_subset (E.angle.source_subset hψ)) m (E.gap_ne_zero ψ hψ)
    P hμ Q γ hQ hnorm hγ hi hm
  rw [E.phase_eq_exp_representative ψ hψ] at he
  obtain ⟨k,hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp he
  refine ⟨k,?_⟩
  have hh := congrArg (fun z : ℂ => z/(2*Complex.I)) hk
  field_simp at hh
  linear_combination hh

/-- Analytic, real-type representatives of the literal original eta integrals. -/
theorem eta_original_local_representative (H : SourceLemma12_12Data hp hp1 W₀ W s)
    (φ : CoeffPair p) (hφ : φ ∈ W) (m : ℤ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) m ≠ 0) :
    ∃ U : Set (CoeffPair p), ∃ f : CoeffPair p → ℂ,
      IsOpen U ∧ φ ∈ U ∧ U ⊆ W ∧
      (∀ ψ ∈ U, canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m ≠ 0) ∧
      AnalyticOnNhd ℂ f U ∧
      (∀ ψ ∈ U, IsRealType (CoeffPair.toMax p ψ) → (f ψ).im = 0) ∧
      (∀ ψ ∈ U, Complex.exp (2*Complex.I*f ψ) = sourceAngularEtaAnalyticPhase hp hp1 m s ψ) ∧
      ∀ ψ ∈ U, ∀ P : SourceCriticalRootPeriodCircle hp hp1 ψ m,
        canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m ∈ ball (P.center:ℂ) P.radius →
        ∀ Q : ℂ × CoeffPair p → ℂ,
        ∀ γ : Path (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m)
          (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m),
          SourceAngularAdmissiblePathRootData hp hp1 m ψ (P.center:ℂ) P.radius Q γ →
          (sourceAntiDiscriminantCandidate hp hp1 ψ
            (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m) ≠ 0 →
            Q (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m,ψ) =
              sourceAntiDiscriminantCandidate hp hp1 ψ (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m)) →
          ContDiffOn ℝ 1 γ.extend (Icc 0 1) →
          CurveIntegrable (holomorphicOneForm (fun z => sourceAngularIntegrand m s Q (z,ψ))) γ →
          CurveIntegrable (holomorphicOneForm (sourceAngularEtaPathModelIntegrand hp hp1 m ψ Q)) γ →
          ∃ k : ℤ, sourceAngularPathIntegral m s Q ψ γ-f ψ = (k:ℂ)*Real.pi := by
  obtain ⟨V,U,c,T,r,R,z₀,ρ,δ,ε,hφU,hUW,_,E,_⟩ := H.eta_original_analytic_chart φ hφ m hgap
  refine ⟨U,sourceAngularEtaCauchyRepresentative hp hp1 m s (c m) r R z₀ ρ ε,
    E.angle.source_open,hφU,hUW,E.gap_ne_zero,E.eta_analytic,?_,?_,?_⟩
  · exact E.representative_im_eq_zero_of_realType H.angular_extension.toSourcePsiIsolatingComplexExtension
  · exact fun ψ hψ => (E.phase_eq_exp_representative ψ hψ).symm
  · exact H.eta_original_pathIntegral_sub_representative E

/-- Every actual eta integral is real at real-type sources. -/
theorem eta_original_pathIntegral_im_eq_zero (H : SourceLemma12_12Data hp hp1 W₀ W s)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (hreal : IsRealType (CoeffPair.toMax p ψ)) (m : ℤ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m ≠ 0)
    (P : SourceCriticalRootPeriodCircle hp hp1 ψ m)
    (hμ : canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m ∈ ball (P.center:ℂ) P.radius)
    (Q : ℂ × CoeffPair p → ℂ)
    (γ : Path (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m)
      (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m))
    (hQ : SourceAngularAdmissiblePathRootData hp hp1 m ψ (P.center:ℂ) P.radius Q γ)
    (hnorm : sourceAntiDiscriminantCandidate hp hp1 ψ
      (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m) ≠ 0 →
      Q (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m,ψ) =
        sourceAntiDiscriminantCandidate hp hp1 ψ (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m))
    (hγ : ContDiffOn ℝ 1 γ.extend (Icc 0 1))
    (hi : CurveIntegrable (holomorphicOneForm (fun z => sourceAngularIntegrand m s Q (z,ψ))) γ)
    (hm : CurveIntegrable (holomorphicOneForm (sourceAngularEtaPathModelIntegrand hp hp1 m ψ Q)) γ) :
    (sourceAngularPathIntegral m s Q ψ γ).im = 0 := by
  obtain ⟨U,f,_,hψU,_,_,_,hf,_,hval⟩ := H.eta_original_local_representative ψ hψ m hgap
  obtain ⟨k,hk⟩ := hval ψ hψU P hμ Q γ hQ hnorm hγ hi hm
  have hh := congrArg Complex.im hk
  simpa only [Complex.sub_im,Complex.mul_im,Complex.intCast_re,Complex.intCast_im,
    Complex.ofReal_re,Complex.ofReal_im,mul_zero,zero_mul,add_zero,hf ψ hψU hreal,sub_zero] using hh

end SourceLemma12_12Data
end NLS.ZakharovShabat
