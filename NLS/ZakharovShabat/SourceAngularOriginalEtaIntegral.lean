import NLS.ZakharovShabat.SourceAngularOriginalEtaValues

/-!
# Eta chosen from actual original-disk integrals

The set of normalized integrable endpoint values is nonempty at every
open gap of the retained domain. Choosing a member defines one eta value;
all other admissible choices differ by an integer multiple of 2π.
Its local analytic representatives modulo π are the original eta charts.
-/

noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal unitInterval
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Values of actual normalized integrable eta paths in original isolating disks. -/
def sourceAngularOriginalEtaIntegralValues (hp : p ≠ ⊤) (hp1 : 1 < p) (m : ℤ)
    (s : (n : ℤ) → CoeffPair p → DeletedCoeff p n) (ψ : CoeffPair p) : Set ℂ :=
  {v | ∃ P : SourceCriticalRootPeriodCircle hp hp1 ψ m,
    canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m ∈ ball (P.center:ℂ) P.radius ∧
    ∃ Q : ℂ × CoeffPair p → ℂ,
    ∃ γ : Path (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m)
      (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m),
      SourceAngularAdmissiblePathRootData hp hp1 m ψ (P.center:ℂ) P.radius Q γ ∧
      ContDiffOn ℝ 1 γ.extend (Icc 0 1) ∧
      (sourceAntiDiscriminantCandidate hp hp1 ψ
        (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m) ≠ 0 →
        Q (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m,ψ) =
          sourceAntiDiscriminantCandidate hp hp1 ψ (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m)) ∧
      CurveIntegrable (holomorphicOneForm (fun z => sourceAngularIntegrand m s Q (z,ψ))) γ ∧
      CurveIntegrable (holomorphicOneForm (sourceAngularEtaPathModelIntegrand hp hp1 m ψ Q)) γ ∧
      sourceAngularPathIntegral m s Q ψ γ = v}

/-- A literal eta integral, defined modulo 2π; zero is only a fallback outside its proved domain. -/
def sourceAngularOriginalEta (hp : p ≠ ⊤) (hp1 : 1 < p) (m : ℤ)
    (s : (n : ℤ) → CoeffPair p → DeletedCoeff p n) (ψ : CoeffPair p) : ℂ := by
  classical
  exact if h : (sourceAngularOriginalEtaIntegralValues hp hp1 m s ψ).Nonempty then Classical.choose h else 0

namespace SourceLemma12_12Data
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

theorem eta_original_integral_values_nonempty (H : SourceLemma12_12Data hp hp1 W₀ W s)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (m : ℤ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m ≠ 0) :
    (sourceAngularOriginalEtaIntegralValues hp hp1 m s ψ).Nonempty := by
  obtain ⟨P,hμ,Q,γ,hQ,hγ,hnorm,hi,hm,_⟩ := H.eta_original_exists_phase_integral ψ hψ m hgap
  exact ⟨_,P,hμ,Q,γ,hQ,hγ,(fun _ => hnorm),hi,hm,rfl⟩

theorem eta_original_integral_mem (H : SourceLemma12_12Data hp hp1 W₀ W s)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (m : ℤ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m ≠ 0) :
    sourceAngularOriginalEta hp hp1 m s ψ ∈ sourceAngularOriginalEtaIntegralValues hp hp1 m s ψ := by
  have hne := H.eta_original_integral_values_nonempty ψ hψ m hgap
  unfold sourceAngularOriginalEta
  rw [dif_pos hne]
  exact Classical.choose_spec hne

/-- All actual integral choices define the same eta modulo 2π. -/
theorem eta_original_integral_values_period (H : SourceLemma12_12Data hp hp1 W₀ W s)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (m : ℤ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m ≠ 0)
    {v v' : ℂ} (hv : v ∈ sourceAngularOriginalEtaIntegralValues hp hp1 m s ψ)
    (hv' : v' ∈ sourceAngularOriginalEtaIntegralValues hp hp1 m s ψ) :
    ∃ k : ℤ, v-v' = (k:ℂ)*(2*Real.pi) := by
  obtain ⟨P,hμ,Q,γ,hQ,hγ,hnorm,hi,hm,rfl⟩ := hv
  obtain ⟨P',hμ',Q',κ,hQ',hκ,hnorm',hi',hm',rfl⟩ := hv'
  have hgap' : canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m ≠
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m := by
    intro h
    apply hgap
    simp only [canonicalPeriodicGap,h,sub_self]
  exact H.eta_original_dirichlet_path_periods_across_circles ψ hψ m P P' hgap' hμ hμ'
    Q Q' γ κ hQ hQ' hnorm hnorm' hγ hκ hi hi' hm hm'

theorem eta_original_integral_phase (H : SourceLemma12_12Data hp hp1 W₀ W s)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (m : ℤ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m ≠ 0) :
    Complex.exp (2*Complex.I*sourceAngularOriginalEta hp hp1 m s ψ) =
      sourceAngularEtaAnalyticPhase hp hp1 m s ψ := by
  obtain ⟨P,hμ,Q,γ,hQ,hγ,hnorm,hi,hm,he⟩ := H.eta_original_integral_mem ψ hψ m hgap
  rw [← he]
  exact H.eta_original_pathIntegral_phase ψ hψ m hgap P hμ Q γ hQ hnorm hγ hi hm

theorem eta_original_integral_im_eq_zero (H : SourceLemma12_12Data hp hp1 W₀ W s)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (hreal : IsRealType (CoeffPair.toMax p ψ)) (m : ℤ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m ≠ 0) :
    (sourceAngularOriginalEta hp hp1 m s ψ).im = 0 := by
  obtain ⟨P,hμ,Q,γ,hQ,hγ,hnorm,hi,hm,he⟩ := H.eta_original_integral_mem ψ hψ m hgap
  rw [← he]
  exact H.eta_original_pathIntegral_im_eq_zero ψ hψ hreal m hgap P hμ Q γ hQ hnorm hγ hi hm

/-- The chosen eta is the joint improper limit of an actual endpoint path integral. -/
theorem eta_original_exists_improper_integral (H : SourceLemma12_12Data hp hp1 W₀ W s)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (m : ℤ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m ≠ 0) :
    ∃ P : SourceCriticalRootPeriodCircle hp hp1 ψ m,
      ∃ Q : ℂ × CoeffPair p → ℂ,
      ∃ γ : Path (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m)
        (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m),
        SourceAngularAdmissiblePathRootData hp hp1 m ψ (P.center:ℂ) P.radius Q γ ∧
        ContDiffOn ℝ 1 γ.extend (Icc 0 1) ∧
        CurveIntegrable (holomorphicOneForm (fun z => sourceAngularIntegrand m s Q (z,ψ))) γ ∧
        Tendsto (fun u : ℝ × ℝ => ∫ t in u.1..u.2,
          curveIntegralFun (holomorphicOneForm (fun z => sourceAngularIntegrand m s Q (z,ψ))) γ t)
          ((𝓝[>] (0:ℝ)) ×ˢ (𝓝[<] (1:ℝ))) (𝓝 (sourceAngularOriginalEta hp hp1 m s ψ)) := by
  obtain ⟨P,_,Q,γ,hQ,hγ,_,hi,_,he⟩ := H.eta_original_integral_mem ψ hψ m hgap
  refine ⟨P,Q,γ,hQ,hγ,hi,?_⟩
  have hl := tendsto_curveIntegral_truncations
    (holomorphicOneForm (fun z => sourceAngularIntegrand m s Q (z,ψ))) γ hi
  change Tendsto _ _ (𝓝 (sourceAngularPathIntegral m s Q ψ γ)) at hl
  rwa [he] at hl

/-- The chosen literal eta has real analytic local representatives modulo π. -/
theorem eta_original_value_local_representative (H : SourceLemma12_12Data hp hp1 W₀ W s)
    (φ : CoeffPair p) (hφ : φ ∈ W) (m : ℤ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) m ≠ 0) :
    ∃ U : Set (CoeffPair p), ∃ f : CoeffPair p → ℂ,
      IsOpen U ∧ φ ∈ U ∧ U ⊆ W ∧
      (∀ ψ ∈ U, canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m ≠ 0) ∧
      AnalyticOnNhd ℂ f U ∧
      (∀ ψ ∈ U, IsRealType (CoeffPair.toMax p ψ) → (f ψ).im = 0) ∧
      ∀ ψ ∈ U, ∃ k : ℤ, sourceAngularOriginalEta hp hp1 m s ψ-f ψ = (k:ℂ)*Real.pi := by
  obtain ⟨U,f,ho,hφU,hUW,hg,ha,hr,_,hval⟩ := H.eta_original_local_representative φ hφ m hgap
  refine ⟨U,f,ho,hφU,hUW,hg,ha,hr,?_⟩
  intro ψ hψ
  obtain ⟨P,hμ,Q,γ,hQ,hγ,hnorm,hi,hm,he⟩ := H.eta_original_integral_mem ψ (hUW hψ) m (hg ψ hψ)
  rw [← he]
  exact hval ψ hψ P hμ Q γ hQ hnorm hγ hi hm

end SourceLemma12_12Data
end NLS.ZakharovShabat
