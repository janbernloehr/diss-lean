import NLS.ZakharovShabat.SourceAngularEtaSheetReflection
import NLS.ZakharovShabat.SourceAngularEtaLocalCommonDomain

/-!
# Normalized eta periods on the common angular source domain

Shrink each constructed terminal chart by one real-centered source ball
on which all cosine periods have their exact Kronecker normalization.
This preserves its actual terminal angle and sheet sign. The original
and reflected representatives are analytic and have the same actual
terminal root and value. All of Theorem 13.1(i) and (iii) is retained
on the same common source domain. General spectral-path identification,
gap-label transitions, and coverage of every complex open-gap point
are not asserted here.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {m : ℤ}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}
  {W V U : Set (CoeffPair p)} {Ω : Set ℂ} {c : ℤ → ℂ} {R : ℤ → ℝ}
  {ε : CoeffPair p → ℂ} {κ : ℂ}

/-- Restriction keeps the exact terminal coordinates and source
analyticity of an actual eta cosine chart. -/
theorem SourceAngularEtaCosineSourceChartData.mono
    (D : SourceAngularEtaCosineSourceChartData hp hp1 m s W V U Ω c R ε κ)
    (U' : Set (CoeffPair p)) (hU' : IsOpen U') (hU'U : U' ⊆ U) :
    SourceAngularEtaCosineSourceChartData hp hp1 m s W V U' Ω c R ε κ :=
  ⟨D.chart,hU',hU'U.trans D.source_subset,D.sign,D.angle_analytic.mono hU'U,
    (fun ψ hψ => D.terminal_coordinates ψ (hU'U hψ)),
    (fun ψ hψ => D.terminal_root ψ (hU'U hψ)),D.eta_analytic.mono hU'U⟩

/-- The exact endpoint periods for all numerator indices are retained
on the analytic terminal chart's own source neighborhood. -/
structure SourceAngularEtaPeriodSourceChartData
    (hp : p ≠ ⊤) (hp1 : 1 < p) (m : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k)
    (W V U : Set (CoeffPair p)) (Ω : Set ℂ) (c : ℤ → ℂ) (R : ℤ → ℝ)
    (ε : CoeffPair p → ℂ) (κ : ℂ) : Prop
    extends SourceAngularEtaCosineSourceChartData hp hp1 m s W V U Ω c R ε κ where
  zero_angle_periods : ∀ ψ ∈ U, ∀ n : ℤ,
    sourceAngularCanonicalCosinePrimitive hp hp1 n m s (0,ψ) =
      -I * (Real.pi : ℂ) * (if m = n then 1 else 0)

/-- A constructed real terminal chart can be shrunk to retain all
exact cosine periods without changing its terminal angle or sign. -/
theorem SourceAngularEtaCosineSourceChartData.exists_period_chart
    (D : SourceAngularEtaCosineSourceChartData hp hp1 m s W V U Ω c R ε κ)
    (φ : CoeffPair p) (hφ : φ ∈ U) (hreal : IsRealType (CoeffPair.toMax p φ)) :
    ∃ U' : Set (CoeffPair p), U' ⊆ U ∧ φ ∈ U' ∧
      SourceAngularEtaPeriodSourceChartData hp hp1 m s W V U' Ω c R ε κ := by
  obtain ⟨O,hO,hφO,_,hperiod⟩ :=
    D.chart.exists_local_primitive_zero_angle_periods φ (D.source_subset hφ) hreal
  exact ⟨U ∩ O,inter_subset_left,⟨hφ,hφO⟩,
    ⟨D.mono (U ∩ O) (D.source_open.inter hO) inter_subset_left,
      fun ψ hψ => hperiod ψ hψ.2⟩⟩

namespace SourceAngularEtaPeriodSourceChartData

/-- The selected diagonal has its exact nonzero half period at every
complex source in the constructed local terminal chart. -/
theorem diagonal_period
    (D : SourceAngularEtaPeriodSourceChartData hp hp1 m s W V U Ω c R ε κ)
    (ψ : CoeffPair p) (hψ : ψ ∈ U) :
    sourceAngularCanonicalCosinePrimitive hp hp1 m m s (0,ψ) = -I * (Real.pi : ℂ) := by
  simpa only [eq_self_iff_true,ite_true,mul_one] using D.zero_angle_periods ψ hψ m

/-- The right-endpoint eta value is the signed pi value on the same
complex source neighborhood as the moving Dirichlet terminal. -/
theorem eta_right_endpoint
    (D : SourceAngularEtaPeriodSourceChartData hp hp1 m s W V U Ω c R ε κ)
    (ψ : CoeffPair p) (hψ : ψ ∈ U) :
    sourceAngularEtaCosineRepresentative hp hp1 m s κ (0,ψ) = -κ * (Real.pi : ℂ) :=
  SourceAngularCanonicalCosineChartData.etaCosineRepresentative_zero_angle ψ (D.diagonal_period ψ hψ) κ

/-- The reflected moving terminal is analytic and gives exactly
the original representative, with the same actual normalized root. -/
theorem reflected_terminal
    (D : SourceAngularEtaPeriodSourceChartData hp hp1 m s W V U Ω c R ε κ) :
    AnalyticOnNhd ℂ (fun ψ =>
      sourceAngularEtaReflectedCosineRepresentative hp hp1 m s (-κ) (-ε ψ,ψ)) U ∧
      ∀ ψ ∈ U,
        sourceAngularCosineLiftedRoot hp hp1 m (-κ) (-ε ψ,ψ) =
          sourceAntiDiscriminantCandidate hp hp1 ψ (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m) ∧
        sourceAngularEtaReflectedCosineRepresentative hp hp1 m s (-κ) (-ε ψ,ψ) =
          sourceAngularEtaCosineRepresentative hp hp1 m s κ (ε ψ,ψ) := by
  have hfun : (fun ψ => sourceAngularEtaReflectedCosineRepresentative hp hp1 m s (-κ) (-ε ψ,ψ)) =
      (fun ψ => sourceAngularEtaCosineRepresentative hp hp1 m s κ (ε ψ,ψ)) :=
    funext (fun ψ => sourceAngularEtaReflectedCosineRepresentative_neg_neg hp hp1 m s κ (ε ψ) ψ)
  refine ⟨hfun ▸ D.eta_analytic,?_⟩
  intro ψ hψ
  exact ⟨(sourceAngularCosineLiftedRoot_neg_neg hp hp1 m κ (ε ψ) ψ).trans (D.terminal_root ψ hψ),
    sourceAngularEtaReflectedCosineRepresentative_neg_neg hp hp1 m s κ (ε ψ) ψ⟩

/-- The two normalized angle charts agree modulo pi on their overlap
at every complex source in the constructed terminal neighborhood. -/
theorem overlap_mod_pi
    (D : SourceAngularEtaPeriodSourceChartData hp hp1 m s W V U Ω c R ε κ)
    (ψ : CoeffPair p) (hψ : ψ ∈ U) (θ : ℂ) (hθ : θ ∈ Ω) (hnegθ : -θ ∈ Ω) :
    ∃ k : ℤ, sourceAngularEtaReflectedCosineRepresentative hp hp1 m s κ (θ,ψ) =
      sourceAngularEtaCosineRepresentative hp hp1 m s κ (θ,ψ) + (k : ℂ) * (Real.pi : ℂ) :=
  D.chart.etaReflectedCosineRepresentative_eq_mod_pi ψ (D.source_subset hψ)
    (D.diagonal_period ψ hψ) θ κ hθ hnegθ D.sign

end SourceAngularEtaPeriodSourceChartData

/-- The common angular data now include local real open-gap eta
charts with the exact diagonal and off-diagonal endpoint periods. -/
structure SourceAngularEtaPeriodCommonDomainData
    (hp : p ≠ ⊤) (hp1 : 1 < p) (W₀ W : Set (CoeffPair p))
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) : Prop
    extends SourceAngularEtaLocalCommonDomainData hp hp1 W₀ W s where
  eta_local_period_real : ∀ φ : realTypeSourceLocus p, ∀ m : ℤ,
    canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) m ≠ 0 →
    ∃ V U : Set (CoeffPair p), ∃ Ω : Set ℂ, ∃ c : ℤ → ℂ, ∃ R : ℤ → ℝ,
      ∃ ε : CoeffPair p → ℂ, ∃ κ : ℂ, φ.val ∈ U ∧
        ε φ.val ∈ segment ℝ (0 : ℂ) (Real.pi : ℂ) ∧
        SourceAngularEtaPeriodSourceChartData hp hp1 m s W V U Ω c R ε κ

/-- The same full normalized psi extension and all beta assertions
coexist with analytic, exactly period-normalized eta cosine charts. -/
theorem exists_sourceAngularEta_period_common_domain
    (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W₀ W : Set (CoeffPair p), IsOpen W₀ ∧ IsSimplyConnected W₀ ∧
      realTypeSourceLocus p ⊆ W₀ ∧ IsOpen W ∧ realTypeSourceLocus p ⊆ W ∧ W ⊆ W₀ ∧
      ∃ s : (k : ℤ) → CoeffPair p → DeletedCoeff p k,
        SourceAngularEtaPeriodCommonDomainData hp hp1 W₀ W s := by
  obtain ⟨W₀,W,hW₀,hW₀conn,hW₀real,hW,hWreal,hWW₀,s,D⟩ :=
    exists_sourceAngularEta_local_common_domain hp hp1
  refine ⟨W₀,W,hW₀,hW₀conn,hW₀real,hW,hWreal,hWW₀,s,⟨D,?_⟩⟩
  intro φ m hgap
  obtain ⟨V,U,Ω,c,R,ε,κ,hφU,he,E⟩ := D.eta_local_real φ m hgap
  obtain ⟨U',_,hφU',E'⟩ := E.exists_period_chart φ.val hφU φ.property
  exact ⟨V,U',Ω,c,R,ε,κ,hφU',he,E'⟩

end NLS.ZakharovShabat
