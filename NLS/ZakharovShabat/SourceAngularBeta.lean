import NLS.ZakharovShabat.SourceAngularCollapsedSheetPrimitive

/-!
# The actual off-diagonal angular values of Section 13

At a regular Dirichlet terminal the normalized primitive determines
one value, including for collapsed gaps. At either periodic endpoint
the value is zero, consistently with every integrable endpoint path
on a regular prescribed sheet. The actual psi family supplies existence
and uniqueness for every off-diagonal pair on one open neighborhood
of all real sources. Source analyticity and the uniform estimates are
separate remaining assertions of Theorem 13.1.
-/

noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal unitInterval
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def SourceAngularDirichletTerminalIsEndpoint
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (m : ℤ) : Prop :=
  canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m =
      canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m ∨
    canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m =
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m

/-- Section 13's regular terminal value and its zero endpoint convention. -/
def sourceAngularBetaValues (hp : p ≠ ⊤) (hp1 : 1 < p) (n m : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (ψ : CoeffPair p) : Set ℂ := by
  classical
  exact if SourceAngularDirichletTerminalIsEndpoint hp hp1 ψ m then {0}
    else sourceAngularRegularDirichletValues hp hp1 n m s ψ

/-- The common-domain theorem below proves that the chosen value is
the unique actual off-diagonal angular value throughout that domain. -/
def sourceAngularBeta (hp : p ≠ ⊤) (hp1 : 1 < p) (n m : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (ψ : CoeffPair p) : ℂ :=
  Classical.epsilon (fun b => b ∈ sourceAngularBetaValues hp hp1 n m s ψ)

theorem sourceAngularBeta_eq_zero_of_endpoint
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n m : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (ψ : CoeffPair p)
    (hend : SourceAngularDirichletTerminalIsEndpoint hp hp1 ψ m) :
    sourceAngularBeta hp hp1 n m s ψ = 0 := by
  have hex : ∃ b : ℂ, b ∈ sourceAngularBetaValues hp hp1 n m s ψ :=
    ⟨0,by simp only [sourceAngularBetaValues,if_pos hend,mem_singleton_iff]⟩
  have hmem : sourceAngularBeta hp hp1 n m s ψ ∈ sourceAngularBetaValues hp hp1 n m s ψ :=
    Classical.epsilon_spec hex
  simpa only [sourceAngularBetaValues,if_pos hend,mem_singleton_iff] using hmem

/-- Real interlacing puts the collapsed Dirichlet terminal at its
periodic endpoint. Complex collapsed terminals were handled separately. -/
theorem sourceAngularBeta_eq_zero_of_real_collapsed_gap
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n m : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (ψ : CoeffPair p)
    (hreal : IsRealType (CoeffPair.toMax p ψ))
    (hgap : sourcePeriodicGapDisplacement hp hp1 ψ m = 0) :
    sourceAngularBeta hp hp1 n m s ψ = 0 := by
  have hK := sourcePeriodicSegment_eq_singleton_of_collapsed_gap hp hp1 ψ m hgap
  have hl := left_mem_segment ℝ
    (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m)
    (canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m)
  change _ ∈ sourcePeriodicSegment hp hp1 ψ m at hl
  rw [hK] at hl
  have hlτ : canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m =
      sourceStandardRootMidpoint hp hp1 ψ m := hl
  exact sourceAngularBeta_eq_zero_of_endpoint hp hp1 n m s ψ
    (Or.inl ((sourceDirichletRoot_eq_midpoint_of_real_collapsed_gap hp hp1 ψ hreal m hgap).trans hlτ.symm))

theorem SourceAngularDirichletPrimitiveData.beta_eq_terminal
    {hp : p ≠ ⊤} {hp1 : 1 < p} {n m : ℤ}
    {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k} {ψ : CoeffPair p}
    {c : ℂ} {R : ℝ} {F E : ℂ → ℂ} {A : ℂ}
    (hE : SourceAngularDirichletPrimitiveData hp hp1 n m s ψ c R F A E) :
    sourceAngularBeta hp hp1 n m s ψ =
      E (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m) := by
  have hne := sourceAngularRootSheet_point_ne_periodic_endpoints hp hp1 ψ m
    (sourceAntiDiscriminantCandidate hp hp1 ψ (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m))
    (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m) hE.root_ne_zero hE.terminal_mem.2
  have hend : ¬ SourceAngularDirichletTerminalIsEndpoint hp hp1 ψ m :=
    fun h => h.elim hne.1 hne.2
  have hmemE : E (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m) ∈
      sourceAngularBetaValues hp hp1 n m s ψ := by
    rw [sourceAngularBetaValues,if_neg hend]
    exact ⟨c,R,F,A,E,hE,rfl⟩
  have hmem : sourceAngularBeta hp hp1 n m s ψ ∈ sourceAngularRegularDirichletValues hp hp1 n m s ψ := by
    have h : sourceAngularBeta hp hp1 n m s ψ ∈ sourceAngularBetaValues hp hp1 n m s ψ :=
      Classical.epsilon_spec ⟨_,hmemE⟩
    simpa only [sourceAngularBetaValues,if_neg hend] using h
  obtain ⟨d,S,G,B,J,hJ,hβ⟩ := hmem
  exact hβ.symm.trans (hJ.terminal_eq hE)

/-- Integrable C¹ Dirichlet paths on the normalized regular sheet
evaluate to the actual beta value, including for collapsed gaps. -/
theorem SourceAngularDirichletPrimitiveData.pathIntegral_eq_beta
    {hp : p ≠ ⊤} {hp1 : 1 < p} {n m : ℤ}
    {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k} {ψ : CoeffPair p}
    {c : ℂ} {R : ℝ} {F E : ℂ → ℂ} {A : ℂ}
    (hE : SourceAngularDirichletPrimitiveData hp hp1 n m s ψ c R F A E)
    (γ : Path (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m)
      (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m))
    (hγ : ContDiffOn ℝ 1 γ.extend (Icc 0 1))
    (hγD : ∀ t ∈ Ioo (0:ℝ) 1, γ.extend t ∈ sourceAngularRegularSheetDisc hp ψ c R
      (sourceAntiDiscriminantCandidate hp hp1 ψ (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m)))
    (hInt : CurveIntegrable (holomorphicOneForm (fun z => sourceAngularIntegrand n s
      (sourceAngularRootSheet hp (sourceAntiDiscriminantCandidate hp hp1 ψ
        (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m))) (z,ψ))) γ) :
    sourceAngularPathIntegral n s (sourceAngularRootSheet hp (sourceAntiDiscriminantCandidate hp hp1 ψ
      (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m))) ψ γ = sourceAngularBeta hp hp1 n m s ψ :=
  (hE.pathIntegral_eq_terminal γ hγ hγD hInt).trans hE.beta_eq_terminal.symm

/-- Both endpoint boundary limits are zero, so the terminal sheet sign
does not affect an integrable path to either periodic endpoint. -/
theorem SourceAngularSheetPrimitiveData.periodicEndpoint_pathIntegral_eq_zero
    {hp : p ≠ ⊤} {hp1 : 1 < p} {n m : ℤ}
    {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k} {ψ : CoeffPair p}
    {c : ℂ} {R : ℝ} {w : ℂ} {F E : ℂ → ℂ} {A : ℂ}
    (hE : SourceAngularSheetPrimitiveData hp hp1 n m s ψ c R w F A E)
    {b : ℂ} (hb : b = canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m ∨
      b = canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m)
    (γ : Path (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m) b)
    (hγ : ContDiffOn ℝ 1 γ.extend (Icc 0 1))
    (hγD : ∀ t ∈ Ioo (0:ℝ) 1, γ.extend t ∈ sourceAngularRegularSheetDisc hp ψ c R w)
    (hInt : CurveIntegrable (holomorphicOneForm (fun z => sourceAngularIntegrand n s
      (sourceAngularRootSheet hp w) (z,ψ))) γ) :
    sourceAngularPathIntegral n s (sourceAngularRootSheet hp w) ψ γ = 0 := by
  have hend : Tendsto E (𝓝[sourceAngularRegularSheetDisc hp ψ c R w] b) (𝓝 0) := by
    rcases hb with rfl | rfl
    · exact hE.tendsto_left_sheet
    · exact hE.tendsto_right_sheet
  exact curveIntegral_eq_zero_of_primitive_boundary_ends _ E _ hE.hasDerivAt_sheet
    γ hγ hγD hInt hE.tendsto_left_sheet hend

theorem SourceAngularSheetPrimitiveData.endpoint_dirichlet_pathIntegral_eq_beta
    {hp : p ≠ ⊤} {hp1 : 1 < p} {n m : ℤ}
    {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k} {ψ : CoeffPair p}
    {c : ℂ} {R : ℝ} {w : ℂ} {F E : ℂ → ℂ} {A : ℂ}
    (hE : SourceAngularSheetPrimitiveData hp hp1 n m s ψ c R w F A E)
    (hend : SourceAngularDirichletTerminalIsEndpoint hp hp1 ψ m)
    (γ : Path (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m)
      (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m))
    (hγ : ContDiffOn ℝ 1 γ.extend (Icc 0 1))
    (hγD : ∀ t ∈ Ioo (0:ℝ) 1, γ.extend t ∈ sourceAngularRegularSheetDisc hp ψ c R w)
    (hInt : CurveIntegrable (holomorphicOneForm (fun z => sourceAngularIntegrand n s
      (sourceAngularRootSheet hp w) (z,ψ))) γ) :
    sourceAngularPathIntegral n s (sourceAngularRootSheet hp w) ψ γ = sourceAngularBeta hp hp1 n m s ψ := by
  rw [sourceAngularBeta_eq_zero_of_endpoint hp hp1 n m s ψ hend]
  exact hE.periodicEndpoint_pathIntegral_eq_zero hend γ hγ hγD hInt

theorem SourceAngularDirichletDiscFamilyData.exists_unique_beta_value
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k} {ψ : CoeffPair p}
    {c : ℤ → ℂ} {R : ℤ → ℝ}
    (D : SourceAngularDirichletDiscFamilyData hp hp1 s ψ c R)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 W s) (hψ : ψ ∈ W)
    (n m : ℤ) (hmn : m ≠ n) (hdata : SourceAngularEndpointSpectralData hp hp1 ψ m) :
    ∃! b : ℂ, b ∈ sourceAngularBetaValues hp hp1 n m s ψ := by
  by_cases hend : SourceAngularDirichletTerminalIsEndpoint hp hp1 ψ m
  · simpa only [sourceAngularBetaValues,if_pos hend,mem_singleton_iff] using
      (show ∃! b : ℂ, b = 0 from existsUnique_eq)
  · have hleft : canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m ≠
        canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m :=
      fun h => hend (Or.inl h)
    have hright : canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m ≠
        canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m :=
      fun h => hend (Or.inr h)
    simpa only [sourceAngularBetaValues,if_neg hend] using
      D.exists_unique_dirichlet_value_including_collapsed hs hψ n m hmn hdata hleft hright

/-- All actual off-diagonal beta values are constructed on one common
open neighborhood of all real sources, including every collapsed gap
and every periodic Dirichlet terminal. The full simply connected psi
domain and its estimates are retained separately. -/
theorem exists_sourceAngularBeta_common_domain (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W₀ W : Set (CoeffPair p), IsOpen W₀ ∧ IsSimplyConnected W₀ ∧
      realTypeSourceLocus p ⊆ W₀ ∧ IsOpen W ∧ realTypeSourceLocus p ⊆ W ∧ W ⊆ W₀ ∧
      ∃ s : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
        SourcePsiSquaredGapComplexExtension hp hp1 W₀ s ∧
          ∀ ψ ∈ W, ∀ n m : ℤ, m ≠ n →
            sourceAngularBeta hp hp1 n m s ψ ∈ sourceAngularBetaValues hp hp1 n m s ψ ∧
              ∀ b ∈ sourceAngularBetaValues hp hp1 n m s ψ, b = sourceAngularBeta hp hp1 n m s ψ := by
  obtain ⟨W₀,W,hW₀,hW₀conn,hW₀real,hW,hWreal,hWW₀,s,hs,hdata⟩ :=
    exists_sourceAngularDirichlet_common_domain hp hp1
  refine ⟨W₀,W,hW₀,hW₀conn,hW₀real,hW,hWreal,hWW₀,s,hs,?_⟩
  intro ψ hψ n m hmn
  obtain ⟨hendpoint,c,R,D⟩ := hdata ψ hψ
  have huniq := D.exists_unique_beta_value hs (hWW₀ hψ) n m hmn (hendpoint m)
  have hmem : sourceAngularBeta hp hp1 n m s ψ ∈ sourceAngularBetaValues hp hp1 n m s ψ :=
    Classical.epsilon_spec huniq.exists
  exact ⟨hmem,fun b hb => huniq.unique hb hmem⟩

end NLS.ZakharovShabat
