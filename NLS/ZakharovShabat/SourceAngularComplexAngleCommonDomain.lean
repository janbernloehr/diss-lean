import NLS.ZakharovShabat.SourceAngularComplexDirichletAngle
import NLS.ZakharovShabat.SourceAngularEtaLocalCommonDomain

/-! # Complex Dirichlet angle charts on one actual source domain

A common complex neighborhood retains all established beta data and
has a constructed analytic half-gap and terminal angle at every open
complex gap. Assigned discs prove terminal containment in the omitted
domain; no geometric or analytic terminal hypotheses are left as input.
Identification of these charts with eta values remains separate.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Local source charts for the actual complex Dirichlet terminal,
including exact normalization of the lifted full root. -/
structure SourceAngularComplexDirichletAngleData
    (hp : p ≠ ⊤) (hp1 : 1 < p) (m : ℤ) (W U : Set (CoeffPair p))
    (δ ε : CoeffPair p → ℂ) : Prop where
  source_open : IsOpen U
  source_subset : U ⊆ W
  halfGap_analytic : AnalyticOnNhd ℂ δ U
  angle_analytic : AnalyticOnNhd ℂ ε U
  halfGap_ne_zero : ∀ ψ ∈ U, δ ψ ≠ 0
  halfGap_sq : ∀ ψ ∈ U, δ ψ ^ 2 = (canonicalPeriodicGap hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ) m / 2) ^ 2
  terminal_coordinates : ∀ ψ ∈ U,
    sourceAngularBranchCosinePoint hp hp1 m δ (ε ψ,ψ) =
      canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m ∧
    Complex.sin (ε ψ) = sourceAngularBranchDirichletSine hp hp1 m δ ψ
  terminal_root : ∀ ψ ∈ U, sourceAngularBranchCosineRoot hp hp1 m δ (ε ψ,ψ) =
    sourceAntiDiscriminantCandidate hp hp1 ψ (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m)

/-- Local terminal angles on different analytic half-gap branches agree
modulo pi. This statement concerns angles, before integrating eta. -/
theorem SourceAngularComplexDirichletAngleData.angle_sub_eq_int_pi
    {hp : p ≠ ⊤} {hp1 : 1 < p} {m : ℤ} {W U U' : Set (CoeffPair p)}
    {δ ε δ' ε' : CoeffPair p → ℂ}
    (D : SourceAngularComplexDirichletAngleData hp hp1 m W U δ ε)
    (D' : SourceAngularComplexDirichletAngleData hp hp1 m W U' δ' ε')
    (ψ : CoeffPair p) (hψ : ψ ∈ U) (hψ' : ψ ∈ U') :
    ∃ k : ℤ, ε ψ - ε' ψ = (k : ℂ) * (Real.pi : ℂ) := by
  let μ := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m
  let τ := canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m
  have hcos : Complex.cos (ε ψ) = (μ - τ) / δ ψ := by
    apply (eq_div_iff (D.halfGap_ne_zero ψ hψ)).mpr
    have hpoint := (D.terminal_coordinates ψ hψ).1
    change τ + δ ψ * Complex.cos (ε ψ) = μ at hpoint
    linear_combination hpoint
  have hcos' : Complex.cos (ε' ψ) = (μ - τ) / δ' ψ := by
    apply (eq_div_iff (D'.halfGap_ne_zero ψ hψ')).mpr
    have hpoint := (D'.terminal_coordinates ψ hψ').1
    change τ + δ' ψ * Complex.cos (ε' ψ) = μ at hpoint
    linear_combination hpoint
  have hsine := (D.terminal_coordinates ψ hψ).2
  have hsine' := (D'.terminal_coordinates ψ hψ').2
  have hsq : δ ψ ^ 2 = δ' ψ ^ 2 := (D.halfGap_sq ψ hψ).trans (D'.halfGap_sq ψ hψ').symm
  rcases eq_or_eq_neg_of_sq_eq_sq (δ ψ) (δ' ψ) hsq with hd | hd
  · apply NLS.ComplexAnalysis.angle_sub_eq_int_pi_of_coordinates_up_to_sign (ε ψ) (ε' ψ) 1 (Or.inl rfl)
    · rw [hsine,hsine']
      simp only [sourceAngularBranchDirichletSine,hd,one_mul]
    · rw [hcos,hcos',hd,one_mul]
  · apply NLS.ComplexAnalysis.angle_sub_eq_int_pi_of_coordinates_up_to_sign (ε ψ) (ε' ψ) (-1) (Or.inr rfl)
    · rw [hsine,hsine']
      simp only [sourceAngularBranchDirichletSine,hd,mul_neg,neg_mul,div_neg,one_mul]
    · rw [hcos,hcos',hd,div_neg,neg_one_mul]

/-- Every open complex gap on a constructed common neighborhood has
analytic terminal charts. The full beta theorem and real eta charts
are retained on a larger domain containing this neighborhood. -/
theorem exists_sourceAngular_complex_angle_common_domain
    (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W₀ B W : Set (CoeffPair p), IsOpen W₀ ∧ IsSimplyConnected W₀ ∧
      realTypeSourceLocus p ⊆ W₀ ∧ IsOpen B ∧ realTypeSourceLocus p ⊆ B ∧ B ⊆ W₀ ∧
      IsOpen W ∧ realTypeSourceLocus p ⊆ W ∧ W ⊆ B ∧
      ∃ s : (k : ℤ) → CoeffPair p → DeletedCoeff p k,
        SourceAngularEtaLocalCommonDomainData hp hp1 W₀ B s ∧
        ∀ φ ∈ W, ∀ m : ℤ, canonicalPeriodicGap hp hp1
          (periodOnePotential φ) (periodOnePotential_mem φ) m ≠ 0 →
          ∃ U : Set (CoeffPair p), ∃ δ ε : CoeffPair p → ℂ, φ ∈ U ∧
            δ φ = canonicalPeriodicGap hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) m / 2 ∧
            SourceAngularComplexDirichletAngleData hp hp1 m W U δ ε := by
  classical
  obtain ⟨W₀,B,hW₀,hW₀conn,hW₀real,hB,hBreal,hBW₀,s,D⟩ :=
    exists_sourceAngularEta_local_common_domain hp hp1
  obtain ⟨A,hA,_,hAreal,hprod⟩ := exists_global_source_analytic_omittedJointProduct hp hp1
  let O := B ∩ A
  have hO : IsOpen O := hB.inter hA
  have hOreal : realTypeSourceLocus p ⊆ O := fun φ hφ => ⟨hBreal hφ,hAreal hφ⟩
  have hlocal (φ : realTypeSourceLocus p) :=
    D.psi.toSourcePsiIsolatingComplexExtension.exists_local_angular_dirichlet_disc_family
      φ O hO (hOreal φ.property)
  choose ρ hρ hball c R hfamily using hlocal
  let W := ⋃ φ : realTypeSourceLocus p, ball φ.val (ρ φ)
  have hW : IsOpen W := isOpen_iUnion (fun _ => isOpen_ball)
  have hWreal : realTypeSourceLocus p ⊆ W := by
    intro φ hφ
    exact mem_iUnion.mpr ⟨⟨φ,hφ⟩,mem_ball_self (hρ ⟨φ,hφ⟩)⟩
  have hWO : W ⊆ O := by
    intro ψ hψ
    obtain ⟨φ,hψball⟩ := mem_iUnion.mp hψ
    exact hball φ hψball
  have hWB : W ⊆ B := hWO.trans inter_subset_left
  have hWA : W ⊆ A := hWO.trans inter_subset_right
  have heq (m : ℤ) : sourceStandardRootOmittedJointDomain hp hp1 W m =
      sourceStandardRootOmittedJointDomain hp hp1 A m ∩ (univ ×ˢ W) := by
    ext t
    exact ⟨fun ht => ⟨⟨hWA ht.1,ht.2⟩,mem_univ _,ht.1⟩,
      fun ht => ⟨ht.2.2,ht.1.2⟩⟩
  have hD (m : ℤ) : IsOpen (sourceStandardRootOmittedJointDomain hp hp1 W m) := by
    rw [heq m]
    exact (hprod m).1.inter (isOpen_univ.prod hW)
  have hP (m : ℤ) : AnalyticOnNhd ℂ (sourceStandardRootOmittedJointProduct hp hp1 m)
      (sourceStandardRootOmittedJointDomain hp hp1 W m) :=
    (hprod m).2.1.mono (fun t ht => ⟨hWA ht.1,ht.2⟩)
  refine ⟨W₀,B,W,hW₀,hW₀conn,hW₀real,hB,hBreal,hBW₀,hW,hWreal,hWB,s,D,?_⟩
  intro φ hφ m hgap
  obtain ⟨χ,hφball⟩ := mem_iUnion.mp hφ
  have hdisc := hfamily χ φ hφball
  have hμD : canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ m ∈
      sourceStandardRootOmittedDomain hp hp1 φ m :=
    (hdisc.contour_family.2 m).2.2.1 (ball_subset_closedBall (hdisc.dirichlet_mem_ball m))
  obtain ⟨U,hU,hφU,hUW,δ,ε,hδ,hε,hbase,hcoords⟩ :=
    exists_local_analytic_complex_dirichlet_angle hp hp1 W hW φ hφ m hgap
      (D.symmetric_analytic φ (hWB hφ) m).1 (D.symmetric_analytic φ (hWB hφ) m).2
      (D.roots_analytic .dirichlet m φ (hWB hφ)) hμD (hD m) (hP m)
  exact ⟨U,δ,ε,hφU,hbase,⟨hU,hUW,hδ,hε,
    (fun ψ hψ => (hcoords ψ hψ).1),(fun ψ hψ => (hcoords ψ hψ).2.1),
    (fun ψ hψ => ⟨(hcoords ψ hψ).2.2.1,(hcoords ψ hψ).2.2.2.1⟩),
    (fun ψ hψ => (hcoords ψ hψ).2.2.2.2)⟩⟩

end NLS.ZakharovShabat
