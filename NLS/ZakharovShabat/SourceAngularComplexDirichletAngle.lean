import NLS.ComplexAnalysis.ComplexCircleTerminal
import NLS.ZakharovShabat.SourceAnalyticHalfGap
import NLS.ZakharovShabat.SourceAngularCanonicalCosineEndpoint

/-! # Dirichlet angles on analytic half-gap branches

At any complex source with an open gap, the analytic squared gap
constructs a local half-gap. The actual anti-discriminant and omitted
product then give analytic sine and cosine coordinates. Their circle
identity constructs a moving angle and exactly normalizes its lifted
root, also at a periodic terminal with zero anti-discriminant.
-/

noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual Dirichlet sine for a chosen analytic half-gap. -/
def sourceAngularBranchDirichletSine (hp : p ≠ ⊤) (hp1 : 1 < p) (m : ℤ)
    (δ : CoeffPair p → ℂ) : CoeffPair p → ℂ := fun ψ =>
  sourceAntiDiscriminantCandidate hp hp1 ψ (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m) /
    (2 * δ ψ * sourceStandardRootOmittedProduct hp hp1 m ψ
      (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m))

def sourceAngularBranchCosinePoint (hp : p ≠ ⊤) (hp1 : 1 < p) (m : ℤ)
    (δ : CoeffPair p → ℂ) : ℂ × CoeffPair p → ℂ := fun x =>
  cosineGapPoint (canonicalPeriodicMidpoint hp hp1
    (periodOnePotential x.2) (periodOnePotential_mem x.2) m) (δ x.2) x.1

def sourceAngularBranchCosineRoot (hp : p ≠ ⊤) (hp1 : 1 < p) (m : ℤ)
    (δ : CoeffPair p → ℂ) : ℂ × CoeffPair p → ℂ := fun x =>
  2 * δ x.2 * sourceStandardRootOmittedProduct hp hp1 m x.2
    (sourceAngularBranchCosinePoint hp hp1 m δ x) * Complex.sin x.1

/-- The Dirichlet circle identity is independent of periodic endpoint
ordering and does not require real interlacing. -/
theorem sourceAngularBranchDirichletSine_sq_add_cosine_sq
    (hp : p ≠ ⊤) (hp1 : 1 < p) (m : ℤ) (δ : CoeffPair p → ℂ)
    (ψ : CoeffPair p) (hδ : δ ψ ≠ 0)
    (hδsq : δ ψ ^ 2 = (canonicalPeriodicGap hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ) m / 2) ^ 2)
    (hμ : canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m ∈
      sourceStandardRootOmittedDomain hp hp1 ψ m) :
    sourceAngularBranchDirichletSine hp hp1 m δ ψ ^ 2 +
      ((canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m -
        canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m) /
          δ ψ) ^ 2 = 1 := by
  let μ := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m
  let τ := canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m
  let γ := canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m
  let P := sourceStandardRootOmittedProduct hp hp1 m ψ μ
  let w := sourceAntiDiscriminantCandidate hp hp1 ψ μ
  have hP : P ≠ 0 := sourceStandardRootOmittedProduct_ne_zero hp hp1 ψ μ m hμ
  have hid : w ^ 2 = (γ ^ 2 - 4 * (μ - τ) ^ 2) * P ^ 2 := by
    dsimp only [w]
    rw [← sourceDiscriminant_sq_sub_four_at_canonicalDirichletRoot hp hp1 ψ m,
      canonicalDiscriminant_sq_sub_four_eq_pair_mul hp hp1 _ (periodOnePotential_mem ψ) m,
      ← sourceStandardRootOmittedProduct_sq_eq_canonicalDeletedPeriodicProduct hp hp1 ψ m μ hμ]
    dsimp only [γ,τ,canonicalPeriodicGap,canonicalPeriodicMidpoint,P]
    ring
  have hγsq : γ ^ 2 = 4 * δ ψ ^ 2 := by
    change δ ψ ^ 2 = (γ / 2) ^ 2 at hδsq
    linear_combination -4 * hδsq
  change (w / (2 * δ ψ * P)) ^ 2 + ((μ - τ) / δ ψ) ^ 2 = 1
  field_simp [hδ,hP]
  linear_combination hid + P ^ 2 * hγsq

/-- The lifted branch is a square root of the actual discriminant
radicand at every cosine point in the omitted-root domain. -/
theorem sourceAngularBranchCosineRoot_sq
    (hp : p ≠ ⊤) (hp1 : 1 < p) (m : ℤ) (δ : CoeffPair p → ℂ)
    (ψ : CoeffPair p) (e : ℂ)
    (hδsq : δ ψ ^ 2 = (canonicalPeriodicGap hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ) m / 2) ^ 2)
    (hz : sourceAngularBranchCosinePoint hp hp1 m δ (e,ψ) ∈ sourceStandardRootOmittedDomain hp hp1 ψ m) :
    sourceAngularBranchCosineRoot hp hp1 m δ (e,ψ) ^ 2 =
      sourceAngularRadicand hp (sourceAngularBranchCosinePoint hp hp1 m δ (e,ψ),ψ) := by
  let z := sourceAngularBranchCosinePoint hp hp1 m δ (e,ψ)
  let τ := canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m
  let γ := canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m
  let P := sourceStandardRootOmittedProduct hp hp1 m ψ z
  have hl : canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m = τ - γ / 2 := by
    dsimp only [τ,γ,canonicalPeriodicMidpoint,canonicalPeriodicGap]; ring
  have hr : canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m = τ + γ / 2 := by
    dsimp only [τ,γ,canonicalPeriodicMidpoint,canonicalPeriodicGap]; ring
  have hpoly : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m - z) *
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m - z) =
        -(δ ψ) ^ 2 * Complex.sin e ^ 2 := by
    rw [hl,hr]
    calc
      _ = (τ - z) ^ 2 - (γ / 2) ^ 2 := by ring
      _ = (τ - z) ^ 2 - (δ ψ) ^ 2 := by rw [← hδsq]
      _ = (τ - δ ψ - z) * (τ + δ ψ - z) := by ring
      _ = -(δ ψ) ^ 2 * Complex.sin e ^ 2 := by
        rw [show z = cosineGapPoint τ (δ ψ) e from rfl]
        simpa only [neg_mul] using cosineGapPoint_endpoint_factor τ (δ ψ) e
  change (2 * δ ψ * P * Complex.sin e) ^ 2 = canonicalDiscriminant hp (periodOnePotential ψ) z ^ 2 - 4
  rw [canonicalDiscriminant_sq_sub_four_eq_pair_mul hp hp1 _ (periodOnePotential_mem ψ) m z,
    ← sourceStandardRootOmittedProduct_sq_eq_canonicalDeletedPeriodicProduct hp hp1 ψ m z hz]
  change (2 * δ ψ * P * Complex.sin e) ^ 2 = -4 * _ * _ * P ^ 2
  linear_combination 4 * P ^ 2 * hpoly

/-- The branch sine stays analytic when the terminal anti-discriminant
vanishes; only the half-gap and omitted product must be nonzero. -/
theorem analyticAt_sourceAngularBranchDirichletSine
    (hp : p ≠ ⊤) (hp1 : 1 < p) (m : ℤ) (δ : CoeffPair p → ℂ)
    (W : Set (CoeffPair p)) (φ : CoeffPair p) (hφ : φ ∈ W)
    (hδ : AnalyticAt ℂ δ φ) (hδne : δ φ ≠ 0)
    (hμ : AnalyticAt ℂ (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m) φ)
    (hμD : canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ m ∈ sourceStandardRootOmittedDomain hp hp1 φ m)
    (hP : AnalyticOnNhd ℂ (sourceStandardRootOmittedJointProduct hp hp1 m)
      (sourceStandardRootOmittedJointDomain hp hp1 W m)) :
    AnalyticAt ℂ (sourceAngularBranchDirichletSine hp hp1 m δ) φ := by
  let μ : CoeffPair p → ℂ := fun ψ => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m
  have hgraph : AnalyticAt ℂ (fun ψ => (μ ψ,ψ)) φ := hμ.prod analyticAt_id
  have hprod := (hP (μ φ,φ) ⟨hφ,hμD⟩).comp
    (f := fun ψ : CoeffPair p => (μ ψ,ψ)) hgraph
  have hanti := (analyticOnNhd_sourceAntiDiscriminantCandidate_joint hp hp1
    (μ φ,φ) (mem_univ _)).comp (f := fun ψ : CoeffPair p => (μ ψ,ψ)) hgraph
  exact hanti.div ((analyticAt_const.mul hδ).mul hprod)
    (mul_ne_zero (mul_ne_zero (by norm_num) hδne)
      (sourceStandardRootOmittedProduct_ne_zero hp hp1 φ (μ φ) m hμD))

theorem sourceAngularBranchCosineRoot_eq_dirichlet_anti
    (hp : p ≠ ⊤) (hp1 : 1 < p) (m : ℤ) (δ : CoeffPair p → ℂ)
    (ψ : CoeffPair p) (e : ℂ) (hδ : δ ψ ≠ 0)
    (hμD : canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m ∈ sourceStandardRootOmittedDomain hp hp1 ψ m)
    (hpoint : sourceAngularBranchCosinePoint hp hp1 m δ (e,ψ) =
      canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m)
    (hsin : Complex.sin e = sourceAngularBranchDirichletSine hp hp1 m δ ψ) :
    sourceAngularBranchCosineRoot hp hp1 m δ (e,ψ) =
      sourceAntiDiscriminantCandidate hp hp1 ψ (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m) := by
  have hP := sourceStandardRootOmittedProduct_ne_zero hp hp1 ψ
    (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m) m hμD
  simp only [sourceAngularBranchCosineRoot,hpoint,hsin,sourceAngularBranchDirichletSine]
  exact mul_div_cancel₀ _ (mul_ne_zero (mul_ne_zero (by norm_num) hδ) hP)

/-- Every open complex source gap has a constructed analytic half-gap
and moving terminal angle with the actual Dirichlet sheet normalization.
This includes both endpoint terminals and needs no real-source hypothesis. -/
theorem exists_local_analytic_complex_dirichlet_angle
    (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p)) (hW : IsOpen W)
    (φ : CoeffPair p) (hφ : φ ∈ W) (m : ℤ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) m ≠ 0)
    (hτ : AnalyticAt ℂ (fun ψ : CoeffPair p => canonicalPeriodicMidpoint hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ) m) φ)
    (hγsq : AnalyticAt ℂ (fun ψ : CoeffPair p => (canonicalPeriodicGap hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ) m) ^ 2) φ)
    (hμ : AnalyticAt ℂ (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m) φ)
    (hμD : canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ m ∈ sourceStandardRootOmittedDomain hp hp1 φ m)
    (hD : IsOpen (sourceStandardRootOmittedJointDomain hp hp1 W m))
    (hP : AnalyticOnNhd ℂ (sourceStandardRootOmittedJointProduct hp hp1 m)
      (sourceStandardRootOmittedJointDomain hp hp1 W m)) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ φ ∈ U ∧ U ⊆ W ∧
      ∃ δ ε : CoeffPair p → ℂ, AnalyticOnNhd ℂ δ U ∧ AnalyticOnNhd ℂ ε U ∧
        δ φ = canonicalPeriodicGap hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) m / 2 ∧
        ∀ ψ ∈ U, δ ψ ≠ 0 ∧ δ ψ ^ 2 = (canonicalPeriodicGap hp hp1
          (periodOnePotential ψ) (periodOnePotential_mem ψ) m / 2) ^ 2 ∧
          sourceAngularBranchCosinePoint hp hp1 m δ (ε ψ,ψ) =
            canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m ∧
          Complex.sin (ε ψ) = sourceAngularBranchDirichletSine hp hp1 m δ ψ ∧
          sourceAngularBranchCosineRoot hp hp1 m δ (ε ψ,ψ) =
            sourceAntiDiscriminantCandidate hp hp1 ψ (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m) := by
  obtain ⟨V,hV,hφV,hVW,δ,hδ,hbase,hroots⟩ :=
    exists_local_sourceAnalyticHalfGap hp hp1 W hW φ hφ m hgap hγsq
  let τ : CoeffPair p → ℂ := fun ψ => canonicalPeriodicMidpoint hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ) m
  let μ : CoeffPair p → ℂ := fun ψ => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m
  let σ := sourceAngularBranchDirichletSine hp hp1 m δ
  have hgraph : ContinuousAt (fun ψ => (μ ψ,ψ)) φ := (hμ.prod analyticAt_id).continuousAt
  have hterminal : ∀ᶠ ψ in 𝓝 φ, μ ψ ∈ sourceStandardRootOmittedDomain hp hp1 ψ m := by
    filter_upwards [hgraph.preimage_mem_nhds (hD.mem_nhds ⟨hφ,hμD⟩)] with ψ hψ
    exact hψ.2
  have hcircle : ∀ᶠ ψ in 𝓝 φ, σ ψ ^ 2 + ((μ ψ - τ ψ) / δ ψ) ^ 2 = 1 := by
    filter_upwards [hV.mem_nhds hφV,hterminal] with ψ hψ ht
    exact sourceAngularBranchDirichletSine_sq_add_cosine_sq hp hp1 m δ ψ
      (hroots ψ hψ).1 (hroots ψ hψ).2 ht
  obtain ⟨ε,hε,hcoords⟩ := exists_analytic_parametricCosine_terminal_from_circle τ δ μ σ φ
    hτ (hδ φ hφV) hμ
    (analyticAt_sourceAngularBranchDirichletSine hp hp1 m δ W φ hφ
      (hδ φ hφV) (hroots φ hφV).1 hμ hμD hP) (hroots φ hφV).1 hcircle
  have hgood : ∀ᶠ ψ in 𝓝 φ, ψ ∈ V ∧ AnalyticAt ℂ ε ψ ∧
      μ ψ ∈ sourceStandardRootOmittedDomain hp hp1 ψ m ∧
      sourceAngularBranchCosinePoint hp hp1 m δ (ε ψ,ψ) = μ ψ ∧ Complex.sin (ε ψ) = σ ψ := by
    filter_upwards [hV.mem_nhds hφV,hε.eventually_analyticAt,hterminal,hcoords] with ψ hv he ht hc
    exact ⟨hv,he,ht,hc⟩
  obtain ⟨U,hUsub,hU,hφU⟩ := _root_.mem_nhds_iff.mp hgood
  refine ⟨U,hU,hφU,(fun ψ hψ => hVW (hUsub hψ).1),δ,ε,
    hδ.mono (fun ψ hψ => (hUsub hψ).1),(fun ψ hψ => (hUsub hψ).2.1),hbase,?_⟩
  intro ψ hψ
  obtain ⟨hv,_,ht,hpoint,hsin⟩ := hUsub hψ
  exact ⟨(hroots ψ hv).1,(hroots ψ hv).2,hpoint,hsin,
    sourceAngularBranchCosineRoot_eq_dirichlet_anti hp hp1 m δ ψ (ε ψ)
      (hroots ψ hv).1 ht hpoint hsin⟩

end NLS.ZakharovShabat
