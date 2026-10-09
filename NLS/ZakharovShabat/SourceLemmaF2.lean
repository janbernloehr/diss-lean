import NLS.ZakharovShabat.SourceAbelianEndpointIntegrals

/-! # Lemma F.2: analyticity of the endpoint-averaged primitive

One complex source neighborhood works for all signed gaps and every
point of the corresponding isolating boundary. The function is the
literal average of improper endpoint integrals. No nonzero-gap or
continuous choice of lexicographic endpoint labels is assumed.
-/
noncomputable section
open Set Metric Filter Topology Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

namespace SourceFullAbelianUniformCauchyFamily
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
variable (C : SourceFullAbelianUniformCauchyFamily hp hp1 W)

/-- Analyticity at every fixed spectral point avoiding the cuts on the source ball. -/
theorem endpointAverage_analytic (n : ℤ) (ν : ℂ)
    (hν : ∀ ψ ∈ ball C.discs.source.val C.discs.sourceRadius,
      ν ∈ sourceCanonicalRootDomain hp hp1 ψ) :
    AnalyticOnNhd ℂ (sourceAbelianEndpointAverage hp hp1 n ν)
      (ball C.discs.source.val C.discs.sourceRadius) := by
  intro ψ hψ
  have hf := (C.full_analytic n (ν,ψ) ⟨hψ,hν ψ hψ⟩).comp
    (f := fun χ : CoeffPair p => (ν,χ)) (analyticAt_const.prod analyticAt_id)
  apply hf.congr
  filter_upwards [isOpen_ball.mem_nhds hψ] with χ hχ
  exact (C.endpointAverage_eq χ hχ n ν (hν χ hχ)).symm

/-- The entire isolating boundary is allowed, with the same source ball for every point. -/
theorem sourceLemmaF2 (n : ℤ) (ν : ℂ)
    (hν : ν ∈ sphere (C.discs.center n) (C.discs.outer n)) :
    AnalyticOnNhd ℂ (sourceAbelianEndpointAverage hp hp1 n ν)
      (ball C.discs.source.val C.discs.sourceRadius) :=
  C.endpointAverage_analytic n ν (fun ψ hψ => C.circle_root n ψ hψ ν hν)

end SourceFullAbelianUniformCauchyFamily

/-- F.2 on a single connected almost-real domain. Every complex base point
has one source neighborhood and an isolating family working for all indices
and all boundary points, including when the selected gap is collapsed. -/
theorem sourceLemmaF2 (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W V : Set (CoeffPair p), IsOpen V ∧ IsConnected V ∧ realTypeSourceLocus p ⊆ V ∧ V ⊆ W ∧
      ∀ φ ∈ V, ∃ C : SourceFullAbelianUniformCauchyFamily hp hp1 W, ∃ r : ℝ,
        0 < r ∧ ball φ r ⊆ V ∧ ball φ r ⊆ ball C.discs.source.val C.discs.sourceRadius ∧
        ∀ n : ℤ, ∀ ν ∈ sphere (C.discs.center n) (C.discs.outer n),
          AnalyticOnNhd ℂ (sourceAbelianEndpointAverage hp hp1 n ν) (ball φ r) ∧
          ∀ ψ ∈ ball φ r,
            sourceAbelianEndpointAverage hp hp1 n ν ψ = sourceFullAbelianPrimitive hp hp1 W n (ν,ψ) := by
  obtain ⟨W,_,_,hfamilies⟩ := exists_sourceFullAbelianUniformCauchyFamilies hp hp1
  choose C hC using hfamilies
  let U : Set (CoeffPair p) := ⋃ φ : realTypeSourceSubmodule p,
    ball (C φ).discs.source.val (C φ).discs.sourceRadius
  have hU : IsOpen U := isOpen_iUnion (fun _ => isOpen_ball)
  have hrU : realTypeSourceLocus p ⊆ U := by
    intro φ hφ
    apply mem_iUnion.mpr
    refine ⟨⟨φ,hφ⟩,?_⟩
    rw [hC]
    exact mem_ball_self (C ⟨φ,hφ⟩).discs.sourceRadius_pos
  let V := connectedComponentIn U (0 : CoeffPair p)
  have h0 : (0 : CoeffPair p) ∈ realTypeSourceLocus p := by simp [realTypeSourceLocus]
  have hrV : realTypeSourceLocus p ⊆ V :=
    isConnected_realTypeSourceLocus.isPreconnected.subset_connectedComponentIn h0 hrU
  have hVU : V ⊆ U := connectedComponentIn_subset U 0
  have hV : IsOpen V := hU.connectedComponentIn
  have hVW : V ⊆ W := by
    intro ψ hψ
    obtain ⟨φ,hφ⟩ := mem_iUnion.mp (hVU hψ)
    exact (C φ).discs.source_subset hφ
  refine ⟨W,V,hV,isConnected_connectedComponentIn_iff.mpr (hrU h0),hrV,hVW,?_⟩
  intro ψ hψ
  obtain ⟨φ,hφ⟩ := mem_iUnion.mp (hVU hψ)
  obtain ⟨r,hr,hsub⟩ := Metric.mem_nhds_iff.mp ((hV.inter isOpen_ball).mem_nhds ⟨hψ,hφ⟩)
  refine ⟨C φ,r,hr,fun χ hχ => (hsub hχ).1,fun χ hχ => (hsub hχ).2,?_⟩
  intro n ν hν
  exact ⟨((C φ).sourceLemmaF2 n ν hν).mono (fun χ hχ => (hsub hχ).2),fun χ hχ =>
    (C φ).endpointAverage_eq χ (hsub hχ).2 n ν ((C φ).circle_root n χ (hsub hχ).2 ν hν)⟩

/-- The actual endpoint average has the exact free normalization, including negative n. -/
theorem sourceAbelianEndpointAverage_zero (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (ν : ℂ)
    (hν : ν ∈ sourceCanonicalRootDomain hp hp1 (0 : CoeffPair p)) :
    sourceAbelianEndpointAverage hp hp1 n ν (0 : CoeffPair p) =
      -Complex.I*ν+Complex.I*(Real.pi:ℂ)*n := by
  obtain ⟨W,_,_,hfamilies⟩ := exists_sourceFullAbelianUniformCauchyFamilies hp hp1
  obtain ⟨C,hC⟩ := hfamilies (0 : realTypeSourceSubmodule p)
  have h0 : (0 : CoeffPair p) ∈ ball C.discs.source.val C.discs.sourceRadius := by
    rw [hC]
    exact mem_ball_self C.discs.sourceRadius_pos
  obtain ⟨E⟩ := C.charts 0 h0
  rw [C.endpointAverage_eq 0 h0 n ν hν,sourceFullAbelianPrimitive_zero E]

end NLS.ZakharovShabat
