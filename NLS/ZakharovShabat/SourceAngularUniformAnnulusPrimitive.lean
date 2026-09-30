import NLS.ZakharovShabat.SourceAngularBetaCauchyAnalytic
import NLS.ZakharovShabat.SourceBoundaryDisplacementAnalytic
import NLS.ZakharovShabat.SourceNormalizedActionUniformTailCircles

/-!
# All angular annuli on one source neighborhood

The distant periodic segments and Dirichlet terminals lie inside free
eighth-pi discs on a common complex neighborhood. The original assigned
quarter-pi discs provide the exact periods and separation. A finite
intersection handles all remaining indices, so every selected gap has
a joint annular primitive chart on the same source neighborhood.
-/

noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

namespace SourceAngularJointAnnulusChartData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {m : ℤ}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}
  {W V : Set (CoeffPair p)} {c : ℤ → ℂ} {T : ℤ → ℝ} {r R : ℝ} {z₀ : ℂ}

/-- Restricting the source neighborhood preserves the actual chart and
every numerator's primitive, period, and spectral derivative. -/
theorem mono_source
    (D : SourceAngularJointAnnulusChartData hp hp1 m s W V c T r R z₀)
    (U : Set (CoeffPair p)) (hU : IsOpen U) (hUV : U ⊆ V) :
    SourceAngularJointAnnulusChartData hp hp1 m s W U c T r R z₀ where
  source_open := hU
  source_subset := hUV.trans D.source_subset
  inner_pos := D.inner_pos
  inner_lt_outer := D.inner_lt_outer
  outer_lt_assigned := D.outer_lt_assigned
  anchor_mem := D.anchor_mem
  disc_family := fun ψ hψ => D.disc_family ψ (hUV hψ)
  gap_enclosed := fun ψ hψ => D.gap_enclosed ψ (hUV hψ)
  terminal_enclosed := fun ψ hψ => D.terminal_enclosed ψ (hUV hψ)
  integrand_analytic := fun n => (D.integrand_analytic n).mono (prod_mono Subset.rfl hUV)
  selected_root_analytic := D.selected_root_analytic.mono (prod_mono Subset.rfl hUV)
  omitted_analytic := D.omitted_analytic.mono (prod_mono Subset.rfl hUV)
  period_zero := fun n hmn ψ hψ => D.period_zero n hmn ψ (hUV hψ)
  primitive_analytic := fun n => (D.primitive_analytic n).mono (prod_mono Subset.rfl hUV)
  primitive_anchor := D.primitive_anchor
  spectral_derivative := fun n hmn ψ hψ => D.spectral_derivative n hmn ψ (hUV hψ)

end SourceAngularJointAnnulusChartData

namespace SourcePsiIsolatingComplexExtension
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- One source neighborhood supports all selected gap charts. Only a
finite set of their neighborhoods is intersected: the distant charts
have fixed inner and outer radii inside their original assigned discs. -/
theorem exists_local_joint_angular_annulus_primitives_allIndices
    (hs : SourcePsiIsolatingComplexExtension hp hp1 W₀ s)
    (W : Set (CoeffPair p)) (hW : IsOpen W) (hWW₀ : W ⊆ W₀)
    (hA : ∀ ψ ∈ W, ∀ k : ℤ,
      AnalyticAt ℂ (fun χ : CoeffPair p => canonicalPeriodicMidpoint hp hp1
        (periodOnePotential χ) (periodOnePotential_mem χ) k) ψ ∧
      AnalyticAt ℂ (fun χ : CoeffPair p => (canonicalPeriodicGap hp hp1
        (periodOnePotential χ) (periodOnePotential_mem χ) k)^2) ψ)
    (φ : CoeffPair p) (hφ : φ ∈ W) (hreal : IsRealType (CoeffPair.toMax p φ)) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧ V ⊆ W ∧
      ∀ m : ℤ, ∃ c : ℤ → ℂ, ∃ T : ℤ → ℝ, ∃ r R : ℝ, ∃ z₀ : ℂ,
        SourceAngularJointAnnulusChartData hp hp1 m s W V c T r R z₀ := by
  classical
  obtain ⟨δ,hδ,hballW,N,ε,_,hdiscs⟩ :=
    hs.exists_local_angular_assigned_disc_family ⟨φ,hreal⟩ W hW hφ
  let c := sourceIsolatingCenter hp hp1 φ N
  let T := sourceIsolatingRadius hp hp1 φ N ε
  obtain ⟨Kg,Vg,hVg,hφg,hgap⟩ := exists_local_sourcePeriodicMidpointGap_tiny_tail hp hp1 φ
  obtain ⟨Kμ,Vμ,hVμ,hφμ,hterminal⟩ := exists_local_sourceBoundaryRoots_small_tail hp hp1
    .dirichlet φ hreal (Real.pi/8) (by positivity)
  let K := max N (max Kg Kμ)
  have hlocal (m : ℤ) := hs.exists_local_joint_angular_annulus_primitives
    W hW hWW₀ hA φ hφ hreal m
  choose Vm cm Tm rm Rm zm hφm Dm using hlocal
  have hhead : ∀ᶠ ψ : CoeffPair p in 𝓝 φ,
      ∀ m ∈ Finset.Icc (-(K:ℤ)) (K:ℤ), ψ ∈ Vm m := by
    rw [Finset.eventually_all]
    intro m _
    exact (Dm m).source_open.mem_nhds (hφm m)
  obtain ⟨C,hCsub,hC,hφC⟩ := _root_.mem_nhds_iff.mp hhead
  let V := ((ball φ δ ∩ Vg) ∩ Vμ) ∩ C
  have hV : IsOpen V := ((isOpen_ball.inter hVg).inter hVμ).inter hC
  have hVW : V ⊆ W := fun ψ hψ => hballW hψ.1.1.1
  refine ⟨V,hV,⟨⟨⟨mem_ball_self hδ,hφg⟩,hφμ⟩,hφC⟩,hVW,?_⟩
  intro m
  by_cases hm : m.natAbs ≤ K
  · have hmhead : m ∈ Finset.Icc (-(K:ℤ)) (K:ℤ) := by
      simp only [Finset.mem_Icc]
      omega
    exact ⟨cm m,Tm m,rm m,Rm m,zm m,(Dm m).mono_source V hV
      (fun ψ hψ => hCsub hψ.2 m hmhead)⟩
  · have hmK : K < m.natAbs := lt_of_not_ge hm
    have hmN : N < m.natAbs := (le_max_left _ _).trans_lt hmK
    have hmKg : Kg ≤ m.natAbs := by dsimp only [K] at hmK; omega
    have hmKμ : Kμ < m.natAbs := by dsimp only [K] at hmK; omega
    have hc : c m = (Real.pi:ℂ)*m := by
      simp only [c,sourceIsolatingCenter,if_neg (not_le.mpr hmN)]
    have hT : T m = Real.pi/4 := by
      simp only [T,sourceIsolatingRadius,if_neg (not_le.mpr hmN)]
    let r := Real.pi/8
    let R := 3*Real.pi/16
    have hr : 0 < r := by dsimp only [r]; positivity
    have hrR : r < R := by dsimp only [r,R]; nlinarith [Real.pi_pos]
    have hRT : R < T m := by rw [hT]; dsimp only [R]; nlinarith [Real.pi_pos]
    let z₀ : ℂ := c m+((r+R)/2:ℝ)
    have hz₀ : z₀ ∈ ball (c m) R \ closedBall (c m) r := by
      have hdist : dist z₀ (c m) = (r+R)/2 := by
        simp only [z₀,dist_eq_norm,add_sub_cancel_left,Complex.norm_real,Real.norm_eq_abs]
        rw [abs_of_pos (by linarith)]
      exact ⟨mem_ball.mpr (by rw [hdist]; linarith),
        fun h => by have hle := mem_closedBall.mp h; rw [hdist] at hle; linarith⟩
    have hg (ψ : CoeffPair p) (hψ : ψ ∈ V) :
        sourcePeriodicSegment hp hp1 ψ m ⊆ ball (c m) r := by
      rw [hc]
      obtain ⟨hmid,hgapSmall⟩ := hgap ψ hψ.1.1.2 m hmKg
      exact sourcePeriodicSegment_subset_free_eighth_ball hp hp1 ψ m hmid hgapSmall
    have ht (ψ : CoeffPair p) (hψ : ψ ∈ V) :
        canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m ∈ ball (c m) r := by
      rw [hc]
      exact hterminal ψ hψ.1.2 m hmKμ
    exact ⟨c,T,r,R,z₀,hs.joint_angular_annulus_chart_of_geometry W hW hWW₀ hA V hV hVW
      m c T r R z₀ hr hrR hRT hz₀ (fun ψ hψ => hdiscs ψ hψ.1.1.1) hg ht⟩

end SourcePsiIsolatingComplexExtension
end NLS.ZakharovShabat
