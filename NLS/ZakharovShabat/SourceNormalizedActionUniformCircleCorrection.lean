import NLS.ZakharovShabat.SourceNormalizedActionFactorDiscMajorants
import NLS.ZakharovShabat.SourceCriticalGapQuotientUniform

/-!
# A uniform complex correction estimate on distant circles

The fixed free-centered circles simultaneously enclose all sufficiently
distant periodic gaps near a real-type source. Combining their geometry
with local bounds for the critical squared-gap quotient and deleted
factor makes the normalized contour quotient's correction uniformly
proportional to the squared periodic gap.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)]

/-- One complex source neighborhood and one index cutoff give a
common correction constant for the normalized-action candidate on
all distant free-centered eighth-π circles. The estimate includes
complex sources with collapsed selected gaps. -/
theorem exists_local_sourceNormalizedAction_uniform_circle_correction
    [Fact (1 ≤ q)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (hq1 : 1 < q) (hq : q ≠ ⊤)
    (hhalf : ENNReal.ofReal (p.toReal/2) ≤ q)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∃ K : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ ψ ∈ V,
        ∀ n : ℤ, K ≤ n.natAbs →
          ‖sourceNormalizedActionCircleCandidate hp hp1 n
              ((Real.pi:ℂ)*n) (Real.pi/8) ψ -
            I * sourceCriticalRootRatioExtension hp hp1 n ψ
              (sourceStandardRootMidpoint hp hp1 ψ n) / 4‖ ≤
            C * ‖(sourcePeriodicGapDisplacement hp hp1 ψ n)^2‖ := by
  obtain ⟨Kg,Vg,hVgopen,hφVg,hgeom⟩ :=
    exists_local_sourceNormalizedAction_uniform_tail_circle_data hp hp1 φ hφ
  obtain ⟨Vb,hVbopen,hφVb,M,hM,hB⟩ :=
    exists_local_uniform_sourceCriticalGapQuotient hp hp1 φ hφ
  obtain ⟨Ve,hVeopen,hφVe,Ke,Le,hEbound⟩ :=
    exists_local_sourceNormalizedAction_factor_circle_uniform_bound
      hp hp1 hq1 hq hhalf φ hφ
  let V := (Vg ∩ Vb) ∩ Ve
  let K := max Kg Ke
  let a : ℝ := Real.pi/16
  let L : ℝ := max 0 Le
  let C : ℝ := 2*(Real.pi/8)*
    (2/a^3 + M/a^2 + 2*M^2/a)*L
  have ha : 0 < a := by dsimp [a]; positivity
  have hL : 0 ≤ L := le_max_left _ _
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨V,(hVgopen.inter hVbopen).inter hVeopen,
    ⟨⟨hφVg,hφVb⟩,hφVe⟩,K,C,hC,?_⟩
  intro ψ hψ n hn
  have hKg : Kg ≤ n.natAbs := le_trans (le_max_left _ _) hn
  have hKe : Ke ≤ n.natAbs := le_trans (le_max_right _ _) hn
  obtain ⟨hseg,_,hE,hsep,hq⟩ := hgeom ψ hψ.1.1 n hKg
  let c : ℂ := (Real.pi:ℂ)*n
  let R : ℝ := Real.pi/8
  let τ := sourceStandardRootMidpoint hp hp1 ψ n
  let g := (sourcePeriodicGapDisplacement hp hp1 ψ n)^2
  let B := canonicalCriticalGapQuotient hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ) n
  let E := sourceCriticalRootRatioExtension hp hp1 n ψ
  have hR : 0 < R := by dsimp [R]; positivity
  have hτ : τ ∈ ball c R :=
    hseg (sourcePeriodicMidpoint_mem_segment hp hp1 ψ n)
  have hBpoint : ‖B‖ ≤ M := by
    have hpoint := lp.norm_apply_le_norm (zero_lt_one.trans hp1).ne'
      (sourceCriticalGapQuotient hp hp1 ψ) n
    have hBapply : ‖B‖ ≤ ‖sourceCriticalGapQuotient hp hp1 ψ‖ := by
      simpa only [B,sourceCriticalGapQuotient_apply] using hpoint
    exact hBapply.trans (hB ψ hψ.1.2).1
  have hLpoint : ∀ z ∈ sphere c R, ‖E z‖ ≤ L := by
    intro z hz
    exact (hEbound ψ hψ.2 n hKe z hz).trans (le_max_right _ _)
  have hrootEq (z : ℂ) :
      sourceStandardRoot hp hp1 ψ n z = normalizedStandardRoot τ g z := by
    simp only [sourceStandardRoot, τ, g, sourceStandardRootMidpoint,
      sourcePeriodicGapDisplacement_apply]
  have hzseg (z : ℂ) (hz : z ∈ sphere c R) :
      z ∉ sourcePeriodicSegment hp hp1 ψ n := by
    intro hzs
    have hzball := hseg hzs
    exact (ne_of_lt (mem_ball.mp hzball)) (mem_sphere.mp hz)
  have hroot : ∀ z ∈ sphere c R,
      AnalyticAt ℂ (normalizedStandardRoot τ g) z := by
    intro z hz
    have hfun : normalizedStandardRoot τ g = sourceStandardRoot hp hp1 ψ n := by
      funext t
      exact (hrootEq t).symm
    rw [hfun]
    exact sourceStandardRoot_analyticAt hp hp1 ψ n z (hzseg z hz)
  have hden : ∀ z ∈ sphere c R,
      τ ≠ z ∧ normalizedStandardRoot τ g z ≠ 0 ∧
        τ-z+normalizedStandardRoot τ g z ≠ 0 := by
    intro z hz
    have hτz : τ ≠ z := by
      intro he
      exact hzseg z hz (he.symm ▸ sourcePeriodicMidpoint_mem_segment hp hp1 ψ n)
    have hw : normalizedStandardRoot τ g z ≠ 0 := by
      rw [← hrootEq]
      exact sourceStandardRoot_ne_zero_off_segment hp hp1 ψ n z (hzseg z hz)
    exact ⟨hτz,hw,normalizedStandardRoot_add_ne_zero τ g z hτz⟩
  have hbound := norm_normalizedActionCircleQuotient_sub_midpoint_le
    τ g B c R E hR hτ hE hroot hden a M L ha hsep hq hBpoint hLpoint
  change ‖normalizedActionCircleQuotient τ g B c R E - I*E τ/4‖ ≤
    C*‖g‖
  calc
    _ ≤ 2*R*‖g‖ * (2/a^3 + M/a^2 + 2*M^2/a) * L := hbound
    _ = C*‖g‖ := by dsimp [C,R]; ring

end NLS.ZakharovShabat
