import NLS.ZakharovShabat.AppendixFCollapsedPath
import NLS.ComplexAnalysis.ParametricIntervalIntegralAnalytic

/-!
# Analytic extension of the collapsed-gap restriction

The regular χ_n segment integral is analytic for all nearby potentials,
including open gaps. On the collapsed-gap locus it equals the literal
endpoint average. This supplies a full Banach analytic extension of the
restriction used in the second step of Appendix F.
-/

noncomputable section
open Set Metric Filter Topology Complex MeasureTheory NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceFullAbelianUniformCauchyFamily
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W S : Set (CoeffPair p)}
variable (C : SourceFullAbelianUniformCauchyFamily hp hp1 W)

/-- The regular χ_n segment formula is analytic on the entire common source neighborhood. -/
theorem appendixF_regular_chi_integral_analytic
    (H : SourceCorollary10_6Data hp hp1 S) (hS : IsOpen S) (n : ℤ)
    (ν : ℂ) (hν : ν ∈ closedBall (C.discs.center n) (C.discs.outer n)) :
    let τ := fun ψ : CoeffPair p => canonicalPeriodicMidpoint hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ) n
    AnalyticOnNhd ℂ (fun ψ => -Complex.I*(ν-τ ψ)*∫ t in (0:ℝ)..1,
      sourceActionChi hp hp1 n ψ (τ ψ+(t:ℂ)*(ν-τ ψ)))
      (ball C.discs.source.val C.discs.sourceRadius ∩ S) := by
  dsimp only
  let τ := fun ψ : CoeffPair p => canonicalPeriodicMidpoint hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ) n
  let Z : ℂ × CoeffPair p → ℂ := fun q => τ q.2+q.1*(ν-τ q.2)
  let G : ℂ × CoeffPair p → ℂ := fun q => sourceActionChi hp hp1 n q.2 (Z q)
  have hτ : AnalyticOnNhd ℂ τ S := H.roots.roots.symmetric.midpoint n
  have hGA (ψ : CoeffPair p)
      (hψ : ψ ∈ ball C.discs.source.val C.discs.sourceRadius ∩ S)
      (t : ℝ) (ht : t ∈ uIcc (0:ℝ) 1) : AnalyticAt ℂ G ((t:ℂ),ψ) := by
    have hτD : τ ψ ∈ closedBall (C.discs.center n) (C.discs.outer n) :=
      ball_subset_closedBall (C.segment_subset_outer n ψ hψ.1
        (sourcePeriodicMidpoint_mem_segment hp hp1 ψ n))
    have hZD : Z ((t:ℂ),ψ) ∈ closedBall (C.discs.center n) (C.discs.outer n) := by
      have h := (convex_closedBall (C.discs.center n) (C.discs.outer n)).lineMap_mem hτD hν
        (show t ∈ Icc (0:ℝ) 1 by simpa only [uIcc_of_le zero_le_one] using ht)
      simpa only [Z,AffineMap.lineMap_apply_module',Complex.real_smul,add_comm] using h
    have hAτ : AnalyticAt ℂ (fun q : ℂ × CoeffPair p => τ q.2) ((t:ℂ),ψ) :=
      (hτ ψ hψ.2).comp (g := τ) (f := fun q : ℂ × CoeffPair p => q.2)
        (show AnalyticAt ℂ (fun q : ℂ × CoeffPair p => q.2) ((t:ℂ),ψ) from analyticAt_snd)
    have hAZ : AnalyticAt ℂ Z ((t:ℂ),ψ) :=
      hAτ.add (analyticAt_fst.mul (analyticAt_const.sub hAτ))
    exact (H.chi_joint hS n (Z ((t:ℂ),ψ),ψ)
      ⟨hψ.2,C.discs.avoids_other ψ hψ.1 n hZD⟩).comp
        (f := fun q : ℂ × CoeffPair p => (Z q,q.2)) (hAZ.prod analyticAt_snd)
  have hI := analyticOnNhd_intervalIntegral_of_jointAnalytic G
    (D := {q | AnalyticAt ℂ G q}) (isOpen_analyticAt ℂ G) (fun _ hq => hq) 0 1
    (isOpen_ball.inter hS) hGA
  exact (analyticOnNhd_const.mul (analyticOnNhd_const.sub (hτ.mono inter_subset_right))).mul hI

/-- The collapsed-gap restriction of the actual endpoint average has an analytic extension. -/
theorem appendixF_collapsed_average_analytic_extension
    (H : SourceLemma10_10Data hp hp1 S) (hS : IsOpen S) (n : ℤ)
    (ν : ℂ) (hν : ν ∈ sphere (C.discs.center n) (C.discs.outer n)) :
    ∃ G : CoeffPair p → ℂ,
      AnalyticOnNhd ℂ G (ball C.discs.source.val C.discs.sourceRadius ∩ S) ∧
      ∀ ψ ∈ ball C.discs.source.val C.discs.sourceRadius ∩ S,
        canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n = 0 →
          G ψ = sourceAbelianEndpointAverage hp hp1 n ν ψ := by
  refine ⟨fun ψ => -Complex.I*(ν-canonicalPeriodicMidpoint hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ) n)*∫ t in (0:ℝ)..1,
      sourceActionChi hp hp1 n ψ (canonicalPeriodicMidpoint hp hp1
        (periodOnePotential ψ) (periodOnePotential_mem ψ) n+(t:ℂ)*
          (ν-canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)),
    C.appendixF_regular_chi_integral_analytic H.previous.previous.previous hS n ν
      (sphere_subset_closedBall hν),?_⟩
  intro ψ hψ hgap
  exact (C.appendixF_collapsed_average_segment H ψ hψ.2 hψ.1 n hgap ν
    (C.circle_root n ψ hψ.1 ν hν) (sphere_subset_closedBall hν)).symm

end SourceFullAbelianUniformCauchyFamily
end NLS.ZakharovShabat
