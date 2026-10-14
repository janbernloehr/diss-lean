import NLS.ZakharovShabat.SourceCriticalGapCommonIsolation
import NLS.ZakharovShabat.SourceDeletedPairJointAnalytic
import NLS.ZakharovShabat.SourceLemma10_5

/-!
# Analytic critical-gap coefficients on the unchanged common domain

The critical root lies in its original isolating disk, where the deleted
periodic product is nonzero. Composing that product and its spectral
derivative with the critical-root graph makes the gap-free quotient
analytic at every complex source in the common domain, even at collapsed
gaps. Every finite block consequently has a common local bound.
-/

noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Every coordinate of the actual quotient is analytic throughout the retained common domain. -/
theorem SourceLemma10_5Data.analyticAt_criticalGapQuotient
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (h : SourceLemma10_5Data hp hp1 W) (φ : CoeffPair p) (hφ : φ ∈ W)
    (n : ℤ) :
    AnalyticAt ℂ (fun ψ : CoeffPair p =>
      canonicalCriticalGapQuotient hp hp1
        (periodOnePotential ψ) (periodOnePotential_mem ψ) n) φ := by
  let c (ψ : CoeffPair p) := canonicalCriticalPoints hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ) n
  let τ (ψ : CoeffPair p) := canonicalPeriodicMidpoint hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ) n
  let P (ψ : CoeffPair p) := canonicalDeletedPeriodicProduct hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ) n (c ψ)
  let d (ψ : CoeffPair p) := canonicalDeletedCriticalDerivative hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ) n
  let C (ψ : CoeffPair p) := canonicalCriticalOffsetCoefficient hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ) n
  have hc : AnalyticAt ℂ c φ := (h.roots.symmetric.simplicity.critical φ hφ n).1
  have hτ : AnalyticAt ℂ τ φ := h.roots.symmetric.midpoint n φ hφ
  obtain ⟨hDopen,hO⟩ := h.joint n
  have hPjoint := sourceDeletedPairJointProduct_analyticOnNhd_of_omitted
    hp hp1 W n hDopen hO
  have hdjoint := sourceDeletedPairJointSpectralDerivative_analyticOnNhd_of_omitted
    hp hp1 W n hDopen hO
  obtain ⟨V,_,_,hφV,_,D,k,hD⟩ := h.neighborhoods φ hφ
  have hcdisc : c φ ∈ D n :=
    hD.cluster φ hφV n (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
  have hcdomain : c φ ∈ sourceStandardRootOmittedDomain hp hp1 φ n :=
    hD.toSourceIsolatingNeighborhoods.disk_subset_omittedDomain φ hφV n hcdisc
  have hpoint : (c φ,φ) ∈ sourceStandardRootOmittedJointDomain hp hp1 W n :=
    ⟨hφ,hcdomain⟩
  have hmap : AnalyticAt ℂ (fun ψ : CoeffPair p => (c ψ,ψ)) φ :=
    hc.prod analyticAt_id
  have hP : AnalyticAt ℂ P φ := by
    exact (hPjoint (c φ,φ) hpoint).comp
      (f := fun ψ : CoeffPair p => (c ψ,ψ)) hmap
  have hd : AnalyticAt ℂ d φ := by
    exact (hdjoint (c φ,φ) hpoint).comp
      (f := fun ψ : CoeffPair p => (c ψ,ψ)) hmap
  have hC : AnalyticAt ℂ C φ := by
    have heq : C = (fun ψ : CoeffPair p =>
        2*P ψ+(c ψ-τ ψ)*d ψ) := by
      funext ψ
      simp only [C,canonicalCriticalOffsetCoefficient,
        canonicalCriticalMidpointOffset_apply,P,c,τ,d]
    rw [heq]
    exact (analyticAt_const.mul hP).add ((hc.sub hτ).mul hd)
  have hCne : C φ ≠ 0 :=
    hD.toSourceIsolatingNeighborhoods.criticalOffsetCoefficient_ne_zero φ hφV n
  change AnalyticAt ℂ (fun ψ : CoeffPair p => d ψ/(4*C ψ)) φ
  exact hd.div (analyticAt_const.mul hC)
    (mul_ne_zero (by norm_num) hCne)

/-- Any finite block of critical squared-gap quotients has one
common local source neighborhood and one finite coefficient bound. -/
theorem SourceLemma10_5Data.uniform_criticalGapQuotient_finiteBlock
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (h : SourceLemma10_5Data hp hp1 W) (φ : CoeffPair p) (hφ : φ ∈ W)
    (s : Finset ℤ) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∃ B : ℝ, 0 ≤ B ∧ ∀ ψ ∈ V, ∀ n ∈ s,
        ‖canonicalCriticalGapQuotient hp hp1
          (periodOnePotential ψ) (periodOnePotential_mem ψ) n‖ ≤ B := by
  let q (ψ : CoeffPair p) (n : ℤ) :=
    canonicalCriticalGapQuotient hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ) n
  have hnear : ∀ᶠ ψ : CoeffPair p in 𝓝 φ,
      ∀ n ∈ s, ‖q ψ n‖ ≤ ‖q φ n‖+1 := by
    rw [Finset.eventually_all]
    intro n hn
    have hcont : ContinuousAt (fun ψ : CoeffPair p => ‖q ψ n‖) φ :=
      (h.analyticAt_criticalGapQuotient φ hφ n).continuousAt.norm
    have hlt : ‖q φ n‖ < ‖q φ n‖+1 := by linarith
    filter_upwards [hcont.eventually (gt_mem_nhds hlt)] with ψ hψ
    exact hψ.le
  obtain ⟨V,hVsub,hVopen,hφV⟩ := _root_.mem_nhds_iff.mp hnear
  let B : ℝ := ∑ n ∈ s, (‖q φ n‖+1)
  have hB : 0 ≤ B := Finset.sum_nonneg (fun n _ => by positivity)
  refine ⟨V,hVopen,hφV,B,hB,?_⟩
  intro ψ hψ n hn
  calc
    ‖q ψ n‖ ≤ ‖q φ n‖+1 := hVsub hψ n hn
    _ ≤ B := Finset.single_le_sum (f := fun k => ‖q φ k‖+1)
      (fun k _ => by positivity) hn

end NLS.ZakharovShabat
