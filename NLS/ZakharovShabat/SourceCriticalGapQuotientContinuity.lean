import NLS.ZakharovShabat.SourceDeletedPairJointAnalytic
import NLS.ZakharovShabat.SourceCriticalOffsetCoefficientNonzero
import NLS.ZakharovShabat.SourceClusterDiscsLocal

/-!
# Continuity of fixed-index squared-gap critical coefficients

Near a real-type source, the critical root and periodic midpoint are
continuous. The deleted periodic product and its spectral derivative
are jointly continuous on an isolating disc, while the midpoint
coefficient is nonzero. Thus each fixed-index squared-gap quotient
is continuous and locally bounded, including at a collapsed gap.
-/

noncomputable section
open Set Metric Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Every point of an assigned source isolating disc avoids all
unomitted gap segments. -/
theorem sourceIsolatingDisc_subset_omittedDomain
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ ψ : CoeffPair p) (N : ℕ) (ε : ℝ)
    (hcluster : ∀ m : ℤ, sourceSpectralCluster hp hp1 ψ m ⊆
      sourceIsolatingDisc hp hp1 φ N ε m)
    (hdisjoint : ∀ i j : ℤ, i ≠ j →
      Disjoint (sourceIsolatingDisc hp hp1 φ N ε i)
        (sourceIsolatingDisc hp hp1 φ N ε j))
    (n : ℤ) :
    sourceIsolatingDisc hp hp1 φ N ε n ⊆
      sourceStandardRootOmittedDomain hp hp1 ψ n := by
  intro z hz m hmn hmseg
  have hseg := sourcePeriodicSegment_subset_isolatingDisc
    hp hp1 φ ψ N ε m (hcluster m) hmseg
  exact Set.disjoint_left.mp (hdisjoint n m (Ne.symm hmn)) hz hseg

/-- Each fixed-index coefficient in the critical squared-gap formula
is continuous at a real-type base source. -/
theorem continuousAt_sourceCriticalGapQuotient_of_realType
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (n : ℤ) :
    ContinuousAt (fun ψ : CoeffPair p =>
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
  let F : CoeffPair p →L[ℂ] pairParitySubspace (p := p) 0 :=
    (periodOnePotential (p := p)).codRestrict _ periodOnePotential_mem
  have hc : ContinuousAt c φ := by
    exact (continuousAt_canonicalCriticalPoints_of_realType hp hp1 (F φ)
      (isRealType_periodOnePotential φ hφ) n).comp F.continuous.continuousAt
  have hL := continuousAt_canonicalPeriodicLeft_periodOne_of_realType hp hp1 φ hφ n
  have hR := continuousAt_canonicalPeriodicRight_periodOne_of_realType hp hp1 φ hφ n
  have hτ : ContinuousAt τ φ := by
    change ContinuousAt (fun ψ : CoeffPair p =>
      (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n +
        canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)/2) φ
    exact (hL.add hR).div_const 2
  obtain ⟨W,_,_,hreal,hWdata⟩ := exists_global_sourceDeletedPairJointAnalytic hp hp1
  obtain ⟨hDopen,hPanalytic,hDcont⟩ := hWdata n
  have hφW : φ ∈ W := hreal hφ
  obtain ⟨N,ε,_,_,U,_,_,hφU,hcluster,hdisjoint⟩ :=
    exists_local_source_connected_isolating_discs hp hp1 φ hφ
  have hcdisc : c φ ∈ sourceIsolatingDisc hp hp1 φ N ε n :=
    hcluster φ hφU n (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
  have hcdomain : c φ ∈ sourceStandardRootOmittedDomain hp hp1 φ n :=
    sourceIsolatingDisc_subset_omittedDomain hp hp1 φ φ N ε
      (hcluster φ hφU) hdisjoint n hcdisc
  have hpoint : (c φ,φ) ∈ sourceStandardRootOmittedJointDomain hp hp1 W n :=
    ⟨hφW,hcdomain⟩
  have hmap : ContinuousAt (fun ψ : CoeffPair p => (c ψ,ψ)) φ :=
    hc.prodMk continuousAt_id
  have hPcont : ContinuousAt P φ := by
    have h := (hPanalytic.continuousOn.continuousAt
      (hDopen.mem_nhds hpoint)).comp
        (f := fun ψ : CoeffPair p => (c ψ,ψ)) hmap
    change ContinuousAt P φ at h
    exact h
  have hdcont : ContinuousAt d φ := by
    have h := (hDcont.continuousAt (hDopen.mem_nhds hpoint)).comp
      (f := fun ψ : CoeffPair p => (c ψ,ψ)) hmap
    change ContinuousAt d φ at h
    exact h
  have hCcont : ContinuousAt C φ := by
    have heq : C = (fun ψ : CoeffPair p => 2*P ψ+(c ψ-τ ψ)*d ψ) := by
      funext ψ
      simp only [C,canonicalCriticalOffsetCoefficient,
        canonicalCriticalMidpointOffset_apply,P,c,τ,d]
    rw [heq]
    exact (continuousAt_const.mul hPcont).add ((hc.sub hτ).mul hdcont)
  have hCne : C φ ≠ 0 :=
    sourceCriticalOffsetCoefficient_ne_zero_of_isolating hp hp1 φ φ N ε
      (hcluster φ hφU) hdisjoint n
  change ContinuousAt (fun ψ : CoeffPair p => d ψ/(4*C ψ)) φ
  exact hdcont.div (continuousAt_const.mul hCcont)
    (mul_ne_zero (by norm_num) hCne)

/-- Any finite block of critical squared-gap quotients has one
common local source neighborhood and one finite coefficient bound. -/
theorem exists_local_uniform_sourceCriticalGapQuotient_finiteBlock
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
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
      (continuousAt_sourceCriticalGapQuotient_of_realType hp hp1 φ hφ n).norm
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
