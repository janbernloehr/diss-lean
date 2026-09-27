import NLS.ZakharovShabat.SourceCriticalPointsAnalytic
import NLS.ZakharovShabat.CanonicalCriticalStability
import NLS.ZakharovShabat.RealCriticalSimplicity

/-!
# A common neighborhood of simple critical roots

At a real-type source every critical root is simple. The uniform
critical-point labeling preserves simplicity outside one finite
index block on a common complex neighborhood. Joint continuity of the
second spectral derivative preserves it on the remaining finite block.
-/

noncomputable section
open Set Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- All canonical critical roots remain simple on one open complex
source neighborhood of a real-type potential. -/
theorem exists_local_source_allCanonicalCriticalPoints_simple
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ)) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∀ ψ ∈ V, ∀ n : ℤ,
        deriv (deriv (canonicalDiscriminant hp (periodOnePotential ψ)))
          (canonicalCriticalPoints hp hp1 (periodOnePotential ψ)
            (periodOnePotential_mem ψ) n) ≠ 0 := by
  let c (n : ℤ) (ψ : CoeffPair p) := canonicalCriticalPoints hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ) n
  let G : ℂ × CoeffPair p → ℂ := fun t =>
    deriv (canonicalDiscriminant hp (periodOnePotential t.2)) t.1
  have hG : AnalyticOnNhd ℂ G univ :=
    analyticOnNhd_sourceDiscriminantDerivative_joint hp hp1
  have hsecond : Continuous (fun t : ℂ × CoeffPair p =>
      deriv (deriv (canonicalDiscriminant hp (periodOnePotential t.2))) t.1) := by
    have h := continuousOn_spectral_deriv_of_analyticOnNhd
      G univ isOpen_univ hG
    exact continuousOn_univ.mp h
  let P : CoeffPair p →L[ℂ] pairParitySubspace (p := p) 0 :=
    (periodOnePotential (p := p)).codRestrict _ periodOnePotential_mem
  obtain ⟨N,_,hlabel⟩ := exists_eventually_canonicalCriticalLabeling
    hp hp1 (P φ)
  have hlabelSource : ∀ᶠ ψ : CoeffPair p in 𝓝 φ,
      CriticalPointLabeling hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) N (c · ψ) := by
    exact P.continuous.continuousAt.eventually hlabel
  have hfinite : ∀ᶠ ψ : CoeffPair p in 𝓝 φ,
      ∀ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        deriv (deriv (canonicalDiscriminant hp (periodOnePotential ψ)))
          (c n ψ) ≠ 0 := by
    rw [Finset.eventually_all]
    intro n hn
    have hc : ContinuousAt (c n) φ :=
      (analyticAt_sourceCanonicalCriticalPoint_of_realType hp hp1 n φ hreal).continuousAt
    have hmap : ContinuousAt (fun ψ : CoeffPair p => (c n ψ,ψ)) φ :=
      hc.prodMk continuousAt_id
    have hcont : ContinuousAt (fun ψ : CoeffPair p =>
        deriv (deriv (canonicalDiscriminant hp (periodOnePotential ψ)))
          (c n ψ)) φ := hsecond.continuousAt.comp
            (f := fun ψ : CoeffPair p => (c n ψ,ψ)) hmap
    have hbase := discriminant_second_derivative_ne_zero_at_critical_of_realType
      hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ)
      (isRealType_periodOnePotential φ hreal) (c n φ)
      (canonicalCriticalPoints_is_critical hp hp1
        (periodOnePotential φ) (periodOnePotential_mem φ) n)
    exact hcont.eventually_ne hbase
  have hall : ∀ᶠ ψ : CoeffPair p in 𝓝 φ, ∀ n : ℤ,
      deriv (deriv (canonicalDiscriminant hp (periodOnePotential ψ)))
        (c n ψ) ≠ 0 := by
    filter_upwards [hlabelSource,hfinite] with ψ hψlabel hψfinite n
    by_cases hn : n.natAbs ≤ N
    · exact hψfinite n (by simp only [Finset.mem_Icc]; omega)
    · have horder := (hψlabel.distant n (lt_of_not_ge hn)).2.2.1
      have hanalytic := (analyticOnNhd_discriminant_derivative hp hp1
        (periodOnePotential ψ) (periodOnePotential_mem ψ))
          (c n ψ) (mem_univ _)
      have hderivOrder :
          analyticOrderAt
            (deriv (deriv (canonicalDiscriminant hp (periodOnePotential ψ))))
            (c n ψ) = 0 :=
        analyticOrderAt_deriv_of_pos hanalytic (n := 0)
          (by simpa using horder)
      intro hzero
      exact (hanalytic.deriv.analyticOrderAt_ne_zero.mpr hzero) hderivOrder
  obtain ⟨V,hVsub,hVopen,hφV⟩ := mem_nhds_iff.mp hall
  exact ⟨V,hVopen,hφV,fun ψ hψ n => hVsub hψ n⟩

end NLS.ZakharovShabat
