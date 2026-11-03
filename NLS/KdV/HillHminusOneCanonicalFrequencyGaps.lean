import NLS.KdV.HillHminusOneCriticalPoints
import NLS.ZakharovShabat.CanonicalWeightedGapSummability
import NLS.ZakharovShabat.UniformCanonicalPeriodicEndpoints
import NLS.SequenceSpaces.HolderEmbedding

/-! # Genuine summable frequency gaps on a rough Miura chart

The actual analytic Miura lift supplies the L2 source budget. The gap
sequence is the difference of the actual canonical endpoint displacements,
and its pointwise square is an l1 sequence. No real-form assumption is used.
-/
noncomputable section
open Set Metric Complex Filter Topology NLS.ZakharovShabat
namespace NLS.KdV
namespace HillHminusMiuraChart

def frequencyPotential (C : HillHminusMiuraChart) (q : PeriodOneHminusOne) : PairSpace 2 :=
  periodOnePotential (C.criticalSource q)

theorem analyticOnNhd_frequencyPotential (C : HillHminusMiuraChart) :
    AnalyticOnNhd ℂ C.frequencyPotential C.domain := by
  intro q hq
  exact ((periodOnePotential (p := 2)).analyticAt _).comp (C.analyticOnNhd_criticalSource q hq)

theorem frequencyPotential_even (C : HillHminusMiuraChart) (q : PeriodOneHminusOne) :
    C.frequencyPotential q ∈ pairParitySubspace 0 := periodOnePotential_mem _

def canonicalLeft (C : HillHminusMiuraChart) (q : PeriodOneHminusOne) (n : ℤ) : ℂ :=
  canonicalPeriodicLeft (by simp) (by norm_num) (C.frequencyPotential q) (C.frequencyPotential_even q) n

def canonicalRight (C : HillHminusMiuraChart) (q : PeriodOneHminusOne) (n : ℤ) : ℂ :=
  canonicalPeriodicRight (by simp) (by norm_num) (C.frequencyPotential q) (C.frequencyPotential_even q) n

def canonicalFrequencyGap (C : HillHminusMiuraChart) (q : PeriodOneHminusOne) : NLS.Coeff 2 :=
  canonicalPeriodicRightDisplacement (by simp) (by norm_num) (C.frequencyPotential q) (C.frequencyPotential_even q)-
    canonicalPeriodicLeftDisplacement (by simp) (by norm_num) (C.frequencyPotential q) (C.frequencyPotential_even q)

def canonicalFrequencyGapSquares (C : HillHminusMiuraChart) (q : PeriodOneHminusOne) : NLS.Coeff 1 :=
  NLS.Coeff.holderProduct (C.canonicalFrequencyGap q) (C.canonicalFrequencyGap q)

theorem canonicalFrequencyGapSquares_apply (C : HillHminusMiuraChart)
    (q : PeriodOneHminusOne) (n : ℤ) :
    C.canonicalFrequencyGapSquares q n = (C.canonicalRight q n-C.canonicalLeft q n)^2 := by
  simp only [canonicalFrequencyGapSquares,NLS.Coeff.holderProduct_apply,canonicalFrequencyGap,
    lp.coeFn_sub,Pi.sub_apply,canonicalPeriodicRightDisplacement_apply,
    canonicalPeriodicLeftDisplacement_apply,canonicalRight,canonicalLeft]
  ring

/-- One rough-open neighborhood gives both the genuine l1 norm bound and
the actual canonical pair at every sufficiently high signed index. -/
theorem exists_bounded_canonical_frequency_gaps (C : HillHminusMiuraChart)
    (q0 : PeriodOneHminusOne) (hq0 : q0 ∈ C.domain) :
    ∃ M : ℕ, ∃ U : Set PeriodOneHminusOne, ∃ B : ℝ,
      0 < M ∧ U ⊆ C.domain ∧ IsOpen U ∧ q0 ∈ U ∧ 0 ≤ B ∧
      ∀ q ∈ U, ‖C.canonicalFrequencyGapSquares q‖ ≤ B ∧
        ∀ n : ℤ, M ≤ n.natAbs → PeriodicEndpointPair (by simp) (C.frequencyPotential q) n
          (C.canonicalLeft q n) (C.canonicalRight q n) := by
  obtain ⟨Wb,hWb,_,hqb,_,R,hR,hbound⟩ :=
    exists_uniform_bounded_canonicalPeriodicDisplacements (by simp) (by norm_num) (C.frequencyPotential q0)
  obtain ⟨N,_,We,hWe,_,hqe,_,hlabels⟩ := exists_uniform_canonicalPeriodicEndpoints
    (by simp) (by norm_num) SpectralWeight.one (unitBaseEquiv.symm (C.frequencyPotential q0))
  let f : PeriodOneHminusOne → WeightedCoeffPair SpectralWeight.one.toWeight 2 :=
    fun q => unitBaseEquiv.symm (C.frequencyPotential q)
  let U : Set PeriodOneHminusOne := C.domain ∩
    (C.frequencyPotential ⁻¹' Wb ∩ f ⁻¹' We)
  have hf : AnalyticOnNhd ℂ f C.domain := by
    intro q hq
    exact (unitBaseEquiv.symm.toContinuousLinearMap.analyticAt _).comp
      (C.analyticOnNhd_frequencyPotential q hq)
  have hU : IsOpen U := by
    rw [show U = (C.domain ∩ C.frequencyPotential ⁻¹' Wb) ∩ (C.domain ∩ f ⁻¹' We) by aesop]
    exact (C.analyticOnNhd_frequencyPotential.continuousOn.isOpen_inter_preimage C.domain_open hWb).inter
      (hf.continuousOn.isOpen_inter_preimage C.domain_open hWe)
  have hbase (q : PeriodOneHminusOne) : weightedBaseToPair SpectralWeight.one (f q) = C.frequencyPotential q := by
    rw [← unitBaseEquiv_eq,ContinuousLinearEquiv.apply_symm_apply]
  refine ⟨N+1,U,(2*R)^2,by omega,fun _ hq => hq.1,hU,⟨hq0,hqb,hqe⟩,sq_nonneg _,?_⟩
  intro q hq
  constructor
  · have hg : ‖C.canonicalFrequencyGap q‖ ≤ 2*R := by
      have hh := hbound _ hq.2.1 (C.frequencyPotential_even q)
      exact (norm_sub_le _ _).trans (by linarith [hh.1,hh.2])
    exact (NLS.Coeff.norm_holderProduct_le _ _).trans
      (by simpa only [pow_two] using mul_self_le_mul_self (norm_nonneg _) hg)
  · intro n hn
    have heven : weightedBaseToPair SpectralWeight.one (f q) ∈ pairParitySubspace 0 := by
      rw [hbase]
      exact C.frequencyPotential_even q
    have hl := (hlabels (f q) hq.2.2 heven N le_rfl).distant n (by omega)
    simpa only [hbase,canonicalLeft,canonicalRight] using hl

end HillHminusMiuraChart
end NLS.KdV
