import NLS.KdV.ClassicalHillGapScaleBounds
import NLS.KdV.ClassicalSpectralEmbedding
import NLS.ZakharovShabat.CanonicalWeightedGapSummability
import NLS.SequenceSpaces.HolderEmbedding

/-! # An actual locally bounded l1 majorant for frequency-scale Hill gaps

This controls the energy squared gap divided by the square of its index.
It makes no assertion that the unscaled energy gaps belong to l2.
-/
noncomputable section
open Set Metric Complex NLS.LinearVolterra NLS.ZakharovShabat
namespace NLS.KdV

def classicalHillCanonicalFrequencyGap (q : Curve ℂ) : NLS.Coeff 2 :=
  canonicalPeriodicRightDisplacement (by simp) (by norm_num) (classicalHillCoefficientPotential q)
    (classicalHillCoefficientPotential_even q)-
  canonicalPeriodicLeftDisplacement (by simp) (by norm_num) (classicalHillCoefficientPotential q)
    (classicalHillCoefficientPotential_even q)

def classicalHillCanonicalFrequencyGapSquares (q : Curve ℂ) : NLS.Coeff 1 :=
  NLS.Coeff.holderProduct (classicalHillCanonicalFrequencyGap q) (classicalHillCanonicalFrequencyGap q)

theorem classicalHillCanonicalFrequencyGapSquares_apply (q : Curve ℂ) (j : ℤ) :
    classicalHillCanonicalFrequencyGapSquares q j =
      (canonicalPeriodicGap (by simp) (by norm_num) (classicalHillCoefficientPotential q)
        (classicalHillCoefficientPotential_even q) j)^2 := by
  simp only [classicalHillCanonicalFrequencyGapSquares,NLS.Coeff.holderProduct_apply,
    classicalHillCanonicalFrequencyGap,lp.coeFn_sub,Pi.sub_apply,
    canonicalPeriodicRightDisplacement_apply,canonicalPeriodicLeftDisplacement_apply,
    canonicalPeriodicGap]
  ring

theorem classicalHill_squaredGap_scale_le_periodicSquaredGap
    (q : Curve ℂ) (N : ℕ)
    (hcount : PeriodicCountingData (by simp) (classicalHillCoefficientPotential q) N)
    (k : ℕ+) (hk : N < (k : ℕ)) :
    ‖classicalHillHighSquaredGap q k‖/(k : ℕ)^2 ≤
      (16*Real.pi^2)*‖periodicSquaredGap (by simp) (classicalHillCoefficientPotential q) (k : ℤ)‖ := by
  have hk' : N < (k : ℤ).natAbs := by simpa using hk
  obtain ⟨a,b,hset,_⟩ := hcount.disk_eigenvalue_pair (k : ℤ) hk'
  have hmem (z : ℂ) (hz : z = a ∨ z = b) :
      z ∈ ball ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4) := by
    have hh : z ∈ enclosedPeriodicSpectrum (by simp) (classicalHillCoefficientPotential q)
        ((Real.pi : ℂ)*(k : ℤ)) (Real.pi/4) := by rw [hset];simpa using hz
    simpa using ((mem_enclosedPeriodicSpectrum (by simp) _ _ _ _).mp hh).2
  have ha : ‖a-(Real.pi : ℂ)*(k : ℕ)‖ ≤ Real.pi/4 := (mem_ball_iff_norm.mp (hmem a (Or.inl rfl))).le
  have hb : ‖b-(Real.pi : ℂ)*(k : ℕ)‖ ≤ Real.pi/4 := (mem_ball_iff_norm.mp (hmem b (Or.inr rfl))).le
  have hmid := norm_complex_midpoint_sub_le a b
    ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4) ha hb
  have he := (hcount.midpoint_squaredGap_eq_pair (k : ℤ) hk' a b hset).1
  have hnorm : ‖periodicMidpoint (by simp) (classicalHillCoefficientPotential q) (k : ℤ)‖ ≤
      2*Real.pi*(k : ℝ) := by
    rw [he]
    have ht := norm_add_le ((a+b)/2-(Real.pi : ℂ)*(k : ℕ)) ((Real.pi : ℂ)*(k : ℕ))
    rw [sub_add_cancel,norm_mul,Complex.norm_real,Real.norm_of_nonneg Real.pi_pos.le,Complex.norm_natCast] at ht
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast k.property
    nlinarith [Real.pi_pos]
  rw [classicalHillHighSquaredGap,norm_mul,norm_mul,norm_pow]
  norm_num only [Complex.norm_ofNat]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < (k : ℕ)^2)).mpr
  nlinarith [mul_le_mul_of_nonneg_right
    (mul_self_le_mul_self (norm_nonneg _) hnorm)
    (norm_nonneg (periodicSquaredGap (by simp) (classicalHillCoefficientPotential q) (k : ℤ)))]

/-- One actual l1 sequence with a locally uniform norm bound dominates
all sufficiently high frequency-scale energy squared gaps. -/
theorem exists_classicalHill_frequency_gap_majorant (q0 : Curve ℂ) :
    ∃ M : ℕ, ∃ U : Set (Curve ℂ), ∃ B : ℝ,
      0 < M ∧ IsOpen U ∧ q0 ∈ U ∧ 0 ≤ B ∧ ∀ q ∈ U,
        ‖classicalHillCanonicalFrequencyGapSquares q‖ ≤ B ∧
        ∀ k : ℕ+, M ≤ (k : ℕ) →
          ‖classicalHillHighSquaredGap q k‖/(k : ℕ)^2 ≤
            (16*Real.pi^2)*‖classicalHillCanonicalFrequencyGapSquares q (k : ℤ)‖ := by
  obtain ⟨Nc,Wc,hNc,hWc,hqc,hcount⟩ := exists_classicalHillCounting_near_compact {q0} isCompact_singleton
  obtain ⟨Wb,hWb,_,hqb,_,R,hR,hbound⟩ :=
    exists_uniform_bounded_canonicalPeriodicDisplacements (by simp) (by norm_num)
      (classicalHillCoefficientPotential q0)
  obtain ⟨Ne,_,We,hWe,hqe,heq⟩ := exists_uniform_canonical_squaredGap_eq (by simp) (by norm_num)
    SpectralWeight.one (unitBaseEquiv.symm (classicalHillCoefficientPotential q0))
  let U := Wc ∩ (classicalHillCoefficientPotential ⁻¹' Wb ∩
    ((fun q : Curve ℂ => unitBaseEquiv.symm (classicalHillCoefficientPotential q)) ⁻¹' We))
  let M := max Nc Ne+1
  have hbase (q : Curve ℂ) : weightedBaseToPair SpectralWeight.one
      (unitBaseEquiv.symm (classicalHillCoefficientPotential q)) = classicalHillCoefficientPotential q := by
    rw [← unitBaseEquiv_eq,ContinuousLinearEquiv.apply_symm_apply]
  refine ⟨M,U,(2*R)^2,by dsimp only [M];omega,
    hWc.inter ((hWb.preimage continuous_classicalHillCoefficientPotential).inter
      (hWe.preimage (unitBaseEquiv.symm.continuous.comp continuous_classicalHillCoefficientPotential))),
    ⟨hqc (mem_singleton q0),hqb,hqe⟩,sq_nonneg _,?_⟩
  intro q hq
  constructor
  · have hg : ‖classicalHillCanonicalFrequencyGap q‖ ≤ 2*R := by
      have hh := hbound _ hq.2.1 (classicalHillCoefficientPotential_even q)
      exact (norm_sub_le _ _).trans (by linarith [hh.1,hh.2])
    exact (NLS.Coeff.norm_holderProduct_le _ _).trans (by simpa only [pow_two] using mul_self_le_mul_self (norm_nonneg _) hg)
  · intro k hk
    have hnc : Nc < (k : ℕ) := by dsimp only [M] at hk;omega
    have hne : Ne < (k : ℤ).natAbs := by dsimp only [M] at hk;simp only [Int.natAbs_natCast];omega
    have heven : weightedBaseToPair SpectralWeight.one
        (unitBaseEquiv.symm (classicalHillCoefficientPotential q)) ∈ pairParitySubspace 0 := by
      rw [hbase]
      exact classicalHillCoefficientPotential_even q
    have he := heq _ hq.2.2 heven (k : ℤ) hne
    simp only [hbase] at he
    rw [classicalHillCanonicalFrequencyGapSquares_apply]
    rw [← he]
    exact classicalHill_squaredGap_scale_le_periodicSquaredGap q Nc (hcount q hq.1 Nc le_rfl) k hnc

end NLS.KdV
