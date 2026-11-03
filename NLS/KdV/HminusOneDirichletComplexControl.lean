import NLS.KdV.HminusOneDirichletCentralRoots
import NLS.KdV.HminusOneDirichletBranches
import NLS.ZakharovShabat.SquaredFrequencyOrder

/-! One actual central count and the fixed positive high branches control
the ENTIRE native complex Dirichlet spectrum, with its original index offset. -/
noncomputable section
open Set Complex Metric NLS.ZakharovShabat
open scoped Classical
namespace NLS.KdV

/-- Actual complex spectral data, constructed below without a supplied
central root list or scalar spectral count. -/
structure HillHminusDirichletComplexControl (q : PeriodOneHminusOne)
    (u : Coeff 2) (c : ℂ) (N : ℕ) : Prop where
  index_pos : 0 < N
  image : periodOneMiura u = q+periodOneL2Inclusion (lp.single 2 0 c)
  counting : AuxiliaryCountingData (by simp)
    (auxiliaryPeriodOnePotential (by simp) (by norm_num) (hillMiuraDiagonal u)).val
    (auxiliaryPeriodOnePotential (by simp) (by norm_num) (hillMiuraDiagonal u)).property N
  tail_disk : ∀ n : ℕ, N < n →
    hillMiuraDiracDirichlet u n ∈ ball ((Real.pi:ℂ)*n) (Real.pi/4)
  tail_multiplicity : ∀ n : ℕ, N < n →
    singularDirichletAlgebraicMultiplicity (periodOneOriginal q)
      (hillMiuraDirichletEnergy u c n) = 1

/-- Every literal complex shifted Miura representation has complete actual
central/high control at a sufficiently large cutoff. -/
theorem exists_hillHminusDirichletComplexControl
    (q : PeriodOneHminusOne) (u : Coeff 2) (c : ℂ)
    (hi : periodOneMiura u = q+periodOneL2Inclusion (lp.single 2 0 c)) :
    ∃ N : ℕ, HillHminusDirichletComplexControl q u c N := by
  obtain ⟨N₀,U,hN,_,_,hu,_,hc⟩ := exists_uniform_auxiliaryPeriodOneCountingData
    (by simp) (by norm_num) (hillMiuraDiagonal u)
  let P := auxiliaryPeriodOneDirichletPotential (by simp) (by norm_num) (hillMiuraDiagonal u)
  let K := BoundaryCondition.canonicalRootCutoff .dirichlet (by simp) (by norm_num) P.val P.property
  have hs := (BoundaryCondition.canonicalRoots_spec .dirichlet (by simp) (by norm_num)
    P.val P.property).1
  let N := max N₀ K
  have hNk : K ≤ N := le_max_right _ _
  have hN₀ : N₀ ≤ N := le_max_left _ _
  have hd (n : ℕ) (hn : N < n) :
      hillMiuraDiracDirichlet u n ∈ ball ((Real.pi:ℂ)*n) (Real.pi/4) ∧
      BoundaryCondition.auxiliaryAlgebraicMultiplicity .dirichlet (by simp)
        (auxiliaryPeriodOnePotential (by simp) (by norm_num) (hillMiuraDiagonal u)).val
        (auxiliaryPeriodOnePotential (by simp) (by norm_num) (hillMiuraDiagonal u)).property
        (hillMiuraDiracDirichlet u n) = 1 := by
    have hnK : K < (n:ℤ).natAbs := by simpa using lt_of_le_of_lt hNk hn
    have hd := hs.distant_spec (n:ℤ) hnK
    change hillMiuraDiracDirichlet u (n:ℤ) ∈
      ball ((Real.pi:ℂ)*(n:ℤ)) (Real.pi/4) ∧ _ at hd
    constructor
    · simpa only [Int.cast_natCast] using hd.1
    · rw [BoundaryCondition.auxiliaryAlgebraicMultiplicity_eq]
      exact hd.2
  refine ⟨N,lt_of_lt_of_le hN hN₀,hi,hc _ hu N hN₀,fun n hn => (hd n hn).1,?_⟩
  intro n hn
  have hz : hillMiuraDiracDirichlet u n ≠ 0 := by
    have hp := re_pos_of_mem_positive_frequencyDisk n (by omega)
      (hillMiuraDiracDirichlet u n) (hd n hn).1
    intro he
    rw [he] at hp
    exact (lt_irrefl 0) hp
  rw [hillMiuraDirichletEnergy,
    ← auxiliaryDirichletMultiplicity_eq_native_of_ne_zero q u c _ hi hz]
  exact (hd n hn).2

namespace HillHminusDirichletComplexControl
variable {q : PeriodOneHminusOne} {u : Coeff 2} {c : ℂ} {N : ℕ}
variable (h : HillHminusDirichletComplexControl q u c N)
include h

/-- A positive high disk contains exactly its fixed canonical auxiliary root. -/
theorem frequency_eq_canonical (n : ℕ) (hn : N < n) (z : ℂ)
    (hs : z ∈ BoundaryCondition.auxiliarySpectrum .dirichlet (by simp)
      (auxiliaryPeriodOnePotential (by simp) (by norm_num) (hillMiuraDiagonal u)).val
      (auxiliaryPeriodOnePotential (by simp) (by norm_num) (hillMiuraDiagonal u)).property)
    (hz : z ∈ ball ((Real.pi:ℂ)*n) (Real.pi/4)) :
    z = hillMiuraDiracDirichlet u n := by
  have hn' : N < (n:ℤ).natAbs := by simpa using hn
  have hd := (h.counting.eigenvalue_spec .dirichlet (n:ℤ) hn').1
  have hzmem := (BoundaryCondition.mem_auxiliaryEnclosedSpectrum .dirichlet (by simp)
    (auxiliaryPeriodOnePotential (by simp) (by norm_num) (hillMiuraDiagonal u)).val
    (auxiliaryPeriodOnePotential (by simp) (by norm_num) (hillMiuraDiagonal u)).property
    ((Real.pi:ℂ)*(n:ℤ)) z (Real.pi/4)).mpr ⟨hs,by simpa only [Int.cast_natCast] using hz⟩
  have hcanonical := (canonicalAuxiliaryPeriodOneRoots_exhaustive (by simp) (by norm_num)
    .dirichlet (hillMiuraDiagonal u) (hillMiuraDiracDirichlet u n)).mpr ⟨(n:ℤ),rfl⟩
  have hcmem := (BoundaryCondition.mem_auxiliaryEnclosedSpectrum .dirichlet (by simp)
    (auxiliaryPeriodOnePotential (by simp) (by norm_num) (hillMiuraDiagonal u)).val
    (auxiliaryPeriodOnePotential (by simp) (by norm_num) (hillMiuraDiagonal u)).property
    ((Real.pi:ℂ)*(n:ℤ)) (hillMiuraDiracDirichlet u n) (Real.pi/4)).mpr
      ⟨hcanonical,by simpa only [Int.cast_natCast] using h.tail_disk n hn⟩
  rw [hd,Finset.mem_singleton] at hzmem hcmem
  exact hzmem.trans hcmem.symm

/-- The ENTIRE native complex spectrum consists of precisely the actual
finite central set and the positive high branches at the SAME index. -/
theorem spectrum_iff (e : ℂ) :
    e ∈ singularDirichletSpectrum (periodOneOriginal q) ↔
      e ∈ hillHminusDirichletCentralSpectrum q u c N ∨
        ∃ n : ℕ, N < n ∧ e = hillMiuraDirichletEnergy u c n := by
  constructor
  · intro he
    obtain ⟨z,hsq,hre⟩ := exists_square_root_re_nonneg (e+c)
    have hD := (mem_singularDirichletSpectrum_source_iff q e).mp he
    have hchar : auxiliaryPeriodOneCharacteristic (by simp) (by norm_num) .dirichlet
        (hillMiuraDiagonal u) z = 0 := by
      rw [auxiliaryDirichlet_eq_mul_hillHminusDirichlet q u c z h.image,
        hsq,add_sub_cancel_right,hD,mul_zero]
    have hs := (auxiliaryPeriodOneCharacteristic_eq_zero_iff (by simp) (by norm_num)
      .dirichlet (hillMiuraDiagonal u) z).mp hchar
    rcases h.counting.spectrum_subset .dirichlet hs with hc | ht
    · left
      exact (mem_hillHminusDirichletCentralSpectrum q u c h.image N e).mpr
        ⟨he,z,hc,by change z^2-c = e; rw [hsq]; ring⟩
    · right
      obtain ⟨k,hk⟩ := mem_iUnion.mp ht
      obtain ⟨hn,hz⟩ := mem_iUnion.mp hk
      have hk0 : 0 ≤ k := by
        by_contra hkneg
        have hk' : (k:ℝ) ≤ -1 := by exact_mod_cast (show k ≤ -1 by omega)
        have hb := (abs_lt.mp (frequencyDisk_coordinate_bounds k z hz).1).2
        have hm := mul_le_mul_of_nonneg_left hk' Real.pi_pos.le
        nlinarith [Real.pi_pos]
      let n := k.toNat
      have hnk : (n:ℤ) = k := Int.toNat_of_nonneg hk0
      have hnN : N < n := by simpa only [← hnk,Int.natAbs_natCast] using hn
      have hz' : z ∈ ball ((Real.pi:ℂ)*n) (Real.pi/4) := by
        simpa only [← hnk,Int.cast_natCast] using hz
      have heq := h.frequency_eq_canonical n hnN z hs hz'
      refine ⟨n,hnN,?_⟩
      rw [hillMiuraDirichletEnergy,← heq,hsq]
      ring
  · rintro (he | ⟨n,hn,rfl⟩)
    · exact (Finset.mem_filter.mp he).2
    · exact (singularDirichletAlgebraicMultiplicity_pos_iff (periodOneOriginal q) _).mp
        (by rw [h.tail_multiplicity n hn]; omega)

/-- Every actual central energy strictly precedes every positive high energy
in real part; complex central values and all repetitions are included. -/
theorem central_re_lt_tail (e : ℂ) (he : e ∈ hillHminusDirichletCentralSpectrum q u c N)
    (n : ℕ) (hn : N < n) : e.re < (hillMiuraDirichletEnergy u c n).re := by
  obtain ⟨_,z,hz,rfl⟩ := (mem_hillHminusDirichletCentralSpectrum q u c h.image N e).mp he
  have ho := re_sq_central_lt_positive_frequencyDisk N n hn z
    (hillMiuraDiracDirichlet u n) hz (h.tail_disk n hn)
  simpa only [hillMiuraDirichletEnergy,Complex.sub_re] using sub_lt_sub_right ho c.re

/-- Positive high energies have strictly increasing real parts at ALL high
indices, not merely along an eventual subsequence. -/
theorem tail_re_lt (i j : ℕ) (hi : N < i) (hij : i < j) :
    (hillMiuraDirichletEnergy u c i).re < (hillMiuraDirichletEnergy u c j).re := by
  have ho := re_sq_lt_of_positive_frequencyDisks i j hij
    (hillMiuraDiracDirichlet u i) (hillMiuraDiracDirichlet u j)
      (h.tail_disk i hi) (h.tail_disk j (lt_trans hi hij))
  simpa only [hillMiuraDirichletEnergy,Complex.sub_re] using sub_lt_sub_right ho c.re

/-- The high branches cannot duplicate any central native energy. -/
theorem tail_not_mem_central (n : ℕ) (hn : N < n) :
    hillMiuraDirichletEnergy u c n ∉ hillHminusDirichletCentralSpectrum q u c N := by
  intro he
  exact (lt_irrefl _) (h.central_re_lt_tail _ he n hn)

end HillHminusDirichletComplexControl
end NLS.KdV
