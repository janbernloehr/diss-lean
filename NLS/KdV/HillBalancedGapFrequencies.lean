import NLS.KdV.HillMiuraEnergyGapCoordinates
import NLS.KdV.MiuraCanonicalRootReflection
import NLS.ZakharovShabat.SourceGapSampleSummability

/-! Balanced signed frequencies of ANY full original real Hill gap
sample sequence. The zero mode is zero, opposite modes are negatives,
and every frequency lies in its ACTUAL signed Miura gap. Thus the
frequency displacement is l2 and every signed entry is distinct. -/
noncomputable section
open Set Complex NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.KdV

def hillBalancedGapFrequency (σ : ℕ+ → ℝ) (c : ℝ) (k : ℤ) : ℂ :=
  if hk : 0 < k then energyFrequency (c:ℂ) (σ ⟨k.toNat,by omega⟩:ℂ)
  else if hk' : k < 0 then -energyFrequency (c:ℂ) (σ ⟨(-k).toNat,by omega⟩:ℂ)
  else 0

theorem hillBalancedGapFrequency_zero (σ : ℕ+ → ℝ) (c : ℝ) : hillBalancedGapFrequency σ c 0 = 0 := by
  simp only [hillBalancedGapFrequency,lt_self_iff_false,↓reduceDIte]

theorem hillBalancedGapFrequency_neg (σ : ℕ+ → ℝ) (c : ℝ) (k : ℤ) :
    hillBalancedGapFrequency σ c (-k) = -hillBalancedGapFrequency σ c k := by
  rcases lt_trichotomy k 0 with hk | hk | hk
  · have hn : 0 < -k := by omega
    have hp : ¬ 0 < k := by omega
    simp only [hillBalancedGapFrequency,dif_pos hn,dif_neg hp,dif_pos hk,neg_neg]
  · subst k
    rw [neg_zero,hillBalancedGapFrequency_zero,neg_zero]
  · have hn : -k < 0 := by omega
    have hp : ¬ 0 < -k := by omega
    simp only [hillBalancedGapFrequency,dif_neg hp,dif_pos hn,dif_pos hk,neg_neg]

theorem hillBalancedGapFrequency_pos (σ : ℕ+ → ℝ) (c : ℝ) (m : ℕ+) :
    hillBalancedGapFrequency σ c ((m:ℕ):ℤ) = energyFrequency (c:ℂ) (σ m:ℂ) := by
  have hm : 0 < ((m:ℕ):ℤ) := by exact_mod_cast m.pos
  have hindex : (⟨(((m:ℕ):ℤ)).toNat,by omega⟩:ℕ+) = m := by apply Subtype.ext; rfl
  simp only [hillBalancedGapFrequency,dif_pos hm,hindex]

theorem hillBalancedGapFrequency_pos_sq (σ : ℕ+ → ℝ) (c : ℝ) (m : ℕ+) :
    (hillBalancedGapFrequency σ c ((m:ℕ):ℤ))^2-(c:ℂ) = (σ m:ℂ) := by
  rw [hillBalancedGapFrequency_pos,energyFrequency_sq]
  ring

theorem hillBalancedGapFrequency_mem_segment
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q) (u : PeriodOneRealL2) (c : ℝ)
    (hi : periodOneMiura u.val = q+periodOneL2Inclusion (lp.single 2 0 (c:ℂ)))
    (hc : -(c:ℂ) ∉ singularHillSpectrum (periodOneOriginal q)) (σ : ℕ+ → ℝ)
    (hσ : ∀ m : ℕ+, σ m ∈ Icc (hillHminusLabels q hq (2*(m:ℕ)-1)) (hillHminusLabels q hq (2*(m:ℕ))))
    (k : ℤ) : hillBalancedGapFrequency σ c k ∈
      sourcePeriodicSegment (by norm_num) (by norm_num) (hillMiuraDiagonal u.val) k := by
  have hpositive (j : ℤ) (hj : 0 < j) : hillBalancedGapFrequency σ c j ∈
      sourcePeriodicSegment (by norm_num) (by norm_num) (hillMiuraDiagonal u.val) j := by
    let m : ℕ+ := ⟨j.toNat,by omega⟩
    have hindex : ((m:ℕ):ℤ) = j := by
      change ((j.toNat:ℕ):ℤ) = j
      exact Int.toNat_of_nonneg hj.le
    have h := (hillMiura_frequency_of_original_gap q hq u c hi hc m (σ m) (hσ m)).2.1
    rw [← hillBalancedGapFrequency_pos σ c m,hindex] at h
    exact h
  rcases lt_trichotomy k 0 with hk | hk | hk
  · have h := hpositive (-k) (by omega)
    have hn := ((sourcePeriodicReflection_hillMiuraDiagonal u.val).neg_mem_segment_iff (-k)
      (hillBalancedGapFrequency σ c (-k))).mpr h
    simpa only [neg_neg,hillBalancedGapFrequency_neg] using hn
  · subst k
    rw [hillBalancedGapFrequency_zero]
    simpa only [Complex.ofReal_zero] using sourcePeriodicSegment_mem_of_realIcc
      (by norm_num) (by norm_num) (hillMiuraDiagonal u.val) (hillMiuraRealSource u).property 0 0
      (hillMiura_gap_zero_contains_zero u)
  · exact hpositive k hk

theorem memlp_hillBalancedGapFrequency_displacement
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q) (u : PeriodOneRealL2) (c : ℝ)
    (hi : periodOneMiura u.val = q+periodOneL2Inclusion (lp.single 2 0 (c:ℂ)))
    (hc : -(c:ℂ) ∉ singularHillSpectrum (periodOneOriginal q)) (σ : ℕ+ → ℝ)
    (hσ : ∀ m : ℕ+, σ m ∈ Icc (hillHminusLabels q hq (2*(m:ℕ)-1)) (hillHminusLabels q hq (2*(m:ℕ)))) :
    Memℓp (fun k : ℤ => hillBalancedGapFrequency σ c k-(Real.pi:ℂ)*k) 2 :=
  memℓp_sourcePeriodicSegment_samples (by norm_num) (by norm_num) (hillMiuraDiagonal u.val) _
    (hillBalancedGapFrequency_mem_segment q hq u c hi hc σ hσ)

theorem hillBalancedGapFrequency_injective
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q) (u : PeriodOneRealL2) (c : ℝ)
    (hi : periodOneMiura u.val = q+periodOneL2Inclusion (lp.single 2 0 (c:ℂ)))
    (hc : -(c:ℂ) ∉ singularHillSpectrum (periodOneOriginal q)) (σ : ℕ+ → ℝ)
    (hσ : ∀ m : ℕ+, σ m ∈ Icc (hillHminusLabels q hq (2*(m:ℕ)-1)) (hillHminusLabels q hq (2*(m:ℕ)))) :
    Function.Injective (hillBalancedGapFrequency σ c) := by
  intro i j he
  by_contra hne
  have hI := sourcePeriodicSegment_re_mem_Icc (by norm_num) (by norm_num) (hillMiuraDiagonal u.val) i _
    (hillBalancedGapFrequency_mem_segment q hq u c hi hc σ hσ i)
  have hJ := sourcePeriodicSegment_re_mem_Icc (by norm_num) (by norm_num) (hillMiuraDiagonal u.val) j _
    (hillBalancedGapFrequency_mem_segment q hq u c hi hc σ hσ j)
  rcases lt_or_gt_of_ne hne with hij | hji
  · have hs := canonicalPeriodicRight_re_lt_left_of_lt (by norm_num) (by norm_num)
      (periodOnePotential (hillMiuraDiagonal u.val)) (periodOnePotential_mem _)
      (isRealType_periodOnePotential _ (hillMiuraRealSource u).property) hij
    rw [he] at hI
    exact (not_lt_of_ge (hJ.1.trans hI.2)) hs
  · have hs := canonicalPeriodicRight_re_lt_left_of_lt (by norm_num) (by norm_num)
      (periodOnePotential (hillMiuraDiagonal u.val)) (periodOnePotential_mem _)
      (isRealType_periodOnePotential _ (hillMiuraRealSource u).property) hji
    rw [he] at hI
    exact (not_lt_of_ge (hI.1.trans hJ.2)) hs

end NLS.KdV
