import NLS.ZakharovShabat.SourceFloquetMultiplier
import NLS.ZakharovShabat.CanonicalPeriodicLevels
import NLS.ComplexAnalysis.QuadraticRootPrimitive

/-! # The canonical multiplier at periodic endpoints

The square identity forces the canonical root to tend to zero along
all approaches off the cuts, including at collapsed gaps. Consequently
the multiplier tends to the signed endpoint value fixed by the index.
-/
noncomputable section
open Set Filter Topology Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Parity sign of the discriminant level at a signed periodic gap. -/
def sourceAbelianGapSign (n : ℤ) : ℂ := if n % 2 = 0 then 1 else -1

@[simp] theorem sourceAbelianGapSign_sq (n : ℤ) : sourceAbelianGapSign n ^ 2 = 1 := by
  unfold sourceAbelianGapSign
  split <;> norm_num

@[simp] theorem norm_sourceAbelianGapSign (n : ℤ) : ‖sourceAbelianGapSign n‖ = 1 := by
  unfold sourceAbelianGapSign
  split <;> simp

theorem sourceAbelianGapSign_eq_neg_one_zpow (n : ℤ) : sourceAbelianGapSign n = (-1 : ℂ)^n := by
  rw [neg_one_zpow_eq_ite]
  simp only [sourceAbelianGapSign,Int.even_iff]

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem sourceDiscriminant_eq_two_gapSign_at_endpoint
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) (a : ℂ)
    (ha : a ∈ ({canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n,
      canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n} : Set ℂ)) :
    canonicalDiscriminant hp (periodOnePotential φ) a = 2*sourceAbelianGapSign n := by
  have he := canonicalPeriodicEndpoints_discriminant_of_realType hp hp1
    (periodOnePotential φ) (periodOnePotential_mem φ) (isRealType_periodOnePotential φ hφ) n
  have hlevel : canonicalDiscriminant hp (periodOnePotential φ) a = (if n % 2 = 0 then 2 else -2) := by
    rcases (by simpa only [mem_insert_iff,mem_singleton_iff] using ha) with rfl | rfl
    · exact he.1
    · exact he.2
  rw [hlevel,sourceAbelianGapSign]
  split <;> norm_num

/-- Full relative endpoint limit, independent of the sign of the root
and of whether the selected gap is open. -/
theorem sourceCanonicalRoot_tendsto_zero_at_periodicEndpoint
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) (a : ℂ)
    (ha : a ∈ ({canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n,
      canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n} : Set ℂ)) :
    Tendsto (sourceCanonicalRoot hp hp1 φ) (𝓝[sourceCanonicalRootDomain hp hp1 φ] a) (𝓝 0) := by
  apply tendsto_zero_of_sq_tendsto_zero
  have hd := (analyticOnNhd_canonicalDiscriminant hp hp1 _ (periodOnePotential_mem φ) a
    (mem_univ a)).continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (s := sourceCanonicalRootDomain hp hp1 φ))
  have hs : canonicalDiscriminant hp (periodOnePotential φ) a ^ 2 - 4 = 0 := by
    rw [sourceDiscriminant_eq_two_gapSign_at_endpoint hp hp1 φ hφ n a ha,mul_pow,sourceAbelianGapSign_sq]
    norm_num
  have hlim : Tendsto (fun z => canonicalDiscriminant hp (periodOnePotential φ) z ^ 2 - 4)
      (𝓝[sourceCanonicalRootDomain hp hp1 φ] a) (𝓝 0) := by
    simpa only [hs] using (hd.pow 2).sub_const 4
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact (sourceCanonicalRoot_sq_eq_discriminant_sq_sub_four hp hp1 φ z hz).symm

/-- The multiplier approaches `(-1)^n` from every side of either endpoint. -/
theorem sourceFloquetMultiplier_tendsto_at_periodicEndpoint
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) (a : ℂ)
    (ha : a ∈ ({canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n,
      canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n} : Set ℂ)) :
    Tendsto (sourceFloquetMultiplier hp hp1 φ)
      (𝓝[sourceCanonicalRootDomain hp hp1 φ] a) (𝓝 (sourceAbelianGapSign n)) := by
  have hd := (analyticOnNhd_canonicalDiscriminant hp hp1 _ (periodOnePotential_mem φ) a
    (mem_univ a)).continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (s := sourceCanonicalRootDomain hp hp1 φ))
  have hr := sourceCanonicalRoot_tendsto_zero_at_periodicEndpoint hp hp1 φ hφ n a ha
  simpa only [sourceFloquetMultiplier,sourceDiscriminant_eq_two_gapSign_at_endpoint hp hp1 φ hφ n a ha,
    add_zero,mul_div_cancel_left₀ _ (by norm_num : (2 : ℂ) ≠ 0)] using! (hd.add hr).div_const 2

end NLS.ZakharovShabat
