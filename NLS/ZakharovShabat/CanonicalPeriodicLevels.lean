import NLS.ZakharovShabat.RealPotentialPaths
import NLS.ZakharovShabat.CanonicalPeriodicFree
import NLS.ZakharovShabat.RealDiscriminantValues
import NLS.ComplexAnalysis.FiniteValueContinuity

/-!
# Discriminant levels of canonical ordered periodic endpoints

Along a real scaling path each canonical slot is continuous, and its
spectral membership forces the discriminant to take only the values 2 and
-2. Connectedness fixes that value to its free value, identifying the
parity level at every signed index, including the central cluster.
-/

noncomputable section
open Set Complex Filter Topology
open NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.ZakharovShabat

/-- The free discriminant alternates between its two levels at signed lattice centers. -/
theorem freeDiscriminant_int_pi (n : ℤ) :
    freeDiscriminant ((Real.pi : ℂ)*n) = (if n % 2 = 0 then 2 else -2) := by
  have he : (Real.pi : ℂ)*n = (((n : ℝ)*Real.pi : ℝ) : ℂ) := by simp [mul_comm]
  rw [freeDiscriminant, he, ← ofReal_cos, Real.cos_int_mul_pi, neg_one_zpow_eq_ite]
  by_cases hn : Even n
  · simp [hn,Int.even_iff.mp hn]
  · have hn' : n % 2 ≠ 0 := fun h => hn (Int.even_iff.mpr h)
    simp [hn,hn']

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The discriminant at each canonical slot has its index-parity level at every real-type potential. -/
theorem canonicalDiscriminant_canonicalPeriodicSlot_of_realType (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : pairParitySubspace (p := p) 0) (hφ : IsRealType φ.val) (k : ℤ ×ₗ Fin 2) :
    canonicalDiscriminant hp φ.val (canonicalPeriodicSlot hp hp1 φ.val φ.property k) =
      (if (ofLex k).1 % 2 = 0 then 2 else -2) := by
  let γ := realPotentialPath φ
  let f : ℝ → ℂ := fun t => canonicalDiscriminant hp (γ t).val
    (canonicalPeriodicSlot hp hp1 (γ t).val (γ t).property k)
  have hc : Continuous f := by
    have hd : Continuous (fun q : ℂ × pairParitySubspace (p := p) 0 => canonicalDiscriminant hp q.2.val q.1) :=
      continuousOn_univ.mp (analyticOnNhd_canonicalDiscriminant_joint hp hp1).continuousOn
    have hpair := (continuous_canonicalPeriodicSlot_realPotentialPath hp hp1 φ hφ k).prodMk
      (continuous_realPotentialPath φ)
    have hcomp := hd.comp hpair
    exact hcomp
  have hfin : (range f).Finite := by
    apply (Set.toFinite ({(2 : ℂ),-2} : Set ℂ)).subset
    rintro z ⟨t,rfl⟩
    have hs := (canonicalDiscriminant_sq_eq_four_iff_finite hp hp1 (γ t).val (γ t).property _).mpr
      (canonicalPeriodicSlot_mem_spectrum hp hp1 (γ t).val (γ t).property k)
    have hs' : (f t)^2 = (2 : ℂ)^2 := hs.trans (by norm_num)
    exact (sq_eq_sq_iff_eq_or_eq_neg.mp hs')
  have he := continuous_eq_of_finite_range f hc hfin 1 0
  have hfree : canonicalPeriodicSlot hp hp1 (0 : PairSpace p) (pairParitySubspace 0).zero_mem k =
      (Real.pi : ℂ)*(ofLex k).1 := by
    simp [canonicalPeriodicSlot,periodicEndpointSlot]
  simpa only [f,γ,realPotentialPath_one,realPotentialPath_zero,ZeroMemClass.coe_zero,hfree,
    canonicalDiscriminant_zero_finite,freeDiscriminant_int_pi] using he

/-- Both ordered endpoints have the same prescribed discriminant level at every real-type index. -/
theorem canonicalPeriodicEndpoints_discriminant_of_realType (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (heven : φ ∈ pairParitySubspace 0) (hreal : IsRealType φ) (n : ℤ) :
    canonicalDiscriminant hp φ (canonicalPeriodicLeft hp hp1 φ heven n) = (if n % 2 = 0 then 2 else -2) ∧
      canonicalDiscriminant hp φ (canonicalPeriodicRight hp hp1 φ heven n) = (if n % 2 = 0 then 2 else -2) := by
  constructor
  · exact canonicalDiscriminant_canonicalPeriodicSlot_of_realType hp hp1 ⟨φ,heven⟩ hreal (toLex (n,0))
  · exact canonicalDiscriminant_canonicalPeriodicSlot_of_realType hp hp1 ⟨φ,heven⟩ hreal (toLex (n,1))

end NLS.ZakharovShabat
