import NLS.ZakharovShabat.SourceFiniteGapSobolev
import NLS.ZakharovShabat.ExponentSourcePotentials

/-! # Physical H¹ realizations of real finite-gap sources

The Sobolev bootstrap supplies square-summable weighted coefficients both
before and after period doubling. These give compatible Hilbert sources
and operator-domain representatives without additional regularity assumptions.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual period-two realization of every finite-gap source is H¹. -/
theorem sourceFiniteGap_physical_mem_H1
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceLocus p)
    (hfinite : φ ∈ sourceFiniteGapLocus hp hp1) :
    Memℓp (fun n => (Weight.sobolev 1 n : ℂ)*Coeff.periodDouble φ.val.fst n) 2 ∧
    Memℓp (fun n => (Weight.sobolev 1 n : ℂ)*Coeff.periodDouble φ.val.snd n) 2 := by
  have h := sourceFiniteGap_physical_mem_sobolev hp hp1 φ hfinite 2 (by norm_num)
  have hembed (a : Coeff p) (ha : Memℓp (fun n => (Weight.sobolev 2 n : ℂ)*a n) p) :
      Memℓp (fun n => (Weight.sobolev 1 n : ℂ)*a n) 2 := by
    let b : WeightedCoeff (Weight.sobolev 1) p := ⟨fun n => (Weight.sobolev 1 n : ℂ)*a n, by
      change Memℓp (fun n => (Weight.sobolev 1 n : ℂ)*((Weight.sobolev 1 n : ℂ)*a n)) p
      simpa only [show (2 : ℝ) = 1+1 by norm_num,Weight.sobolev_add,Complex.ofReal_mul,mul_assoc] using ha⟩
    have hb := (WeightedCoeff.sobolevToL1CLM p hp b).property.of_exponent_ge (show (1 : ℝ≥0∞) ≤ 2 by norm_num)
    change Memℓp (fun n => WeightedCoeff.sobolevToL1CLM p hp b n) 2 at hb
    simpa only [WeightedCoeff.sobolevToL1CLM_apply] using hb
  exact ⟨hembed _ h.1,hembed _ h.2⟩

/-- A finite-gap source above the Hilbert exponent has a coefficient-preserving
real Hilbert preimage with a physical H¹ representative. -/
theorem sourceFiniteGap_exists_hilbert_realization
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (φ : realTypeSourceLocus p) (hfinite : φ ∈ sourceFiniteGapLocus hp hp1) :
    ∃ ψ : CoeffPair 2, CoeffPair.exponentInclusion h2p ψ = φ.val ∧
      IsRealType (CoeffPair.toMax 2 ψ) ∧ ∃ a : Domain 2,
        periodOnePotential ψ = domainInclusion a := by
  have h := sourceFiniteGap_mem_H1 hp hp1 φ hfinite
  let u : ScalarDomain 2 := ⟨fun n => φ.val.fst n,h.1⟩
  let v : ScalarDomain 2 := ⟨fun n => φ.val.snd n,h.2⟩
  let ψ : CoeffPair 2 := WithLp.toLp 2 (scalarInclusion u,scalarInclusion v)
  have he : CoeffPair.exponentInclusion h2p ψ = φ.val := by
    apply (CoeffPair.toMax p).injective
    apply Prod.ext <;> ext n <;> exact scalarInclusion_apply _ _
  have hr : IsRealType (CoeffPair.toMax 2 ψ) := by
    intro n
    change scalarInclusion v n = starRingEnd ℂ (scalarInclusion u (-n))
    rw [scalarInclusion_apply,scalarInclusion_apply]
    exact φ.property n
  have hphys := sourceFiniteGap_physical_mem_H1 hp hp1 φ hfinite
  let a : Domain 2 := (⟨fun n => Coeff.periodDouble φ.val.fst n,hphys.1⟩,
    ⟨fun n => Coeff.periodDouble φ.val.snd n,hphys.2⟩)
  refine ⟨ψ,he,hr,a,?_⟩
  have hd := periodOnePotential_exponent h2p ψ
  rw [he] at hd
  apply Prod.ext <;> ext n
  · have hn := congrArg (fun x : PairSpace p => x.1 n) hd
    change Coeff.periodDouble ψ.fst n = scalarInclusion a.1 n
    rw [scalarInclusion_apply]
    exact hn
  · have hn := congrArg (fun x : PairSpace p => x.2 n) hd
    change Coeff.periodDouble ψ.snd n = scalarInclusion a.2 n
    rw [scalarInclusion_apply]
    exact hn

end NLS.ZakharovShabat
