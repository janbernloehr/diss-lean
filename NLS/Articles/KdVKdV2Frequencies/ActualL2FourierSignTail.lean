import NLS.Articles.KdVKdV2Frequencies.ActualL2OriginalFourierIdentification
import NLS.KdV.HillL2FourierSignOverlap
import NLS.KdV.HillNativeL2PhysicalSource
import NLS.ComplexAnalysis.LocallyEventualEquality

/-! Every actual ORIGINAL L2 chart has the SAME eventual Fourier
orientation as the zero chart, by actual overlap bounds and connectedness. -/
noncomputable section
open Set Complex Filter Topology NLS.KdV
open scoped ENNReal ComplexConjugate
namespace NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData

def fixedFourierSigns (D : GlobalRoughAbelianForwardData) : ℤ → Bool :=
  (D.chart ⟨0,by intro j;simp⟩).signs

theorem eventually_eq_fixed_fourier_signs (D : GlobalRoughAbelianForwardData)
    (q : WeightedCoeff (Weight.sobolev ((1:ℝ)-1)) 2)
    (hr : IsRealPeriodOneHminusOne (periodOneSobolevImageInclusion 1 (by norm_num) q)) :
    ∀ᶠ k : ℕ in atTop,(D.chart ⟨periodOneSobolevImageInclusion 1 (by norm_num) q,hr⟩).signs ((k+1:ℕ):ℤ)=
      D.fixedFourierSigns ((k+1:ℕ):ℤ) := by
  classical
  let L := periodOneSobolevImageInclusion 1 (by norm_num : (0:ℝ)≤1)
  let Q := fun t : ℝ => (t:ℂ) • q
  have hqr := sobolev_conjugateReflection_fixed_of_real_inclusion 1 (by norm_num) q hr
  have hQr (t : ℝ) : IsRealPeriodOneHminusOne (L (Q t)) := by
    apply native_l2_inclusion_real_of_fixed
    change WeightedCoeff.conjugateReflection _ _ ((t:ℂ) • q)=(t:ℂ) • q
    rw [WeightedCoeff.conjugateReflection_smul,conj_ofReal,hqr]
  let e := fun t : ℝ => (D.chart ⟨L (Q t),hQr t⟩).signs
  choose U hU hQU CA CR A R hCA hCR hAa hRa hd using
    (fun t : ℝ => D.exists_actual_l2_original_fourier_decomposition (Q t) (hQr t))
  have hQcont : Continuous Q := Complex.continuous_ofReal.smul continuous_const
  have hloc (t : ℝ) : ∃ V : Set ℝ,IsOpen V ∧ t∈V ∧ ∀ u∈V,
      (fun k : ℕ => e u ((k+1:ℕ):ℤ))=ᶠ[atTop](fun k : ℕ => e t ((k+1:ℕ):ℤ)) := by
    refine ⟨Q ⁻¹' U t,(hU t).preimage hQcont,hQU t,?_⟩
    intro u hu
    apply eventually_eq_hill_l2_fourier_signs (U t∩U u) ((hU t).inter (hU u)) (Q u) ⟨hu,hQU u⟩
      (e u) (e t) (fun p n => D.positive (L p) (n:ℤ)) (R u) (R t) (CR u) (CR t)
      (fun p hp => (hd u p hp.2).2.2.1) (fun p hp => (hd t p hp.1).2.2.1)
    · intro p hp n
      have h := (hd u p hp.2).2.2.2.1 (n:ℤ)
      rw [(hd u p hp.2).2.2.2.2.2 n] at h
      exact h
    · intro p hp n
      have h := (hd t p hp.1).2.2.2.1 (n:ℤ)
      rw [(hd t p hp.1).2.2.2.2.2 n] at h
      exact h
  have h := eventuallyEq_of_locally_eventuallyEq atTop (fun t k => e t ((k+1:ℕ):ℤ)) hloc 0 1
  have h1 : (⟨L (Q 1),hQr 1⟩ : PeriodOneRealHminusOne)=⟨L q,hr⟩ := by
    apply Subtype.ext
    change L ((1:ℂ) • q)=L q
    rw [one_smul]
  have h0 : (⟨L (Q 0),hQr 0⟩ : PeriodOneRealHminusOne)=⟨0,by intro j;simp⟩ := by
    apply Subtype.ext
    change L ((0:ℂ) • q)=0
    rw [zero_smul,map_zero]
  change ∀ᶠ k : ℕ in atTop,(D.chart ⟨L (Q 1),hQr 1⟩).signs ((k+1:ℕ):ℤ)=
    (D.chart ⟨L (Q 0),hQr 0⟩).signs ((k+1:ℕ):ℤ) at h
  rw [h1,h0] at h
  exact h

end NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
