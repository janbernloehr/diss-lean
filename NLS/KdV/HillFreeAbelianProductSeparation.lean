import NLS.KdV.HillFreeSeparatedWeights
import NLS.ComplexAnalysis.HilbertPositiveProducts
import NLS.KdV.HillFreeAbelianNormalization
import NLS.KdV.HillAbelianHilbertProduct

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal

namespace NLS.KdV

variable
    (hq : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

include hq hr in
theorem hillFreeAbelianHilbertProduct_separation (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k)
    (hnk : n ≠ k) (a : Coeff 2) :
    hillAbelianHilbertProduct n ((freeHillValue k : ℂ),a) *
        ((freeHillValue n : ℂ)-(freeHillValue k : ℂ))/(freeHillValue n : ℂ) =
      hillAbelianNumeratorProduct hillFreeGapRoot k (freeHillValue k : ℂ) *
        hilbertWeightedProduct (hillFreeSeparatedWeight n k) a *
          (((k : ℂ)*a (k : ℤ))/(freeHillValue k : ℂ)) := by
  let E : ℂ := freeHillValue k
  let f : ℕ → ℂ := hillAbelianComplexNumeratorFactor n (E,a)
  let g : ℕ → ℂ := fun j => hillAbelianNumeratorFactor hillFreeGapRoot k j E
  let v : ℕ → ℂ := fun j => 1+a ((j+1 : ℕ) : ℤ)*hillFreeSeparatedWeight n k ((j+1 : ℕ) : ℤ)
  let c : ℂ := ((freeHillValue n : ℂ)-E)/(freeHillValue n : ℂ)
  let d : ℂ := (k : ℂ)*a (k : ℤ)/(freeHillValue k : ℂ)
  have hf := (multipliable_hillAbelianComplexNumeratorFactors n (E,a)).hasProd
  have hg := (multipliable_hillAbelianNumeratorFactors 0 hq hr hillFreeGapRoot
    (hillFreeGapRoot_mem_box hq hr) k E).hasProd
  have hv := (multipliable_positive_hilbertWeightedFactors (hillFreeSeparatedWeight n k) a).hasProd
  have hleft := hf.mul (hasProd_ite_eq (n-1) c)
  have hright := (hg.mul hv).mul (hasProd_ite_eq (k-1) d)
  have he (j : ℕ) : f j*(if j = n-1 then c else 1) =
      g j*v j*(if j = k-1 then d else 1) := by
    by_cases hjn : j+1 = n
    · have hji : j = n-1 := by omega
      have hjk : j+1 ≠ k := by omega
      have hjik : j ≠ k-1 := by omega
      dsimp only [f,g,v,c]
      rw [hillAbelianComplexNumeratorFactor,if_pos hjn,hillAbelianNumeratorFactor,if_neg hjk,
        hillFreeSeparatedWeight_natSucc,if_pos (Or.inl hjn),if_pos hji,if_neg hjik]
      simp only [hillGapRootEnergyFactor,hillFreeGapRoot,mul_zero,add_zero,one_mul,mul_one]
      rw [hjn]
    · by_cases hjk : j+1 = k
      · have hji : j = k-1 := by omega
        have hjin : j ≠ n-1 := by omega
        dsimp only [f,g,v,d]
        rw [hillAbelianComplexNumeratorFactor,if_neg hjn,hillAbelianNumeratorFactor,if_pos hjk,
          hillFreeSeparatedWeight_natSucc,if_pos (Or.inr hjk),if_pos hji,if_neg hjin]
        simp only [mul_zero,add_zero,one_mul,mul_one]
        rw [hjk]
        dsimp only [E]
        ring
      · have hjin : j ≠ n-1 := by omega
        have hjik : j ≠ k-1 := by omega
        have hdiff : (freeHillValue (j+1 : ℕ) : ℂ)-(freeHillValue k : ℂ) ≠ 0 :=
          sub_ne_zero.mpr (ofReal_injective.ne (strictMono_freeHillValue.injective.ne hjk))
        simp only [f,g,v,E,hillAbelianComplexNumeratorFactor,hillAbelianNumeratorFactor,
          hillGapRootEnergyFactor,hillFreeGapRoot,hillFreeSeparatedWeight_natSucc,
          if_neg hjn,if_neg hjk,if_neg (by omega : ¬(j+1 = n ∨ j+1 = k)),if_neg hjin,if_neg hjik,mul_one]
        field_simp
        ring
  have heq : (fun j => f j*(if j = n-1 then c else 1)) =
      (fun j => g j*v j*(if j = k-1 then d else 1)) := funext he
  change HasProd (fun j => f j*(if j = n-1 then c else 1)) _ at hleft
  rw [heq] at hleft
  have hprod := hleft.unique hright
  rw [← hillAbelianHilbertProduct_eq_tprod,
    ← hilbertWeightedProduct_eq_positive_tprod _ _ (hillFreeSeparatedWeight_nonpositive n k)] at hprod
  change hillAbelianHilbertProduct n (E,a)*c = hillAbelianNumeratorProduct hillFreeGapRoot k E *
    hilbertWeightedProduct (hillFreeSeparatedWeight n k) a*d at hprod
  dsimp only [c,d,E] at hprod
  convert! hprod using 1
  ring

end NLS.KdV
