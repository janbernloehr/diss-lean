import NLS.KdV.HminusOneHillProductZeroJacobian

/-! Reality of literal Hill products and their FILLED coordinate
variations for real independent energy data. No universal numerator
scalar or source normalization is assumed. -/
noncomputable section
open Set Complex ComplexConjugate Filter Topology
open scoped ENNReal Classical
namespace NLS.KdV

theorem hillEnergySequenceProduct_im_eq_zero (n : ℕ+) (E : ℂ) (hE : E.im = 0)
    (d : lp (fun _ : ℕ+ => ℂ) 2) (hd : ∀ m, (d m).im = 0) :
    (hillEnergySequenceProduct n (E,d)).im = 0 := by
  have he : conj E = E := Complex.conj_eq_iff_im.mpr hE
  have hf (j : ℕ) : conj (hillEnergySequenceFactor (E,d) j) = hillEnergySequenceFactor (E,d) j := by
    simp [hillEnergySequenceFactor,he,Complex.conj_eq_iff_im.mpr (hd ⟨j+1,by omega⟩)]
  have hfinite (N : ℕ) : conj (hillEnergySequencePartialProduct n N (E,d)) =
      hillEnergySequencePartialProduct n N (E,d) := by
    unfold hillEnergySequencePartialProduct
    rw [map_prod]
    exact Finset.prod_congr rfl (fun j _ => hf j)
  have ht := tendsto_hillEnergySequencePartialProduct n (E,d)
  have hc := continuous_conj.continuousAt.tendsto.comp ht
  simp only [Function.comp_def,hfinite] at hc
  exact Complex.conj_eq_iff_im.mp (tendsto_nhds_unique hc ht)

theorem hillEnergyProductCoordinateDerivative_im_eq_zero (n m : ℕ+) (E : ℂ) (hE : E.im = 0)
    (d : lp (fun _ : ℕ+ => ℂ) 2) (hd : ∀ k, (d k).im = 0) :
    (hillEnergyProductCoordinateDerivative n m (E,d)).im = 0 := by
  have hs : ∀ k : ℕ+, (hillZeroCoordinateShift m d 1 k).im = 0 := by
    intro k
    rw [hillZeroCoordinateShift_apply]
    by_cases hkm : k = m
    · rw [if_pos hkm, add_im, hd, one_im, add_zero]
    · rw [if_neg hkm, add_zero]
      exact hd k
  rw [hillEnergyProductCoordinateDerivative,sub_im,
    hillEnergySequenceProduct_im_eq_zero n E hE _ hs,hillEnergySequenceProduct_im_eq_zero n E hE d hd,sub_self]

theorem hillHminusPsiZeroDisplacement_im_eq_zero (n m : ℕ+) (q : PeriodOneRealHminusOne) :
    (hillHminusPsiZeroDisplacement n q m).im = 0 := by
  change (((hillHminusCanonicalPsiRealZero n m q.val q.property:ℂ)-((Real.pi:ℂ)*(m:ℕ))^2)/(m:ℕ)).im = 0
  simp [div_im,pow_two,mul_im]

end NLS.KdV
