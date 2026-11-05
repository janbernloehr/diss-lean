import NLS.SequenceSpaces.PhysicalSobolevWienerWeakStar

/-! Finite physical real Wiener tests separate the literal Sobolev target.
Their real evaluations recover both parts of every nonzero coefficient;
the mean-zero constraint supplies the remaining coefficient. -/
noncomputable section
open Set Filter Topology Complex
open scoped ENNReal
namespace NLS.WeightedCoeff

/-- An actual physical real mean-zero Wiener test supported at n and -n. -/
def physicalSobolevWienerPair (s : ℝ) (n : ℤ) (hn : n ≠ 0) (c : ℂ) :
    fourierRealZeroSubmodule (Weight.sobolev (-s)) 1 :=
  ⟨⟨ofFinsupp _ _ (Finsupp.single n c+Finsupp.single (-n) (star c)),by
    change (ofFinsupp (Weight.sobolev (-s)) 1
      (Finsupp.single n c+Finsupp.single (-n) (star c))).val 0=0
    simp [ofFinsupp_apply,hn]⟩,by
    intro k
    change (ofFinsupp (Weight.sobolev (-s)) 1
      (Finsupp.single n c+Finsupp.single (-n) (star c))).val (-k)=
        star ((ofFinsupp (Weight.sobolev (-s)) 1
          (Finsupp.single n c+Finsupp.single (-n) (star c))).val k)
    have hs (P : Prop) [Decidable P] (z : ℂ) :
        star (if P then z else 0)=if P then star z else 0 := by
      split_ifs <;> simp
    simp only [ofFinsupp_apply,Finsupp.add_apply,Finsupp.single_apply,
      star_add,hs,star_star,neg_inj]
    have he : n = -k ↔ -n=k := by omega
    simp only [he]
    exact add_comm _ _⟩

private theorem pairing_single (s : ℝ) (a : WeightedCoeff (Weight.sobolev s) ⊤)
    (n : ℤ) (c : ℂ) :
    sobolevBilinearPairing s a (ofFinsupp (Weight.sobolev (-s)) 1 (Finsupp.single n c))=
      a.val (-n)*c := by
  rw [sobolevBilinearPairing_apply]
  calc
    _=a.val (-n)*(ofFinsupp (Weight.sobolev (-s)) 1 (Finsupp.single n c)).val (-(-n)) := by
      apply tsum_eq_single (-n)
      intro k hk
      have hnk : n ≠ -k := by omega
      simp [ofFinsupp_apply,hnk]
    _=_ := by simp [ofFinsupp_apply]

/-- Exact finite-test evaluation in the literal real physical pairing. -/
theorem physicalSobolevWeakStar_pair (s : ℝ)
    (a : fourierRealZeroSubmodule (Weight.sobolev s) ⊤) (n : ℤ) (hn : n ≠ 0) (c : ℂ) :
    physicalSobolevWeakStar s a (physicalSobolevWienerPair s n hn c)=
      2*((star c)*a.val.val.val n).re := by
  change (sobolevBilinearPairing s a.val.val
    (ofFinsupp _ 1 (Finsupp.single n c+Finsupp.single (-n) (star c)))).re= _
  have he : ofFinsupp (Weight.sobolev (-s)) 1
      (Finsupp.single n c+Finsupp.single (-n) (star c))=
      ofFinsupp _ 1 (Finsupp.single n c)+ofFinsupp _ 1 (Finsupp.single (-n) (star c)) := by
    apply Subtype.ext
    rfl
  rw [he,map_add,pairing_single,pairing_single,neg_neg,a.property n]
  simp only [add_re,mul_re,Complex.star_def,conj_re,conj_im]
  ring

/-- The actual physical real Wiener weak-star realization loses no coefficient. -/
theorem physicalSobolevWeakStar_injective (s : ℝ) :
    Function.Injective (physicalSobolevWeakStar s) := by
  intro a b hab
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext n
  by_cases hn : n=0
  · subst n
    exact a.val.property.trans b.val.property.symm
  · have h1 := congrArg (fun f => f (physicalSobolevWienerPair s n hn 1)) hab
    have hI := congrArg (fun f => f (physicalSobolevWienerPair s n hn I)) hab
    rw [physicalSobolevWeakStar_pair,physicalSobolevWeakStar_pair] at h1 hI
    apply Complex.ext
    · simp only [star_one,one_mul] at h1
      linarith
    · simp only [Complex.star_def,conj_I,mul_re,neg_re,I_re,I_im,zero_mul,neg_zero,
        neg_im] at hI
      linarith

/-- Actual physical real weak-star convergence implies convergence of every
raw complex coefficient, for every filter without a norm-bound assumption. -/
theorem tendsto_coefficients_of_physicalSobolevWeakStar (s : ℝ)
    {X : Type*} {l : Filter X}
    (x : X → fourierRealZeroSubmodule (Weight.sobolev s) ⊤)
    (a : fourierRealZeroSubmodule (Weight.sobolev s) ⊤)
    (h : Tendsto (fun k => physicalSobolevWeakStar s (x k)) l (𝓝 (physicalSobolevWeakStar s a)))
    (n : ℤ) : Tendsto (fun k => (x k).val.val.val n) l (𝓝 (a.val.val.val n)) := by
  by_cases hn : n=0
  · subst n
    have he : (fun k => (x k).val.val.val 0)=(fun _ : X => (0:ℂ)) :=
      funext (fun k => (x k).val.property)
    rw [he,show a.val.val.val 0=0 from a.val.property]
    exact tendsto_const_nhds
  · have hp (c : ℂ) : Tendsto (fun k => 2*((star c)*(x k).val.val.val n).re) l
        (𝓝 (2*((star c)*a.val.val.val n).re)) := by
      have hh := tendsto_iff_forall_eval_tendsto_topDualPairing.mp h
        (physicalSobolevWienerPair s n hn c)
      change Tendsto (fun k => physicalSobolevWeakStar s (x k) (physicalSobolevWienerPair s n hn c)) l
        (𝓝 (physicalSobolevWeakStar s a (physicalSobolevWienerPair s n hn c))) at hh
      simpa only [physicalSobolevWeakStar_pair] using hh
    have hr := (hp 1).const_mul (1/2:ℝ)
    have hi := (hp I).const_mul (1/2:ℝ)
    simp only [star_one,one_mul] at hr
    simp only [Complex.star_def,conj_I,mul_re,neg_re,I_re,I_im,zero_mul,neg_zero,
      neg_im,neg_one_mul,sub_neg_eq_add,zero_add] at hi
    have hre : Tendsto (fun k => ((x k).val.val.val n).re) l (𝓝 (a.val.val.val n).re) := by
      convert hr using 1 <;> simp only [← mul_assoc,show (1/2:ℝ)*2=1 by norm_num,one_mul]
    have him : Tendsto (fun k => ((x k).val.val.val n).im) l (𝓝 (a.val.val.val n).im) := by
      convert hi using 1 <;> simp only [← mul_assoc,show (1/2:ℝ)*2=1 by norm_num,one_mul]
    have hh := (Complex.continuous_ofReal.continuousAt.tendsto.comp hre).add
      ((Complex.continuous_ofReal.continuousAt.tendsto.comp him).mul_const I)
    simpa only [Function.comp_def,Complex.re_add_im] using hh

end NLS.WeightedCoeff
