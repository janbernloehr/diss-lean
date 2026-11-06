import NLS.Articles.KdVKdV2Frequencies.GlobalRoughFiniteSupportCompactness

/-! # Exact recovery of every finite real target by the SAME global map

The fixed original physical Birkhoff inverse is applied to the literal
real coordinate pair, with its original square-root-of-two normalization.
No small target restriction or continuation assumption is used.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.KdV
open scoped ENNReal Classical ComplexConjugate
namespace NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData

/-- Every finite real mean-zero native weak target has an actual ORIGINAL
physical mean-zero preimage, at arbitrary size and with exact signed phases. -/
theorem exists_physical_preimage_of_signed_finite_tail (D : GlobalRoughAbelianForwardData)
    (b : WeightedCoeff (Weight.sobolev (-1/2)) 2)
    (hr : ∀ j : ℤ, b.val (-j)=conj (b.val j)) (hm : b.val 0=0)
    (N : ℕ) (hz : ∀ j : ℤ, N ≤ j.natAbs → b.val j=0) :
    ∃ p : hillRealMeanZeroSourceSubmodule, D.signed (hillOriginalHminusSource p.val.val)=b := by
  let a : ℕ → ℝ × ℝ := fun k =>
    (Real.sqrt 2*(b.val (k+1 : ℕ)).re,-Real.sqrt 2*(b.val (k+1 : ℕ)).im)
  let f := realNatPairNormalization hillBirkhoffBaseWeight a
  have hf (k : ℕ) (hk : f k ≠ 0) : k ∈ Finset.range N := by
    by_contra hout
    have hzero : b.val (k+1 : ℕ)=0 := hz _ (by simp only [Int.natAbs_natCast]; simp only [Finset.mem_range] at hout; omega)
    apply hk
    change (hillBirkhoffBaseWeight k : ℂ)*
      ((Real.sqrt 2*(b.val (k+1 : ℕ)).re : ℝ)-I*(-Real.sqrt 2*(b.val (k+1 : ℕ)).im : ℝ))=0
    rw [hzero]
    simp
  let c : lp (fun _ : ℕ => ℂ) 2 :=
    ⟨fun k => (Finsupp.onFinset (Finset.range N) f hf) k,
      (memℓp_zero_iff.mpr (Finsupp.onFinset (Finset.range N) f hf).hasFiniteSupport).of_exponent_ge bot_le⟩
  have hc : (c : ℕ → ℂ)=f := rfl
  let B : HillBirkhoffSpace := ⟨a,by change Memℓp f 2; exact hc ▸ lp.memℓp c⟩
  let p := hillOriginalBirkhoffInverse B
  let q := hillOriginalHminusSource p.val.val
  have hqr : IsRealPeriodOneHminusOne q := hillOriginalHminusSource_real p.val.val p.val.property.2
  have hpos (n : ℕ) (hn : 0<n) : (D.signed q).val (n : ℤ)=b.val n := by
    have he := D.original_global_birkhoff_agreement p ⟨n,hn⟩
    change (D.signed q).val (n : ℤ)=hillOriginalBirkhoffAbelianCoordinate p ⟨n,hn⟩ at he
    apply he.trans
    unfold hillOriginalBirkhoffAbelianCoordinate
    rw [hillOriginalBirkhoffMap_apply_inverse]
    have hn' : n-1+1=n := by omega
    change (((Real.sqrt 2*(b.val (n-1+1 : ℕ)).re : ℝ) : ℂ)-
      I*((-Real.sqrt 2*(b.val (n-1+1 : ℕ)).im : ℝ) : ℂ))/(Real.sqrt 2 : ℂ)=_
    rw [hn']
    have hs : (Real.sqrt 2 : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2)).ne'
    calc
      _ = (Real.sqrt 2 : ℂ)*((b.val n).re+(b.val n).im*I)/(Real.sqrt 2 : ℂ) := by push_cast; ring
      _ = b.val n := by rw [Complex.re_add_im]; exact mul_div_cancel_left₀ _ hs
  refine ⟨p,?_⟩
  apply Subtype.ext
  funext j
  rcases lt_trichotomy j 0 with hj | rfl | hj
  · let n := (-j).toNat
    have hn : 0<n := by dsimp only [n]; omega
    have hnj : (n : ℤ) = -j := by dsimp only [n]; omega
    have he : j = -(n : ℤ) := by omega
    rw [he,D.signed_real q hqr,hpos n hn,hr]
  · exact (D.signed_zero q (D.real_mem_domain q hqr)).trans hm.symm
  · let n := j.toNat
    have hn : 0<n := by dsimp only [n]; omega
    have hnj : (n : ℤ)=j := by dsimp only [n]; omega
    simpa only [hnj] using hpos n hn

end NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
