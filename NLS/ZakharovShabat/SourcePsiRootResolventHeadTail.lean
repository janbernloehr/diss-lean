import NLS.ZakharovShabat.SourcePsiRootResolventExterior

/-!
# Explicit head and tail estimates on the outer circles

A Holder estimate splits the root resolvent into the coefficient tail
and a finite denominator sum. On the moving half-radius cutoff the
latter has an explicit bound uniform around the whole circle. The
actual-root comparison retains its factor two, and both terms of the
resulting positive bound tend to zero, as required in Lemma 12.7.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
local instance : Fact (1 ≤ p.conjExponent) := ⟨ENNReal.HolderConjugate.one_le p.conjExponent p⟩

/-- An explicit Holder split into the coefficient tail and a finite denominator sum. -/
theorem norm_freeResolvent_le_head_tail
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h : Coeff p) (s : Finset ℤ)
    (z : ℂ) (hz : z ∉ freeLattice) {r : ℝ} (hr : 0 < r) (hrπ : r ≤ Real.pi/4)
    (hsep : ∀ m : ℤ, r ≤ ‖z-(Real.pi:ℂ)*m‖) :
    ‖scalarResolventToL1 hp z hz h‖ ≤
      (WeightedCoeff.sobolevEmbeddingConstant p hp/r)*‖h-Coeff.truncate s h‖ +
      ‖h‖*(∑ m ∈ s, ‖(z-(Real.pi:ℂ)*m)⁻¹‖ ^ p.conjExponent.toReal) ^
        (1/p.conjExponent.toReal) := by
  let b := Coeff.truncate s (conjugateInverseSymbol p hp z hz)
  have he : scalarResolventToL1 hp z hz (Coeff.truncate s h) =
      WeightedCoeff.holderProduct h b := by
    ext m
    rw [scalarResolventToL1_apply]
    change (Coeff.truncate s h) m/(z-(Real.pi:ℂ)*m) = h m*b m
    by_cases hm : m ∈ s
    · simp [Coeff.truncate_apply,hm,b,conjugateInverseSymbol,div_eq_mul_inv]
    · simp [Coeff.truncate_apply,hm,b]
  have hh : ‖scalarResolventToL1 hp z hz (Coeff.truncate s h)‖ ≤ ‖h‖*‖b‖ := by
    rw [he]
    calc
      _ ≤ ‖WeightedCoeff.holderProduct (p := p) (q := p.conjExponent)‖*‖h‖*‖b‖ :=
        (WeightedCoeff.holderProduct (p := p) (q := p.conjExponent)).le_opNorm₂ _ _
      _ ≤ 1*‖h‖*‖b‖ := by gcongr; exact WeightedCoeff.norm_holderProduct_le
      _ = _ := by ring
  have hq : p.conjExponent ≠ ⊤ :=
    ((ENNReal.HolderConjugate.lt_top_iff_one_lt p.conjExponent p).mpr hp1).ne
  have hq0 : 0 < p.conjExponent.toReal := ENNReal.toReal_pos
    (zero_lt_one.trans_le (Fact.out : 1 ≤ p.conjExponent)).ne' hq
  have hb : ‖b‖ =
      (∑ m ∈ s, ‖(z-(Real.pi:ℂ)*m)⁻¹‖ ^ p.conjExponent.toReal) ^
        (1/p.conjExponent.toReal) := by
    rw [lp.norm_eq_tsum_rpow hq0]
    congr 1
    rw [tsum_eq_sum (s := s) (fun m hm => by simp [b,hm,hq0.ne'])]
    apply Finset.sum_congr rfl
    intro m hm
    simp [b,hm,conjugateInverseSymbol]
  have hsplit : scalarResolventToL1 hp z hz h =
      scalarResolventToL1 hp z hz (h-Coeff.truncate s h) +
        scalarResolventToL1 hp z hz (Coeff.truncate s h) := by
    rw [← map_add,sub_add_cancel]
  rw [hsplit]
  exact (norm_add_le _ _).trans (add_le_add
    (norm_scalarResolventToL1_le_of_separated hp z hz hr hrπ hsep _) (by rwa [hb] at hh))

/-- One exterior threshold gives a positive head/tail bound for all directions and cutoffs. -/
theorem exists_threshold_actualRootResolvent_head_tail
    (hp : p ≠ ⊤) (hp1 : 1 < p) (a : Coeff p)
    {r : ℝ} (hr : 0 < r) (hrπ : r ≤ Real.pi/4) :
    ∃ R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ →
      (∀ m : ℤ, r ≤ ‖z-(Real.pi:ℂ)*m‖) →
      ∀ h : Coeff p, ∀ s : Finset ℤ,
      Summable (fun m : ℤ => ‖h m/(displacedRoots a m-z)‖) ∧
      (∑' m : ℤ, ‖h m/(displacedRoots a m-z)‖) ≤
        (2*WeightedCoeff.sobolevEmbeddingConstant p hp/r)*‖h-Coeff.truncate s h‖ +
        2*‖h‖*(∑ m ∈ s, ‖(z-(Real.pi:ℂ)*m)⁻¹‖ ^ p.conjExponent.toReal) ^
          (1/p.conjExponent.toReal) := by
  obtain ⟨R,hR⟩ := exists_threshold_two_rootDisplacement_le_freeDenominator hp a hr
  refine ⟨R,?_⟩
  intro z hz hsep h s
  have hzfree := notMem_freeLattice_of_separated hr hsep
  have hf : Summable (fun m : ℤ => ‖h m/(z-(Real.pi:ℂ)*m)‖) := by
    simpa only [scalarResolventToL1_apply] using
      (lp.memℓp (scalarResolventToL1 hp z hzfree h)).norm.summable_of_one
  have hpoint (m : ℤ) : ‖h m/(displacedRoots a m-z)‖ ≤
      2*‖h m/(z-(Real.pi:ℂ)*m)‖ :=
    norm_actualRootResolvent_le_twice_free a h z m hr (hsep m) (hR z hz hsep m)
  have ha := (hf.mul_left 2).of_nonneg_of_le (fun _ => norm_nonneg _) hpoint
  refine ⟨ha,?_⟩
  have hb := ha.tsum_le_tsum hpoint (hf.mul_left 2)
  rw [tsum_mul_left] at hb
  have hn : (∑' m : ℤ, ‖h m/(z-(Real.pi:ℂ)*m)‖) =
      ‖scalarResolventToL1 hp z hzfree h‖ := by
    simp [lp.norm_eq_tsum_rpow (by norm_num : (0:ℝ) < (1:ℝ≥0∞).toReal)]
  rw [hn] at hb
  have hfree := norm_freeResolvent_le_head_tail hp hp1 h s z hzfree hr hrπ hsep
  calc
    _ ≤ 2*((WeightedCoeff.sobolevEmbeddingConstant p hp/r)*‖h-Coeff.truncate s h‖ +
        ‖h‖*(∑ m ∈ s, ‖(z-(Real.pi:ℂ)*m)⁻¹‖ ^ p.conjExponent.toReal) ^
          (1/p.conjExponent.toReal)) :=
      hb.trans (mul_le_mul_of_nonneg_left hfree (by norm_num))
    _ = _ := by ring

end NLS.ZakharovShabat



noncomputable section
open Set Metric Complex Filter Topology
namespace NLS.ZakharovShabat

/-- The finite denominator sum on the moving half-radius cutoff has an explicit decaying bound. -/
theorem centralCircle_halfCutoff_inversePower_le
    (q : ℝ) (hq : 1 < q) (ν : ℕ) (z : ℂ)
    (hz : z ∈ sphere (0:ℂ) (centralCircleRadius ν)) :
    (∑ m ∈ Finset.Icc (-((ν/2:ℕ):ℤ)) ((ν/2:ℕ):ℤ),
      ‖(z-(Real.pi:ℂ)*m)⁻¹‖ ^ q) ^ (1/q) ≤
        (2/Real.pi)*((ν:ℝ)+1) ^ (1/q-1) := by
  let s : Finset ℤ := Finset.Icc (-((ν/2:ℕ):ℤ)) ((ν/2:ℕ):ℤ)
  let A : ℝ := (ν:ℝ)+1
  have hA : 0 < A := by dsimp [A]; positivity
  have hq0 : 0 < q := zero_lt_one.trans hq
  have hden (m : ℤ) (hm : m ∈ s) : Real.pi*A/2 ≤ ‖z-(Real.pi:ℂ)*m‖ := by
    have hmi : m.natAbs ≤ ν/2 := by
      simp only [s,Finset.mem_Icc] at hm
      omega
    have hmi' : 2*(m.natAbs:ℝ) ≤ (ν:ℝ) := by
      exact_mod_cast (show 2*m.natAbs ≤ ν by omega)
    have hn : ‖z‖ = (ν:ℝ)*Real.pi+Real.pi/2 := by
      simpa only [mem_sphere,dist_zero_right,centralCircleRadius] using hz
    have hc : ‖(Real.pi:ℂ)*m‖ = Real.pi*(m.natAbs:ℝ) := by
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos,Complex.norm_intCast]
      simp only [Nat.cast_natAbs,Int.cast_abs]
    have ht := norm_sub_norm_le z ((Real.pi:ℂ)*m)
    rw [hn,hc] at ht
    dsimp [A]
    nlinarith [Real.pi_pos]
  have hi (m : ℤ) (hm : m ∈ s) : ‖(z-(Real.pi:ℂ)*m)⁻¹‖ ≤ 2/(Real.pi*A) := by
    rw [norm_inv]
    calc
      _ ≤ (Real.pi*A/2)⁻¹ := inv_anti₀ (by positivity) (hden m hm)
      _ = _ := by field_simp
  have hcard : (s.card:ℝ) ≤ A := by
    have : s.card ≤ ν+1 := by simp only [s,Int.card_Icc]; omega
    dsimp [A]
    exact_mod_cast this
  have hs : (∑ m ∈ s, ‖(z-(Real.pi:ℂ)*m)⁻¹‖ ^ q) ≤ A*(2/(Real.pi*A))^q := by
    calc
      _ ≤ ∑ _m ∈ s, (2/(Real.pi*A))^q := Finset.sum_le_sum
        (fun m hm => Real.rpow_le_rpow (norm_nonneg _) (hi m hm) hq0.le)
      _ = (s.card:ℝ)*(2/(Real.pi*A))^q := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hcard (Real.rpow_nonneg (by positivity) _)
  change (∑ m ∈ s, ‖(z-(Real.pi:ℂ)*m)⁻¹‖ ^ q) ^ (1/q) ≤ _
  calc
    _ ≤ (A*(2/(Real.pi*A))^q)^(1/q) :=
      Real.rpow_le_rpow (by positivity) hs (by positivity)
    _ = (2/Real.pi)*A^(1/q-1) := by
      rw [Real.mul_rpow hA.le (by positivity),← Real.rpow_mul (by positivity),
        mul_one_div_cancel hq0.ne',Real.rpow_one,Real.rpow_sub hA,Real.rpow_one]
      field_simp

/-- The bound for the moving finite part tends to zero for every conjugate exponent above one. -/
theorem tendsto_halfCutoff_inversePower_bound (q : ℝ) (hq : 1 < q) :
    Tendsto (fun ν : ℕ => (2/Real.pi)*((ν:ℝ)+1)^(1/q-1)) atTop (𝓝 0) := by
  have he : 0 < 1-1/q := by
    have : 1/q < 1 := (div_lt_one (zero_lt_one.trans hq)).mpr hq
    linarith
  have hn : Tendsto (fun ν : ℕ => (ν:ℝ)+1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have h := (tendsto_rpow_neg_atTop he).comp hn
  simpa only [neg_sub,mul_zero,Function.comp_def] using h.const_mul (2/Real.pi)

end NLS.ZakharovShabat

namespace NLS.ZakharovShabat
open Set Metric Complex Filter Topology
open scoped ENNReal
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The source moving-cutoff estimate with explicit positive constants on all large circles. -/
theorem eventually_centralCircle_actualRootResolvent_halfCutoff_bound
    (hp : p ≠ ⊤) (hp1 : 1 < p) (a h : Coeff p) :
    ∃ K : ℕ, ∀ ν : ℕ, K ≤ ν → ∀ z ∈ sphere (0:ℂ) (centralCircleRadius ν),
      Summable (fun m : ℤ => ‖h m/(displacedRoots a m-z)‖) ∧
      (∑' m : ℤ, ‖h m/(displacedRoots a m-z)‖) ≤
        (8*WeightedCoeff.sobolevEmbeddingConstant p hp/Real.pi)*
          ‖h-Coeff.truncate (Finset.Icc (-((ν/2:ℕ):ℤ)) ((ν/2:ℕ):ℤ)) h‖ +
        (4/Real.pi)*‖h‖*((ν:ℝ)+1)^(1/p.conjExponent.toReal-1) := by
  obtain ⟨R,hR⟩ := exists_threshold_actualRootResolvent_head_tail hp hp1 a
    (by positivity : 0 < Real.pi/4) le_rfl
  obtain ⟨K,hK⟩ := exists_nat_gt (R/Real.pi)
  refine ⟨K,?_⟩
  intro ν hν z hz
  have hlarge : R ≤ ‖z‖ := by
    have hnorm : ‖z‖ = (ν:ℝ)*Real.pi+Real.pi/2 := by
      simpa only [mem_sphere,dist_zero_right,centralCircleRadius] using hz
    have hK' := (div_lt_iff₀ Real.pi_pos).mp hK
    have hν' : (K:ℝ) ≤ (ν:ℝ) := by exact_mod_cast hν
    rw [hnorm]
    nlinarith [Real.pi_pos]
  have hsep (m : ℤ) : Real.pi/4 ≤ ‖z-(Real.pi:ℂ)*m‖ := by
    have ht := centralCircle_lattice_gap ν hz m
    linarith [Real.pi_pos]
  have hq : p.conjExponent ≠ ⊤ :=
    ((ENNReal.HolderConjugate.lt_top_iff_one_lt p.conjExponent p).mpr hp1).ne
  have hq1 : 1 < p.conjExponent.toReal := by
    have he := (ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top
    simpa only [ENNReal.toReal_one] using
      (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hq).mpr he
  obtain ⟨hs,hb⟩ := hR z hlarge hsep h (Finset.Icc (-((ν/2:ℕ):ℤ)) ((ν/2:ℕ):ℤ))
  have hc := centralCircle_halfCutoff_inversePower_le p.conjExponent.toReal hq1 ν z hz
  refine ⟨hs,?_⟩
  calc
    _ ≤ (2*WeightedCoeff.sobolevEmbeddingConstant p hp/(Real.pi/4))*
        ‖h-Coeff.truncate (Finset.Icc (-((ν/2:ℕ):ℤ)) ((ν/2:ℕ):ℤ)) h‖ +
        2*‖h‖*((2/Real.pi)*((ν:ℝ)+1)^(1/p.conjExponent.toReal-1)) :=
      hb.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hc
        (show 0 ≤ 2*‖h‖ from mul_nonneg (by norm_num) (norm_nonneg h))))
    _ = _ := by ring

/-- Both terms in the explicit moving-cutoff estimate tend to zero. -/
theorem tendsto_actualRootResolvent_halfCutoff_bound
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h : Coeff p) :
    Tendsto (fun ν : ℕ =>
      (8*WeightedCoeff.sobolevEmbeddingConstant p hp/Real.pi)*
        ‖h-Coeff.truncate (Finset.Icc (-((ν/2:ℕ):ℤ)) ((ν/2:ℕ):ℤ)) h‖ +
      (4/Real.pi)*‖h‖*((ν:ℝ)+1)^(1/p.conjExponent.toReal-1)) atTop (𝓝 0) := by
  have hdiv : Tendsto (fun ν : ℕ => ν/2) atTop atTop := by
    apply Filter.tendsto_atTop.mpr
    intro N
    filter_upwards [eventually_ge_atTop (2*N)] with ν hν
    omega
  have ht := (Coeff.tendsto_truncate hp h).comp (Finset.tendsto_Icc_neg.comp hdiv)
  have htail : Tendsto (fun ν : ℕ =>
      ‖h-Coeff.truncate (Finset.Icc (-((ν/2:ℕ):ℤ)) ((ν/2:ℕ):ℤ)) h‖) atTop (𝓝 0) := by
    simpa only [Function.comp_def,sub_self,norm_zero] using
      ((tendsto_const_nhds (x := h)).sub ht).norm
  have hq : p.conjExponent ≠ ⊤ :=
    ((ENNReal.HolderConjugate.lt_top_iff_one_lt p.conjExponent p).mpr hp1).ne
  have hq1 : 1 < p.conjExponent.toReal := by
    have he := (ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top
    simpa only [ENNReal.toReal_one] using
      (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hq).mpr he
  have hh := (tendsto_halfCutoff_inversePower_bound p.conjExponent.toReal hq1).const_mul (2*‖h‖)
  have he : (fun ν : ℕ => 2*‖h‖*((2/Real.pi)*((ν:ℝ)+1)^(1/p.conjExponent.toReal-1))) =
      (fun ν : ℕ => (4/Real.pi)*‖h‖*((ν:ℝ)+1)^(1/p.conjExponent.toReal-1)) := by
    funext ν
    ring
  rw [he,mul_zero] at hh
  simpa only [mul_zero,add_zero] using
    (htail.const_mul (8*WeightedCoeff.sobolevEmbeddingConstant p hp/Real.pi)).add hh

end NLS.ZakharovShabat
