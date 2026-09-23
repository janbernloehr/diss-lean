import NLS.ZakharovShabat.JointSingleSpectralProducts
import NLS.ComplexAnalysis.UniformEntireFamilies

/-!
# Single-root spectral products with one index deleted

The denominator of the deleted factor can vanish as its root moves with the
`ℓᵖ` parameter. On a large spectral circle, however, that denominator is
uniformly separated from zero for bounded displacement families. Uniform
convergence of the full products there, followed by maximum modulus, gives
uniform Cauchy convergence of the deleted products on every compact spectral
set, including across the deleted root.
-/

noncomputable section
open Set Filter Topology Metric
open scoped ENNReal ContDiff
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The literal symmetric numerator with one root omitted, normalized to
match the omitted standard-root product of Lemma 10.5. -/
def jointDeletedSingleSpectralPartialProduct (n : ℤ) (N : ℕ) :
    ℂ × Coeff p → ℂ :=
  fun t => (∏ m ∈ (Finset.Icc (-(N : ℤ)) (N : ℤ)).erase n,
    singleSpectralFactor (displacedRoots t.2) t.1 m) /
      singleSpectralDenominator n

/-- The pointwise limit of the literal deleted cutoffs. -/
def jointDeletedSingleSpectralProduct (n : ℤ) : ℂ × Coeff p → ℂ :=
  fun t => limUnder atTop (fun N => jointDeletedSingleSpectralPartialProduct n N t)

omit [Fact (1 ≤ p)] in
/-- Restoring the omitted factor gives the complete normalized product. -/
theorem jointSingleSpectralPartialProduct_eq_deleted (n : ℤ) (N : ℕ)
    (hn : n.natAbs ≤ N) (t : ℂ × Coeff p) :
    jointSingleSpectralPartialProduct N t =
      2 * (displacedRoots t.2 n-t.1) *
        jointDeletedSingleSpectralPartialProduct n N t := by
  have hm : n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
    simp only [Finset.mem_Icc]
    constructor <;> omega
  unfold jointSingleSpectralPartialProduct singleSpectralPartialProduct
    jointDeletedSingleSpectralPartialProduct
  rw [← Finset.mul_prod_erase _ _ hm]
  unfold singleSpectralFactor
  ring

/-- Every literal deleted cutoff is jointly entire. -/
theorem analyticOnNhd_jointDeletedSingleSpectralPartialProduct
    (n : ℤ) (N : ℕ) :
    AnalyticOnNhd ℂ (jointDeletedSingleSpectralPartialProduct (p := p) n N)
      Set.univ := by
  intro t _
  have hfactor (m : ℤ) : AnalyticAt ℂ
      (fun q : ℂ × Coeff p => singleSpectralFactor (displacedRoots q.2) q.1 m) t := by
    have hcoeff : AnalyticAt ℂ (fun a : Coeff p => a m) t.2 := by
      convert (lp.evalCLM ℂ (fun _ : ℤ => ℂ) p m).analyticAt t.2 using 1
      funext a
      rfl
    have hroot : AnalyticAt ℂ (fun q : ℂ × Coeff p => displacedRoots q.2 m) t :=
      analyticAt_const.add (hcoeff.comp analyticAt_snd)
    exact (hroot.sub analyticAt_fst).div_const
  change AnalyticAt ℂ (fun q : ℂ × Coeff p =>
    (∏ m ∈ (Finset.Icc (-(N : ℤ)) (N : ℤ)).erase n,
      singleSpectralFactor (displacedRoots q.2) q.1 m) /
      singleSpectralDenominator n) t
  exact (((Finset.Icc (-(N : ℤ)) (N : ℤ)).erase n).analyticAt_fun_prod
    (fun m _ => hfactor m)).div_const

/-- Deleting one root preserves uniform Cauchy convergence on compact
spectral sets over bounded `ℓᵖ` displacement families. -/
theorem uniformCauchySeqOn_jointDeletedSingleSpectralPartialProduct
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (K : Set ℂ) (hK : IsCompact K) (S : Set (Coeff p))
    (R : ℝ) (hR : 0 ≤ R) (hb : ∀ a ∈ S, ‖a‖ ≤ R) :
    UniformCauchySeqOn (jointDeletedSingleSpectralPartialProduct (p := p) n)
      atTop (K ×ˢ S) := by
  obtain ⟨B,hB⟩ := hK.isBounded.exists_norm_le
  let r : ℝ := max B 0 + ‖(Real.pi : ℂ)*(n : ℂ)‖ + R + 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hKr : K ⊆ closedBall (0 : ℂ) r := by
    intro z hz
    have hnorm := hB z hz
    have hmax : B ≤ max B 0 := le_max_left _ _
    have hle : ‖z‖ ≤ r := by dsimp [r]; nlinarith [norm_nonneg ((Real.pi : ℂ)*(n : ℂ))]
    simpa only [mem_closedBall, dist_zero_right] using hle
  have hsep (t : ℂ × Coeff p) (ht : t ∈ sphere (0 : ℂ) r ×ˢ S) :
      1 ≤ ‖displacedRoots t.2 n-t.1‖ := by
    have han : ‖t.2 n‖ ≤ R :=
      (lp.norm_apply_le_norm (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' t.2 n).trans
        (hb t.2 ht.2)
    have hroot : ‖displacedRoots t.2 n‖ ≤ ‖(Real.pi : ℂ)*(n : ℂ)‖+R := by
      calc
        _ ≤ ‖(Real.pi : ℂ)*(n : ℂ)‖+‖t.2 n‖ := norm_add_le _ _
        _ ≤ ‖(Real.pi : ℂ)*(n : ℂ)‖+R := add_le_add_right han _
    have hzr : ‖t.1‖ = r := by
      simpa only [mem_sphere, dist_zero_right] using ht.1
    have htri : ‖t.1‖ ≤ ‖displacedRoots t.2 n-t.1‖ + ‖displacedRoots t.2 n‖ := by
      simpa only [norm_sub_rev] using norm_le_norm_sub_add t.1 (displacedRoots t.2 n)
    have hmax : 0 ≤ max B 0 := le_max_right _ _
    dsimp [r] at hzr
    linarith
  have hfull := tendstoUniformlyOn_jointSingleSpectralProduct hp hp1
    (sphere (0 : ℂ) r) (isCompact_sphere _ _) S R hR hb
  have hsphere : UniformCauchySeqOn
      (jointDeletedSingleSpectralPartialProduct (p := p) n) atTop
      (sphere (0 : ℂ) r ×ˢ S) := by
    have hc := hfull.uniformCauchySeqOn
    rw [Metric.uniformCauchySeqOn_iff] at hc ⊢
    intro ε hε
    obtain ⟨N,hN⟩ := hc ε hε
    refine ⟨max N n.natAbs, ?_⟩
    intro M hM L hL t ht
    have hden : 1 ≤ ‖2*(displacedRoots t.2 n-t.1)‖ := by
      rw [norm_mul]
      norm_num
      nlinarith [hsep t ht]
    have hden0 : 2*(displacedRoots t.2 n-t.1) ≠ 0 :=
      norm_pos_iff.mp (lt_of_lt_of_le zero_lt_one hden)
    have hz : displacedRoots t.2 n-t.1 ≠ 0 := by
      intro he
      exact hden0 (by rw [he, mul_zero])
    have heq : jointDeletedSingleSpectralPartialProduct n M t -
        jointDeletedSingleSpectralPartialProduct n L t =
        (jointSingleSpectralPartialProduct M t -
          jointSingleSpectralPartialProduct L t) /
          (2*(displacedRoots t.2 n-t.1)) := by
      rw [jointSingleSpectralPartialProduct_eq_deleted n M
        ((le_max_right _ _).trans hM) t,
        jointSingleSpectralPartialProduct_eq_deleted n L
        ((le_max_right _ _).trans hL) t]
      field_simp [hz]
    rw [dist_eq_norm, heq, norm_div]
    have hbound : ‖jointSingleSpectralPartialProduct M t -
        jointSingleSpectralPartialProduct L t‖ < ε := by
      simpa only [dist_eq_norm] using hN M ((le_max_left _ _).trans hM)
        L ((le_max_left _ _).trans hL) t ht
    exact (div_le_self (norm_nonneg _) hden).trans_lt hbound
  have hfinite (N : ℕ) (a : Coeff p) :
      Differentiable ℂ (fun z => jointDeletedSingleSpectralPartialProduct n N (z,a)) := by
    intro z
    have hpair : AnalyticAt ℂ (fun w : ℂ => (w,a)) z :=
      analyticAt_id.prod analyticAt_const
    exact ((analyticOnNhd_jointDeletedSingleSpectralPartialProduct n N
      (z,a) (mem_univ _)).comp (f := fun w : ℂ => (w,a)) hpair).differentiableAt
  exact (NLS.ComplexAnalysis.uniformCauchySeqOn_closedBall_prod_of_sphere
    (jointDeletedSingleSpectralPartialProduct (p := p) n) S hfinite 0 r hr hsphere).mono
      (fun t ht => ⟨hKr ht.1, ht.2⟩)

/-- The literal deleted cutoffs converge at every spectral parameter and
every displacement sequence, including at the removed root itself. -/
theorem tendsto_jointDeletedSingleSpectralPartialProduct
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (t : ℂ × Coeff p) :
    Tendsto (fun N => jointDeletedSingleSpectralPartialProduct n N t) atTop
      (𝓝 (jointDeletedSingleSpectralProduct n t)) := by
  have h := uniformCauchySeqOn_jointDeletedSingleSpectralPartialProduct hp hp1 n
    ({t.1} : Set ℂ) isCompact_singleton ({t.2} : Set (Coeff p))
    ‖t.2‖ (norm_nonneg _) (by intro a ha; subst a; exact le_refl _)
  exact (h.cauchySeq (by simp : t ∈ ({t.1} : Set ℂ) ×ˢ ({t.2} : Set (Coeff p)))).tendsto_limUnder

/-- The literal deleted cutoffs converge uniformly over compact spectral
sets and bounded displacement families. -/
theorem tendstoUniformlyOn_jointDeletedSingleSpectralProduct
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (K : Set ℂ) (hK : IsCompact K) (S : Set (Coeff p))
    (R : ℝ) (hR : 0 ≤ R) (hb : ∀ a ∈ S, ‖a‖ ≤ R) :
    TendstoUniformlyOn (jointDeletedSingleSpectralPartialProduct (p := p) n)
      (jointDeletedSingleSpectralProduct n) atTop (K ×ˢ S) := by
  exact (uniformCauchySeqOn_jointDeletedSingleSpectralPartialProduct hp hp1 n K hK S R hR hb)
    |>.tendstoUniformlyOn_of_tendsto (fun t _ =>
      tendsto_jointDeletedSingleSpectralPartialProduct hp hp1 n t)

/-- The product after deleting an arbitrary index is jointly entire in
the spectral parameter and its `ℓᵖ` displacement sequence. -/
theorem analyticOnNhd_jointDeletedSingleSpectralProduct
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) :
    AnalyticOnNhd ℂ (jointDeletedSingleSpectralProduct (p := p) n) Set.univ := by
  have huniform (t : ℂ × Coeff p) (_ : t ∈ (Set.univ : Set (ℂ × Coeff p))) :
      ∃ U : Set (ℂ × Coeff p), IsOpen U ∧ t ∈ U ∧
        TendstoUniformlyOn (jointDeletedSingleSpectralPartialProduct (p := p) n)
          (jointDeletedSingleSpectralProduct n) atTop U := by
    let K : Set ℂ := closedBall t.1 1
    let S : Set (Coeff p) := closedBall t.2 1
    let U : Set (ℂ × Coeff p) := ball t.1 1 ×ˢ ball t.2 1
    have hb : ∀ a ∈ S, ‖a‖ ≤ ‖t.2‖+1 := by
      intro a ha
      have hdist : ‖a-t.2‖ ≤ (1 : ℝ) := by
        have h := mem_closedBall.mp ha
        simpa only [dist_eq_norm] using h
      calc
        ‖a‖ = ‖(a-t.2)+t.2‖ := by rw [sub_add_cancel]
        _ ≤ ‖a-t.2‖+‖t.2‖ := norm_add_le _ _
        _ ≤ ‖t.2‖+1 := by linarith
    refine ⟨U, isOpen_ball.prod isOpen_ball, ⟨mem_ball_self (by norm_num),
      mem_ball_self (by norm_num)⟩, ?_⟩
    exact (tendstoUniformlyOn_jointDeletedSingleSpectralProduct hp hp1 n K
      (isCompact_closedBall _ _) S (‖t.2‖+1) (by positivity) hb).mono
      (fun q hq => ⟨mem_closedBall.mpr (le_of_lt hq.1),
        mem_closedBall.mpr (le_of_lt hq.2)⟩)
  have happrox := NLS.ComplexAnalysis.HasLocalUniformAnalyticApproximationOn.of_open_local_uniform
    isOpen_univ (fun N => analyticOnNhd_jointDeletedSingleSpectralPartialProduct (p := p) n N)
    huniform
  exact NLS.ComplexAnalysis.analyticOnNhd_of_complexSmoothOn _ isOpen_univ
    happrox.contDiffOn

/-- The entire single-root product factors through the deleted product,
including when the omitted root collides with another root. -/
theorem jointSingleSpectralProduct_eq_deleted
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (t : ℂ × Coeff p) :
    jointSingleSpectralProduct t =
      2*(displacedRoots t.2 n-t.1)*jointDeletedSingleSpectralProduct n t := by
  have hfull := (tendstoLocallyUniformlyOn_entireSingleSpectralProduct hp
    (displacedRoots t.2) (memℓp_displacedRoots t.2)).tendsto_at (mem_univ t.1)
  have hdeleted := (tendsto_jointDeletedSingleSpectralPartialProduct hp hp1 n t).const_mul
    (2*(displacedRoots t.2 n-t.1))
  have he : ∀ᶠ N : ℕ in atTop,
      2*(displacedRoots t.2 n-t.1)*jointDeletedSingleSpectralPartialProduct n N t =
        jointSingleSpectralPartialProduct N t := by
    filter_upwards [eventually_ge_atTop n.natAbs] with N hN
    exact (jointSingleSpectralPartialProduct_eq_deleted n N hN t).symm
  exact tendsto_nhds_unique hfull (hdeleted.congr' he)

end NLS.ZakharovShabat
