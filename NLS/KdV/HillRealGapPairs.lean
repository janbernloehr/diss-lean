import NLS.KdV.HillCharacteristicZeros
import NLS.KdV.HillRealSpectrum

/-! # Ordered real high-energy Hill pairs

The pair is constructed from the actual characteristic zeros, with
repetition at a collapsed gap. It exhausts its checked strip and carries
the exact analytic characteristic orders. This is a local high-energy
enumeration, not yet the source's global labeling from the lowest root.
-/

noncomputable section
open Set Metric
open scoped Classical
namespace NLS.KdV

/-- An ordered actual real pair, including its analytic multiplicities. -/
structure HillRealHighGapPair (q : Coeff 2) (n : ℕ) where
  left : ℝ
  right : ℝ
  ordered : left ≤ right
  left_mem : (left : ℂ) ∈ closedBall (freeHillValue n : ℂ) (n : ℝ)
  right_mem : (right : ℂ) ∈ closedBall (freeHillValue n : ℂ) (n : ℝ)
  left_zero : hillL2Radicand q left = 0
  right_zero : hillL2Radicand q right = 0
  zeros_iff : ∀ z ∈ reducedHillStrip n,
    hillL2Radicand q z = 0 ↔ z = (left : ℂ) ∨ z = (right : ℂ)
  orders : ∀ z ∈ closedBall (freeHillValue n : ℂ) (n : ℝ),
    analyticOrderNatAt (hillL2Radicand q) z = ({(left : ℂ),(right : ℂ)} : Multiset ℂ).count z

/-- The pair exists for every real period-one L2 potential at the checked
linear cutoff; endpoints are actual characteristic roots, not input data. -/
theorem exists_hillRealHighGapPair
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hreal : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (n : ℕ) (hn : 1 ≤ n) (hcut : 8*‖q‖ ≤ (n : ℝ)) :
    Nonempty (HillRealHighGapPair (SpectralWeight.one.toCoeff q) n) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  obtain ⟨b,hb⟩ := (NormedSpace.sphere_nonempty (E := ℂ)
    (x := (freeHillValue n : ℂ))).mpr hnpos.le
  have hb0 := hillL2Radicand_ne_zero_on_sphere q hq n hn hcut b hb
  have ha := (analyticOnNhd_hillL2Radicand (SpectralWeight.one.toCoeff q)).mono
    (subset_univ (closedBall (freeHillValue n : ℂ) (n : ℝ)))
  obtain ⟨x,hx,y,hy,hx0,hy0,horder⟩ := ComplexAnalysis.exists_two_analytic_zeros
    (ComplexAnalysis.analyticZeroCount_hasFiniteSupport (isCompact_closedBall _ _)
      (isConnected_closedBall hnpos.le) ha (sphere_subset_closedBall hb) hb0)
    (hillL2Radicand_two_zeros q hq n hn hcut)
  have hxi := hillL2Discriminant_root_im_zero q hq hreal x (sub_eq_zero.mp hx0)
  have hyi := hillL2Discriminant_root_im_zero q hq hreal y (sub_eq_zero.mp hy0)
  have hxc : (x.re : ℂ) = x := by apply Complex.ext <;> simp [hxi]
  have hyc : (y.re : ℂ) = y := by apply Complex.ext <;> simp [hyi]
  have hzeros (z : ℂ) (hz : z ∈ reducedHillStrip n) :
      hillL2Radicand (SpectralWeight.one.toCoeff q) z = 0 ↔ z = x ∨ z = y := by
    constructor
    · intro hz0
      have hloc := hillL2Radicand_zero_localization q hq n hn z hz
        (show 8*‖q‖ ≤ (n : ℝ) by linarith [norm_nonneg q]) hz0
      have hzk : z ∈ closedBall (freeHillValue n : ℂ) (n : ℝ) := by
        change dist z (freeHillValue n : ℂ) ≤ (n : ℝ)
        rw [dist_eq_norm]
        linarith [norm_nonneg q]
      have hp := ComplexAnalysis.analyticOrderNatAt_pos_of_zero (ha z hzk)
        (ComplexAnalysis.analyticOrderAt_ne_top_on_connected
          (isConnected_closedBall hnpos.le).isPreconnected ha
          (sphere_subset_closedBall hb) hb0 hzk) hz0
      have hp' : 0 < ({x,y} : Multiset ℂ).count z := by
        rw [← horder z, if_pos hzk]
        exact hp
      simpa using Multiset.count_pos.mp hp'
    · rintro (rfl | rfl) <;> assumption
  have hord (z : ℂ) (hz : z ∈ closedBall (freeHillValue n : ℂ) (n : ℝ)) :
      analyticOrderNatAt (hillL2Radicand (SpectralWeight.one.toCoeff q)) z =
        ({x,y} : Multiset ℂ).count z := by simpa only [if_pos hz] using horder z
  rcases le_total x.re y.re with hle | hle
  · exact ⟨⟨x.re,y.re,hle,hxc.symm ▸ hx,hyc.symm ▸ hy,hxc.symm ▸ hx0,hyc.symm ▸ hy0,
      (by simpa only [hxc,hyc] using hzeros), (by simpa only [hxc,hyc] using hord)⟩⟩
  · exact ⟨⟨y.re,x.re,hle,hyc.symm ▸ hy,hxc.symm ▸ hx,hyc.symm ▸ hy0,hxc.symm ▸ hx0,
      (by simpa only [hxc,hyc,or_comm] using hzeros),
      (by simpa only [hxc,hyc,Multiset.pair_comm y x] using hord)⟩⟩

/-- The order and the unordered zero set uniquely determine the ordered pair. -/
theorem HillRealHighGapPair.endpoints_unique (q : Coeff 2) (n : ℕ) (hn : 1 ≤ n)
    (p r : HillRealHighGapPair q n) : p.left = r.left ∧ p.right = r.right := by
  have hp := (r.zeros_iff p.left (openHillStrip_subset n
    (hillClosedBall_subset_openStrip n hn p.left_mem))).mp p.left_zero
  have hp' := (r.zeros_iff p.right (openHillStrip_subset n
    (hillClosedBall_subset_openStrip n hn p.right_mem))).mp p.right_zero
  have hr := (p.zeros_iff r.left (openHillStrip_subset n
    (hillClosedBall_subset_openStrip n hn r.left_mem))).mp r.left_zero
  have hr' := (p.zeros_iff r.right (openHillStrip_subset n
    (hillClosedBall_subset_openStrip n hn r.right_mem))).mp r.right_zero
  simp only [Complex.ofReal_inj] at hp hp' hr hr'
  rcases hp with hp | hp <;> rcases hp' with hp' | hp' <;>
    rcases hr with hr | hr <;> rcases hr' with hr' | hr' <;>
    constructor <;> linarith [p.ordered, r.ordered]

end NLS.KdV
