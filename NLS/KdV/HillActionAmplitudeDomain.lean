import NLS.KdV.HillCanonicalActionRatioReal
import NLS.KdV.HillCanonicalOffIndexBoundedDomain

/-! ONE native complex neighborhood before ALL n supports the positive
principal action-amplitude branch and uniform normalized-ratio bounds.
Uniform high ratios and finitely many positive low ratios supply it. -/
noncomputable section
open Set Metric Complex Filter Topology
open scoped Classical
namespace NLS.KdV

structure HillActionAmplitudeBall where
  center : PeriodOneHminusOne
  center_real : IsRealPeriodOneHminusOne center
  radius : ℝ
  radius_pos : 0 < radius
  subset : ball center radius ⊆ hillHminusCanonicalRatioDomain ∩ hillHminusOffIndexBoundedDomain
  positive : ∀ q ∈ ball center radius, ∀ n : ℕ+, 0 < (hillHminusCanonicalActionRatio n q).re
  bound : ℝ
  bound_pos : 0 < bound
  norm_bound : ∀ q ∈ ball center radius, ∀ n : ℕ+, ‖hillHminusCanonicalActionRatio n q‖ ≤ bound

namespace HillActionAmplitudeBall

def source (B : HillActionAmplitudeBall) : Set PeriodOneHminusOne := ball B.center B.radius

theorem source_open (B : HillActionAmplitudeBall) : IsOpen B.source := isOpen_ball

end HillActionAmplitudeBall

theorem exists_hillActionAmplitudeBall (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) :
    ∃ B : HillActionAmplitudeBall, q ∈ B.source := by
  have hqR := real_mem_hillHminusCanonicalRatioDomain q hr
  obtain ⟨N,Ut,_,hUt,hqt,hUtR,hhigh⟩ := exists_hillHminusCanonicalActionRatio_uniform_high q hqR (1/2) (by norm_num)
  have hfinite : {n : ℕ+ | (n:ℕ) < N}.Finite :=
    (Set.finite_Iio N).preimage (fun _ _ _ _ h => PNat.coe_injective h)
  let F := hfinite.toFinset
  have hlow : ∀ᶠ a in 𝓝 q, ∀ n ∈ F,
      0 < (hillHminusCanonicalActionRatio n a).re ∧
        ‖hillHminusCanonicalActionRatio n a‖ < ‖hillHminusCanonicalActionRatio n q‖+1 := by
    rw [Finset.eventually_all]
    intro n _
    have hcont : ContinuousAt (hillHminusCanonicalActionRatio n) q :=
      (analyticOnNhd_hillHminusCanonicalActionRatio n q hqR).continuousAt
    have hre : ContinuousAt (fun a => (hillHminusCanonicalActionRatio n a).re) q :=
      Complex.continuous_re.continuousAt.comp hcont
    have hp := (hillHminusCanonicalActionRatio_real_positive n q hr).2
    exact (hre.eventually (Ioi_mem_nhds hp)).and
      (hcont.norm.eventually (Iio_mem_nhds (by linarith : ‖hillHminusCanonicalActionRatio n q‖ < ‖hillHminusCanonicalActionRatio n q‖+1)))
  have hqW := real_mem_hillHminusOffIndexBoundedDomain q hr
  obtain ⟨r,hrpos,hball⟩ := Metric.mem_nhds_iff.mp
    (Filter.inter_mem (Filter.inter_mem (hUt.mem_nhds hqt) hlow)
      (isOpen_hillHminusOffIndexBoundedDomain.mem_nhds hqW))
  let L := ∑ n ∈ F, (‖hillHminusCanonicalActionRatio n q‖+1)
  have hL : 0 ≤ L := Finset.sum_nonneg (fun n _ => by positivity)
  have hdata (a : PeriodOneHminusOne) (ha : a ∈ ball q r) (n : ℕ+) :
      0 < (hillHminusCanonicalActionRatio n a).re ∧ ‖hillHminusCanonicalActionRatio n a‖ ≤ L+2 := by
    by_cases hn : N ≤ (n:ℕ)
    · have h := hhigh n hn a (hball ha).1.1
      have hre := Complex.re_le_norm (1-hillHminusCanonicalActionRatio n a)
      rw [norm_sub_rev] at hre
      simp only [Complex.sub_re,Complex.one_re] at hre
      have hnorm := norm_add_le (hillHminusCanonicalActionRatio n a-1) (1:ℂ)
      rw [sub_add_cancel,norm_one] at hnorm
      constructor <;> linarith
    · have hnF : n ∈ F := by rw [Set.Finite.mem_toFinset]; exact lt_of_not_ge hn
      have h := (hball ha).1.2 n hnF
      have hsingle : ‖hillHminusCanonicalActionRatio n q‖+1 ≤ L := by
        dsimp only [L]
        exact Finset.single_le_sum (fun k _ => show (0:ℝ) ≤ ‖hillHminusCanonicalActionRatio k q‖+1 from by positivity) hnF
      exact ⟨h.1,h.2.le.trans (by linarith)⟩
  refine ⟨⟨q,hr,r,hrpos,(fun a ha => ⟨hUtR (hball ha).1.1,(hball ha).2⟩),
    (fun a ha n => (hdata a ha n).1),L+2,by linarith,(fun a ha n => (hdata a ha n).2)⟩,mem_ball_self hrpos⟩

def hillHminusActionAmplitudeDomain : Set PeriodOneHminusOne :=
  ⋃ B : HillActionAmplitudeBall, B.source

theorem isOpen_hillHminusActionAmplitudeDomain : IsOpen hillHminusActionAmplitudeDomain :=
  isOpen_iUnion (fun B => B.source_open)

theorem real_mem_hillHminusActionAmplitudeDomain (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) : q ∈ hillHminusActionAmplitudeDomain := by
  obtain ⟨B,hB⟩ := exists_hillActionAmplitudeBall q hr
  exact mem_iUnion.mpr ⟨B,hB⟩

theorem hillHminusActionAmplitudeDomain_subset_ratio :
    hillHminusActionAmplitudeDomain ⊆ hillHminusCanonicalRatioDomain := by
  intro q hq
  obtain ⟨B,hB⟩ := mem_iUnion.mp hq
  exact (B.subset hB).1

theorem hillHminusActionAmplitudeDomain_subset_bounded :
    hillHminusActionAmplitudeDomain ⊆ hillHminusOffIndexBoundedDomain := by
  intro q hq
  obtain ⟨B,hB⟩ := mem_iUnion.mp hq
  exact (B.subset hB).2

theorem hillHminusActionRatio_re_pos_on_amplitude_domain (n : ℕ+) (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusActionAmplitudeDomain) : 0 < (hillHminusCanonicalActionRatio n q).re := by
  obtain ⟨B,hB⟩ := mem_iUnion.mp hq
  exact B.positive q hB n

theorem isConnected_hillHminusActionAmplitudeDomain : IsConnected hillHminusActionAmplitudeDomain := by
  let S : Set PeriodOneHminusOne := {q | IsRealPeriodOneHminusOne q}
  have hS : IsPreconnected S := isPreconnected_real_periodOneHminus
  have hzero : IsRealPeriodOneHminusOne (0 : PeriodOneHminusOne) := by intro k; simp
  have hpre (B : HillActionAmplitudeBall) : IsPreconnected (S ∪ B.source) :=
    hS.union B.center B.center_real (mem_ball_self B.radius_pos) (convex_ball _ _).isPreconnected
  have hcommon : (⋂ B : HillActionAmplitudeBall, S ∪ B.source).Nonempty :=
    ⟨0,mem_iInter.mpr (fun _ => Or.inl hzero)⟩
  have he : (⋃ B : HillActionAmplitudeBall, S ∪ B.source) = hillHminusActionAmplitudeDomain := by
    ext q
    constructor
    · intro hq
      obtain ⟨B,hqS | hqB⟩ := mem_iUnion.mp hq
      · exact real_mem_hillHminusActionAmplitudeDomain q hqS
      · exact mem_iUnion.mpr ⟨B,hqB⟩
    · intro hq
      obtain ⟨B,hqB⟩ := mem_iUnion.mp hq
      exact mem_iUnion.mpr ⟨B,Or.inr hqB⟩
  refine ⟨⟨0,real_mem_hillHminusActionAmplitudeDomain 0 hzero⟩,?_⟩
  rw [← he]
  exact isPreconnected_iUnion hcommon hpre

end NLS.KdV
