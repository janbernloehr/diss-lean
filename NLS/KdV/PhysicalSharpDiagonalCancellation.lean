import NLS.KdV.PhysicalFractionalDiagonalCancellation
import NLS.SequenceSpaces.WeightedFrequencyRemainders

/-! The actual corrected diagonal frequency has its sharp original
native Sobolev weight. The bound is locally uniform on a full complex
neighborhood, and the normalized tail vanishes at each fixed source. -/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.KdV
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {t : ℝ} {ht : 0≤t} {J : E →L[ℂ] PeriodOneHminusOne}

def PhysicalFrequencyParameterization.renormalizedCorrection
    (A : PhysicalFrequencyParameterization E t ht J) (n : ℕ+) (a : E) : ℂ :=
  A.physical.correction n (J a)+12*sourceComplexHigherAction (by norm_num) (by norm_num) (n:ℤ) 1
    (hillMiuraDiagonal (A.physical.psi.miura.lift (J a)))

def PhysicalFrequencyParameterization.diagonalRemainder
    (A : PhysicalFrequencyParameterization E t ht J) (n : ℕ+) (a : E) : ℂ :=
  A.renormalizedCorrection n a-A.physical.offDiagonalCorrection n (J a)

theorem PhysicalFrequencyParameterization.renormalizedCorrection_eq_original
    (A : PhysicalFrequencyParameterization E t ht J) (a : E) (ha : a∈A.domain)
    (p : RealPeriodOneHillPotential) (hp : J a=hillOriginalHminusSource p.val) (n : ℕ+) :
    A.renormalizedCorrection n a=A.physical.correction n (hillOriginalHminusSource p.val)+
      6*(hillRealGapIntegral p.val p.property.1 p.property.2 (n:ℕ) 0 : ℂ) := by
  have hpB : hillOriginalHminusSource p.val∈A.physical.domain := by
    rw [← hp]
    exact A.domain_subset ha
  have hI := A.physical.original_counterterm_eq_raw_action p hpB n
  rw [PhysicalFrequencyParameterization.renormalizedCorrection,hp,← hI]

theorem PhysicalFrequencyParameterization.exists_sharp_diagonal_cancellation_decay
    (A : PhysicalFrequencyParameterization E t ht J) (ht1 : t≤1)
    (q : E) (hq : q∈A.domain) (hqr : IsRealPeriodOneHminusOne (J q)) :
    ∃ T : Set E, IsOpen T ∧ q∈T ∧ T⊆A.domain ∧ ∃ K : ℕ, ∃ M : ℝ, 0≤M ∧
      (∀ a∈T, ∀ n : ℕ+, K≤(n:ℤ).natAbs →
        Weight.sobolev (3*t-1) (n:ℤ)*‖A.diagonalRemainder n a‖≤M) ∧
      ∀ a∈T, Tendsto (fun n : ℕ => Weight.sobolev (3*t-1) ((n+1:ℕ):ℤ)*
        ‖A.diagonalRemainder ⟨n+1,by omega⟩ a‖) atTop (𝓝 0) := by
  let L := normalizedWeightedSourceCLM (p := 2) (sourceSobolevSpectralWeight t ht)
  obtain ⟨Td,hTd,hqTd,hTdA,K,Md,hMd,hdiag⟩ :=
    A.exists_fractional_diagonal_cancellation_bounds t ht ht1 le_rfl q hq hqr
  obtain ⟨G,hG,hqG,R,hR,hgap⟩ := exists_local_sobolevSquaredGap_bounds t ht (A.normalizedSource q)
  obtain ⟨Tg,hTg,hqTg,hTgA,hTgG,_hTgB⟩ := exists_open_common_pullback_domain A.domain A.domain_open q hq
    A.normalizedSource A.analytic_source.continuousOn G hG hqG
    J J.continuous A.physical.domain A.physical.domain_open (A.domain_subset hq)
  let T := Td∩Tg
  have hTA : T⊆A.domain := fun _ ha => hTdA ha.1
  have hrows : ∀ a∈T, ∃ g : Coeff 1, ‖g‖≤R ∧ ∀ n : ℕ+, K≤(n:ℤ).natAbs →
      Weight.sobolev (3*t-1) (n:ℤ)*‖A.diagonalRemainder n a‖≤Md*‖g (n:ℤ)‖ := by
    intro a ha
    obtain ⟨g,hgn,hquad,_hpoint⟩ := hgap (A.normalizedSource a) (hTgG a ha.2)
    refine ⟨g,hgn,?_⟩
    intro n hn
    let γ := sourcePeriodicGapDisplacement (by norm_num) (by norm_num)
      (hillMiuraDiagonal (A.physical.psi.miura.lift (J a))) (n:ℤ)
    have hd : Weight.sobolev (t-1) (n:ℤ)*‖A.diagonalRemainder n a‖≤‖γ‖^2*Md :=
      (hdiag a ha.1 n hn).1
    have hg : ‖g (n:ℤ)‖=Weight.sobolev (2*t) (n:ℤ)*‖γ‖^2 := by
      have h := hquad (n:ℤ)
      rw [A.source_identity a (hTA ha)] at h
      exact h
    have h := Coeff.sobolev_gap_remainder_bound t (n:ℤ) γ (A.diagonalRemainder n a) Md hd
    rw [← hg] at h
    exact h
  refine ⟨T,hTd.inter hTg,⟨hqTd,hqTg⟩,hTA,K,Md*R,mul_nonneg hMd hR,?_,?_⟩
  · intro a ha n hn
    obtain ⟨g,hgn,hb⟩ := hrows a ha
    exact (hb n hn).trans (mul_le_mul_of_nonneg_left
      ((lp.norm_apply_le_norm (by norm_num : (1 : ℝ≥0∞)≠0) g (n:ℤ)).trans hgn) hMd)
  · intro a ha
    obtain ⟨g,_hgn,hb⟩ := hrows a ha
    exact Coeff.tendsto_positive_weighted_remainder_of_majorant (Weight.sobolev (3*t-1))
      (fun n => ((Weight.sobolev (3*t-1)).positive n).le) (fun n => A.diagonalRemainder n a) g Md K hb

end NLS.KdV
