import NLS.ZakharovShabat.AppendixDReciprocalBounds
import NLS.SequenceSpaces.ReciprocalColumnHeadTail
import NLS.SequenceSpaces.FourierTail
import NLS.ComplexAnalysis.SignedProductEstimates

/-! # The small-factor cutoff in the proof of Lemma D.6 -/
noncomputable section
open Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The source head/tail estimate with signed indices and c on both terms. -/
theorem norm_appendixDReciprocalTerm_le_head_tail (hp : p ≠ ⊤)
    (r : Coeff ⊤) (a : Coeff p) {c : ℝ} {N : ℕ}
    (hc : 0 < c) (hsep : AppendixDReferenceSeparated r c N)
    {n : ℤ} (hn : N ≤ n.natAbs) (hn0 : n ≠ 0)
    (K : ℕ) (hK : 2*K ≤ n.natAbs) {z : ℂ} (hz : z ∈ refinedResonantDisk n) (m : ℤ) :
    ‖appendixDReciprocalTerm r a n z m‖ ≤
      c*((2/(n.natAbs:ℝ))*‖a‖+‖Coeff.fourierTail (K+1) a‖) := by
  by_cases hmn : m = n
  · simp only [appendixDReciprocalTerm,if_pos hmn,norm_zero]
    positivity
  have h := (appendixDReciprocalTerm_bounds hp r a hc hsep hn hz).2.2 m
  have he : ‖NLS.Fourier.hilbertKernel (n-m)‖ = ((n-m).natAbs:ℝ)⁻¹ := by
    rw [NLS.Fourier.hilbertKernel,norm_neg,norm_inv,Complex.norm_intCast,
      ← Int.cast_abs,← Int.natCast_natAbs]
    simp
  rw [he,← div_eq_mul_inv] at h
  apply h.trans
  have hbound := Coeff.reciprocalEntry_le_head_tail n hn0 K hK a m hmn
  have hI : Finset.Icc (-(K:ℤ)) (K:ℤ) = Coeff.lowFrequencies (K+1) := by
    ext j
    simp only [Finset.mem_Icc,Coeff.mem_lowFrequencies]
    omega
  rw [hI] at hbound
  exact mul_le_mul_of_nonneg_left hbound hc.le

/-- One positive cutoff makes every retained factor small on every selected disc. -/
theorem exists_appendixDReciprocalTerm_uniform_cutoff (hp : p ≠ ⊤)
    (r : Coeff ⊤) (a : Coeff p) {c : ℝ} {N : ℕ}
    (hc : 0 < c) (hsep : AppendixDReferenceSeparated r c N)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℕ, N ≤ M ∧ 0 < M ∧ ∀ n : ℤ, M ≤ n.natAbs →
      ∀ z ∈ refinedResonantDisk n, ∀ m : ℤ,
        ‖appendixDReciprocalTerm r a n z m‖ < ε := by
  have ht : Tendsto (fun K : ℕ => ‖Coeff.fourierTail K a‖) atTop (𝓝 0) := by
    simpa only [norm_zero] using (Coeff.tendsto_fourierTail hp a).norm
  obtain ⟨K,hK⟩ := eventually_atTop.mp (ht.eventually_lt_const (div_pos hε (by positivity : 0 < 2*c)))
  obtain ⟨L,hL⟩ := exists_nat_gt (4*c*‖a‖/ε)
  refine ⟨max N (max (2*K) (L+1)),le_max_left _ _,by omega,?_⟩
  intro n hn z hz m
  have hnN : N ≤ n.natAbs := by omega
  have hnK : 2*K ≤ n.natAbs := by omega
  have hnL : L < n.natAbs := by omega
  have hn0 : n ≠ 0 := by intro he; subst n; simp at hnL
  have hnR : 0 < (n.natAbs:ℝ) := by exact_mod_cast Int.natAbs_pos.mpr hn0
  have hlarge : 4*c*‖a‖ < ε*(n.natAbs:ℝ) := by
    have hLn : (L:ℝ) < (n.natAbs:ℝ) := by exact_mod_cast hnL
    have hh := (div_lt_iff₀ hε).mp (hL.trans hLn)
    nlinarith
  have hhead : (2*c*‖a‖)/(n.natAbs:ℝ) < ε/2 :=
    (div_lt_div_iff₀ hnR (by norm_num : (0:ℝ) < 2)).mpr (by nlinarith)
  have htail : c*‖Coeff.fourierTail (K+1) a‖ < ε/2 := by
    have hh := (lt_div_iff₀ (by positivity : 0 < 2*c)).mp (hK (K+1) (by omega))
    nlinarith
  apply (norm_appendixDReciprocalTerm_le_head_tail hp r a hc hsep hnN hn0 K hnK hz m).trans_lt
  calc
    _ = (2*c*‖a‖)/(n.natAbs:ℝ)+c*‖Coeff.fourierTail (K+1) a‖ := by ring
    _ < ε := by linarith

/-- The half-unit hypothesis of D.1 holds uniformly after one tail cutoff. -/
theorem exists_appendixDReciprocalTerm_half_cutoff (hp : p ≠ ⊤)
    (r : Coeff ⊤) (a : Coeff p) {c : ℝ} {N : ℕ}
    (hc : 0 < c) (hsep : AppendixDReferenceSeparated r c N) :
    ∃ M : ℕ, N ≤ M ∧ 0 < M ∧ ∀ n : ℤ, M ≤ n.natAbs →
      ∀ z ∈ refinedResonantDisk n, ∀ m : ℤ,
        ‖appendixDReciprocalTerm r a n z m‖ ≤ (1:ℝ)/2 := by
  obtain ⟨M,hNM,hM,hb⟩ := exists_appendixDReciprocalTerm_uniform_cutoff hp r a hc hsep
    (by norm_num : (0:ℝ) < 1/2)
  exact ⟨M,hNM,hM,fun n hn z hz m => (hb n hn z hz m).le⟩

/-- After the cutoff, D.1 gives an inequality for the actual relative product. -/
theorem exists_appendixDRelativeProduct_signed_bound (hp : p ≠ ⊤)
    (r : Coeff ⊤) (a : Coeff p) {c : ℝ} {N : ℕ}
    (hc : 0 < c) (hsep : AppendixDReferenceSeparated r c N) :
    ∃ M : ℕ, N ≤ M ∧ 0 < M ∧ ∀ n : ℤ, M ≤ n.natAbs →
      ∀ z ∈ refinedResonantDisk n,
        ‖appendixDRelativeProductError r a n z‖ ≤
          ‖∑' m, appendixDReciprocalTerm r a n z m‖ *
            Real.exp (∑' m, ‖appendixDReciprocalTerm r a n z m‖) +
          (∑' m, ‖appendixDReciprocalTerm r a n z m‖^2) *
            Real.exp ((∑' m, ‖appendixDReciprocalTerm r a n z m‖) +
              (∑' m, ‖appendixDReciprocalTerm r a n z m‖)^2) := by
  obtain ⟨M,hNM,hM,hhalf⟩ := exists_appendixDReciprocalTerm_half_cutoff hp r a hc hsep
  refine ⟨M,hNM,hM,?_⟩
  intro n hn z hz
  have hnN := hNM.trans hn
  rw [appendixDRelativeProductError_eq r a hc hsep hnN hz]
  exact NLS.ComplexAnalysis.norm_tprod_one_add_sub_one_le_signed_sum
    (appendixDReciprocalTerm r a n z)
    (appendixDReciprocalTerm_bounds hp r a hc hsep hnN hz).1 (hhalf n hn z hz)

end NLS.ZakharovShabat
