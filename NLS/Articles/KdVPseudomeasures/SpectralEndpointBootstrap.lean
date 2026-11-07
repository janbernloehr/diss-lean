import NLS.Articles.KdVPseudomeasures.SpectralInverseGapComparison
import NLS.SequenceSpaces.ScaledSobolevApproximation
import NLS.Fourier.PeriodicEndpointBounds

/-! Uniform endpoint regularity of the SAME original potential from stronger
ACTUAL canonical gap bounds,using genuine polynomial source weights and the
proved actual adapted-map inverse. -/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
open NLS.Fourier NLS.Fourier.SmoothPeriodicTest NLS.Fourier.PeriodicFourierLebesgue NLS.KdV

/-- The quantitative inverse-map cutoff already excludes the low index1.
The actual adapted map is not changed after its inverse has been constructed. -/
theorem source_inverse_cutoff_ge_two (r : ℝ) (hr : AdmissiblePredualOrder r)
    (m : ℝ) (hm : 1 ≤ m) (N : ℕ) (hN : 1 ≤ N)
    (hcut : ∀ n : ℕ, 1 ≤ n → N ≤ n → endpointHillConstant r*(n:ℝ)^(r-1/2)*(64*(2*m)) ≤ 1/2) : 2 ≤ N := by
  by_contra hh
  have he : N = 1 := by omega
  have hc := hcut 1 le_rfl (by omega)
  have hC : 24 ≤ endpointHillConstant r := by
    calc
      24 = endpointHillConstant 0 := by norm_num [endpointHillConstant]
      _ ≤ _ := endpointHillConstant_mono hr.1 hr.2
  norm_num only [Nat.cast_one, Real.one_rpow, mul_one] at hc
  nlinarith

/-- The ACTUAL original adapted image has stronger weighted membership with
uniform norm<=2R+G:the finite head is unchanged and both high tails use the
ACTUAL canonical gap bound. Odd physical modes remain zero. -/
theorem sourceAdaptedFourier_scaled_weight_bound (r : ℝ) (hr : AdmissiblePredualOrder r)
    (t : ℝ) (ht : 0 ≤ t) (htr : t ≤ r) (N : ℕ) (hN : 2 ≤ N)
    (R G : ℝ) (hR : 0 ≤ R) (hG : 0 ≤ G)
    (hcut : ∀ n : ℕ, 1 ≤ n → N ≤ n → endpointHillConstant r*(n:ℝ)^(r-1/2)*(64*R) ≤ 1/2)
    (q : Potential r) (hq : ‖q.val‖ ≤ R)
    (hgap : ∀ n : ℕ, 1 ≤ n → Weight.sobolev (-t) (n:ℤ)*‖sourceCanonicalGapValues r hr q (n:ℤ)‖ ≤ G) :
    ∃ y : PeriodicFourierLebesgue (2:ℝ)
        ((SpectralWeight.scaledSobolev (SpectralWeight.inverseHeadScale N) (r-t)
          (SpectralWeight.inverseHeadScale_pos_le_one N).1.le (by linarith)).negativeSobolev r) ⊤,
      y.val = (sourceAdaptedFourier r hr N q.val).val ∧ ‖y‖ ≤ 2*R+G := by
  let c := SpectralWeight.inverseHeadScale N
  have hc : 0 < c := (SpectralWeight.inverseHeadScale_pos_le_one N).1
  have hc1 : c ≤ 1 := (SpectralWeight.inverseHeadScale_pos_le_one N).2
  let w := SpectralWeight.scaledSobolev c (r-t) hc.le (by linarith)
  apply exists_of_endpoint_bound (w.negativeSobolev r) (sourceAdaptedFourier r hr N q.val).val (2*R+G) (by positivity)
  intro k
  by_cases hk : k.natAbs/2 < N
  · have hval : (sourceAdaptedFourier r hr N q.val).val (mode (-k)) = q.val.val (mode (-k)) := by
      rw [sourceAdaptedFourier_coefficients r hr N R hR hcut q.val hq k,
        sourceAdaptedFourierValues, evenTailReplacement_low N _ _ k hk]
    have hkn : (k.natAbs:ℝ) ≤ 2*(N:ℝ) := by exact_mod_cast (show k.natAbs ≤ 2*N by omega)
    have hkr : |(k:ℝ)| ≤ 2*(N:ℝ) := by simpa only [Nat.cast_natAbs, Int.cast_abs] using hkn
    have hw : w k ≤ 2 := SpectralWeight.scaledSobolev_inverseHeadScale_le_two N (r-t) (by linarith) (by linarith [hr.2]) k hkr
    have hbase := weight_mul_norm_coefficient_le (Weight.sobolev (-r)) ⊤ q.val k
    rw [hval, SpectralWeight.negativeSobolev_eq_product]
    calc
      _ = w k*(Weight.sobolev (-r) k*‖q.val.val (mode (-k))‖) := by ring
      _ ≤ 2*(Weight.sobolev (-r) k*‖q.val.val (mode (-k))‖) :=
        mul_le_mul_of_nonneg_right hw (by positivity [(Weight.sobolev (-r)).positive k])
      _ ≤ 2*R := mul_le_mul_of_nonneg_left (hbase.trans hq) (by norm_num)
      _ ≤ 2*R+G := le_add_of_nonneg_right hG
  · have hhigh : N ≤ k.natAbs/2 := by omega
    by_cases hpar : k % 2 = 0
    · let n := k.natAbs/2
      have hn : N ≤ n := hhigh
      have hp := sourceAdaptedFourier_tail_le_canonical_gap r hr N hN R hR hcut q hq n hn
      have he : k = 2*(n:ℤ) ∨ k = -(2*(n:ℤ)) := by
        have ha := Int.natCast_natAbs (n := k)
        by_cases hks : 0 ≤ k
        · rw [abs_of_nonneg hks] at ha
          left
          dsimp [n]
          omega
        · rw [abs_of_neg (by omega)] at ha
          right
          dsimp [n]
          omega
      have hpk : ‖(sourceAdaptedFourier r hr N q.val).val (mode (-k))‖ ≤ ‖sourceCanonicalGapValues r hr q (n:ℤ)‖ := by
        rcases he with he | he
        · rw [he]
          exact hp.1
        · rw [he, neg_neg]
          exact hp.2
      have hwk : w.negativeSobolev r k ≤ Weight.sobolev (-t) (n:ℤ) := by
        rcases he with he | he
        · rw [he]
          exact SpectralWeight.scaledNegativeSobolev_double_le c r t hc hc1 ht htr n
        · rw [he, SpectralWeight.negativeSobolev_neg]
          exact SpectralWeight.scaledNegativeSobolev_double_le c r t hc hc1 ht htr n
      exact ((mul_le_mul hwk hpk (norm_nonneg _) ((Weight.sobolev (-t)).positive _).le).trans
        (hgap n (by omega))).trans (le_add_of_nonneg_left (by positivity : 0 ≤ 2*R))
    · have hval : (sourceAdaptedFourier r hr N q.val).val (mode (-k)) = q.val.val (mode (-k)) := by
        rw [sourceAdaptedFourier_coefficients r hr N R hR hcut q.val hq k]
        simp only [sourceAdaptedFourierValues, evenTailReplacement, hpar, false_and, ite_false]
      have hzero : q.val.val (mode (-k)) = 0 := by
        have he : k = 2*(k/2)+1 := by omega
        rw [he]
        exact (Distribution.toTempered_period_one_iff_odd q.val.val).mp q.property.2.2 (k/2)
      rw [hval, hzero, norm_zero, mul_zero]
      positivity

/-- Uniform stronger endpoint regularity of the SAME original potential from
a base original norm bound and a stronger ACTUAL canonical gap bound. All
constants,cutoffs and the auxiliary source weight precede the potential. -/
theorem source_uniform_endpoint_bootstrap (r : ℝ) (hr : AdmissiblePredualOrder r)
    (t : ℝ) (ht : 0 ≤ t) (htr : t ≤ r) (R G : ℝ) (hR : 0 ≤ R) (hG : 0 ≤ G) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q : Potential r, ‖q.val‖ ≤ R →
      (∀ n : ℕ, 1 ≤ n → Weight.sobolev (-t) (n:ℤ)*‖sourceCanonicalGapValues r hr q (n:ℤ)‖ ≤ G) →
      ∃ p : Potential t, p.val.val = q.val.val ∧ ‖p.val‖ ≤ C := by
  let m := 4*(R+G+1)
  have hm : 1 ≤ m := by dsimp [m]; linarith
  obtain ⟨N, hN, hcut, hgain⟩ := source_uniform_weighted_inverse_restriction r hr m (by linarith)
  have hN2 := source_inverse_cutoff_ge_two r hr m hm N hN hcut
  let c := SpectralWeight.inverseHeadScale N
  have hc : 0 < c := (SpectralWeight.inverseHeadScale_pos_le_one N).1
  have hc1 : c ≤ 1 := (SpectralWeight.inverseHeadScale_pos_le_one N).2
  let w := SpectralWeight.scaledSobolev c (r-t) hc.le (by linarith)
  have hcp : 0 < c^(r-t) := Real.rpow_pos_of_pos hc _
  refine ⟨m/c^(r-t), by positivity, fun q hq hgap => ?_⟩
  have hcutR (n : ℕ) (hn : 1 ≤ n) (hNN : N ≤ n) : endpointHillConstant r*(n:ℝ)^(r-1/2)*(64*R) ≤ 1/2 := by
    have hh := hcut n hn hNN
    have hc' : 0 ≤ endpointHillConstant r*(n:ℝ)^(r-1/2) := by positivity [endpointHillConstant_pos r hr.2]
    have hi := mul_le_mul_of_nonneg_left (show 64*R ≤ 64*(2*m) by dsimp [m]; linarith) hc'
    nlinarith
  obtain ⟨y, hy, hyn⟩ := sourceAdaptedFourier_scaled_weight_bound r hr t ht htr N hN2 R G hR hG hcutR q hq hgap
  have hyhalf : ‖y‖ ≤ m/2 := hyn.trans (by dsimp [m]; linarith)
  obtain ⟨p, hp, hpn⟩ := hgain w q.val (by dsimp [m]; linarith) y hyhalf hy
  obtain ⟨u, hu, hun⟩ := exists_of_endpoint_weight_lower_bound (w.negativeSobolev r) (Weight.sobolev (-t))
    (c^(r-t)) hcp (fun k => (SpectralWeight.scaledNegativeSobolev_bounds c r t hc hc1 htr k).1) p
  have huq : u.val = q.val.val := hu.trans hp
  refine ⟨⟨u, huq.symm ▸ q.property⟩, huq, ?_⟩
  exact hun.trans (div_le_div_of_nonneg_right hpn hcp.le)

end NLS.Articles.KdVPseudomeasures
