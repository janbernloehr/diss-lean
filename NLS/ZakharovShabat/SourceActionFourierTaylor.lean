import NLS.ZakharovShabat.SourceActionSequenceExponent
import NLS.ZakharovShabat.SourceBirkhoffImageInverse
import NLS.ZakharovShabat.SourceBirkhoffFourier

/-! # The leading Fourier term of the original action sequence

The introduction, printed p. 10, identifies the leading actions with
squared Fourier coefficients. The remainder here is little-o of the
squared source norm in the full half-exponent sequence norm.
-/

noncomputable section
open Set Complex Filter Topology Asymptotics
open scoped ENNReal ComplexConjugate
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderTriple p q]

/-- The leading physical Fourier actions, in the source's signed convention. -/
def sourceFourierActionSequence (φ : CoeffPair p) : Coeff q :=
  Coeff.doublingProduct (Coeff.reflection φ.fst) φ.snd

@[simp] theorem sourceFourierActionSequence_apply (φ : CoeffPair p) (n : ℤ) :
    sourceFourierActionSequence (q := q) φ n = φ.fst (-n) * φ.snd n := rfl

/-- On the real source, each leading action is the squared physical Fourier modulus. -/
theorem sourceFourierActionSequence_real (φ : realTypeSourceSubmodule p) (n : ℤ) :
    sourceFourierActionSequence (q := q) φ.val n = (‖φ.val.fst (-n)‖^2 : ℝ) := by
  rw [sourceFourierActionSequence_apply]
  have hr : φ.val.snd n = conj (φ.val.fst (-n)) := φ.property n
  rw [hr, Complex.mul_conj', Complex.ofReal_pow]

/-- The rectangular Fourier normalization gives exactly the same leading sequence. -/
theorem quadraticActionsExponent_sourceBirkhoffFourier (φ : CoeffPair p) :
    quadraticActionsExponent (q := q) (sourceBirkhoffFourier φ) =
      sourceFourierActionSequence φ := by
  ext n
  rw [quadraticActionsExponent_apply, sourceBirkhoffFourier_fst,
    sourceBirkhoffFourier_snd, sourceFourierActionSequence_apply]
  have hs : (Real.sqrt 2 : ℂ)^2 = 2 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hn : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)).ne'
  field_simp [hn, I_ne_zero]
  ring_nf
  simp only [hs, I_sq]
  ring

private theorem norm_quadraticActionsExponent_sub_le (z w : Coeff p × Coeff p) :
    ‖quadraticActionsExponent (q := q) z - quadraticActionsExponent w‖ ≤
      ‖z-w‖ * (‖z‖+‖w‖) := by
  have he : quadraticActionsExponent (q := q) z - quadraticActionsExponent w =
      (1/2 : ℂ) • (Coeff.doublingProduct (z.1-w.1) (z.1+w.1) +
        Coeff.doublingProduct (z.2-w.2) (z.2+w.2)) := by
    ext n
    simp only [quadraticActionsExponent_apply, lp.coeFn_sub, Pi.sub_apply,
      lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, lp.coeFn_add, Pi.add_apply,
      Coeff.doublingProduct_apply]
    ring
  have hx : ‖Coeff.doublingProduct (p := q) (z.1-w.1) (z.1+w.1)‖ ≤
      ‖z-w‖ * (‖z‖+‖w‖) :=
    (Coeff.norm_doublingProduct_le _ _).trans
      (mul_le_mul (norm_fst_le (z-w))
        ((norm_add_le _ _).trans (add_le_add (norm_fst_le z) (norm_fst_le w)))
        (norm_nonneg _) (norm_nonneg _))
  have hy : ‖Coeff.doublingProduct (p := q) (z.2-w.2) (z.2+w.2)‖ ≤
      ‖z-w‖ * (‖z‖+‖w‖) :=
    (Coeff.norm_doublingProduct_le _ _).trans
      (mul_le_mul (norm_snd_le (z-w))
        ((norm_add_le _ _).trans (add_le_add (norm_snd_le z) (norm_snd_le w)))
        (norm_nonneg _) (norm_nonneg _))
  rw [he, norm_smul]
  have hsum := norm_add_le (Coeff.doublingProduct (p := q) (z.1-w.1) (z.1+w.1))
    (Coeff.doublingProduct (p := q) (z.2-w.2) (z.2+w.2))
  have hc : ‖(1/2 : ℂ)‖ = (1/2 : ℝ) := by norm_num
  rw [hc]
  linarith

namespace SourceBirkhoffMapComplexData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- The entire original action sequence has its Fourier quadratic leading term,
with a little-o remainder in the half-exponent norm. -/
theorem actionSequence_fourier_isLittleO
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s) :
    (fun φ => sourceActionSequence (q := q) hp hp1 s φ - sourceFourierActionSequence φ)
      =o[𝓝 (0 : CoeffPair p)] (fun φ => ‖φ‖^2) := by
  have h0 : (0 : CoeffPair p) ∈ W := D.real_subset (0 : realTypeSourceSubmodule p).property
  have hd : HasFDerivAt (sourceBirkhoffMap hp hp1 s) sourceBirkhoffFourier 0 := by
    rw [← D.jacobian_zero]
    exact (D.analytic 0 h0).differentiableAt.hasFDerivAt
  have hr : (fun φ => sourceBirkhoffMap hp hp1 s φ - sourceBirkhoffFourier φ)
      =o[𝓝 (0 : CoeffPair p)] (fun φ => φ) := by
    simpa only [D.birkhoff_map_zero, sub_zero] using hd.isLittleO
  have hb : (sourceBirkhoffMap hp hp1 s)
      =O[𝓝 (0 : CoeffPair p)] (fun φ => φ) := by
    simpa only [D.birkhoff_map_zero, sub_zero] using hd.isBigO_sub
  have hl := (sourceBirkhoffFourier (p := p)).isBigO_id (𝓝 (0 : CoeffPair p))
  have hbound : (fun φ => sourceActionSequence (q := q) hp hp1 s φ -
      sourceFourierActionSequence φ) =O[𝓝 (0 : CoeffPair p)]
      (fun φ => ‖sourceBirkhoffMap hp hp1 s φ - sourceBirkhoffFourier φ‖ *
        (‖sourceBirkhoffMap hp hp1 s φ‖ + ‖sourceBirkhoffFourier φ‖)) := by
    apply IsBigO.of_norm_le
    intro φ
    rw [← quadraticActionsExponent_sourceBirkhoffFourier]
    exact norm_quadraticActionsExponent_sub_le _ _
  simpa only [← pow_two] using
    hbound.trans_isLittleO (hr.norm_norm.mul_isBigO (hb.norm_norm.add hl.norm_norm))

/-- One source neighborhood controls the full action remainder, hence every
coordinate simultaneously, and stays inside the original analytic domain. -/
theorem actionSequence_fourier_remainder
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, Metric.ball (0 : CoeffPair p) δ ⊆ W ∧
      ∀ φ : CoeffPair p, ‖φ‖ < δ →
        ‖sourceActionSequence (q := q) hp hp1 s φ - sourceFourierActionSequence φ‖ ≤
          ε * ‖φ‖^2 := by
  have h0 : (0 : CoeffPair p) ∈ W := D.real_subset (0 : realTypeSourceSubmodule p).property
  have h := (D.actionSequence_fourier_isLittleO (q := q)).bound hε
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp
    (inter_mem (D.source_open.mem_nhds h0) h)
  refine ⟨δ,hδ,fun φ hφ => (hball hφ).1,fun φ hφ => ?_⟩
  simpa only [Set.mem_ofPred_eq, Real.norm_eq_abs, abs_pow, abs_norm] using
    (hball (by simpa only [Metric.mem_ball, dist_zero_right] using hφ)).2

end SourceBirkhoffMapComplexData

/-- Construct the original analytic action sequence and its full-norm leading
term without assuming a Birkhoff map or an action expansion as input. -/
theorem exists_sourceActionFourierTaylor (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ A : CoeffPair p → Coeff q, ∃ W : Set (CoeffPair p),
      IsOpen W ∧ realTypeSourceLocus p ⊆ W ∧ AnalyticOnNhd ℂ A W ∧
      (∀ φ ∈ W, ∀ n, A φ n = sourceComplexAction hp hp1 n φ) ∧
      (fun φ => A φ - sourceFourierActionSequence φ)
        =o[𝓝 (0 : CoeffPair p)] (fun φ => ‖φ‖^2) := by
  obtain ⟨W₀,B,W,s,D⟩ := exists_sourceBirkhoffMap_complex_analytic hp hp1
  exact ⟨sourceActionSequence hp hp1 s,W,D.source_open,D.real_subset,
    D.actionSequence_analytic,D.actionSequence_apply,D.actionSequence_fourier_isLittleO⟩

end NLS.ZakharovShabat
