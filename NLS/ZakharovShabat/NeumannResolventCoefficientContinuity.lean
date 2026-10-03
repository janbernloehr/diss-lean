import NLS.ZakharovShabat.DoubleResolventCoefficientContinuity
import NLS.SequenceSpaces.ExponentEmbedding
import NLS.ZakharovShabat.HeightResolvent

/-! # Full Neumann resolvent continuity from coefficient limits

A fixed-point estimate on summable output turns convergence of the double
free resolvent into convergence of the full resolvent. The common Neumann
margin is explicit and does not require norm convergence of the potentials.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The Neumann resolvent with its summable-output regularity retained. -/
def neumannResolventToL1 (hp : p ≠ ⊤) (φ : PairSpace p) (z : ℂ)
    (hz : z ∉ freeLattice) (hφ : NeumannCondition hp φ z hz) :
    PairSpace p →L[ℂ] PairSpace 1 :=
  (freeResolventToL1 hp z hz).comp (neumannCorrection hp φ z hz hφ)

/-- The resolvent satisfies the fixed-point equation on the summable output space. -/
theorem neumannResolventToL1_eq_add (hp : p ≠ ⊤) (φ : PairSpace p) (z : ℂ)
    (hz : z ∉ freeLattice) (hφ : NeumannCondition hp φ z hz) :
    neumannResolventToL1 hp φ z hz hφ = freeResolventToL1 hp z hz +
      ((freeResolventToL1 hp z hz).comp (potentialFromL1 φ)).comp
        (neumannResolventToL1 hp φ z hz hφ) := by
  apply ContinuousLinearMap.ext
  intro f
  have he := congrArg (freeResolventToL1 hp z hz) (neumannCorrection_right hp φ z hz hφ f)
  rw [map_sub, potentialFreeResolvent_eq_comp_L1] at he
  exact eq_add_of_sub_eq he

/-- Resolvent variation is controlled by double-resolvent variation, with a
fixed positive Neumann margin on the varying potential. -/
theorem norm_neumannResolventToL1_sub_le (hp : p ≠ ⊤) (φ ψ : PairSpace p) (z : ℂ)
    (hz : z ∉ freeLattice) (hφ : NeumannCondition hp φ z hz)
    (hψ : NeumannCondition hp ψ z hz) (c : ℝ) (hc : c < 1)
    (hbound : freeL1Bound p hp z hz * ‖φ‖ ≤ c) :
    ‖neumannResolventToL1 hp φ z hz hφ - neumannResolventToL1 hp ψ z hz hψ‖ ≤
      (‖neumannCorrection hp ψ z hz hψ‖/(1-c)) *
        ‖doubleResolvent hp φ z hz - doubleResolvent hp ψ z hz‖ := by
  let R := freeResolventToL1 hp z hz
  let Qφ := neumannResolventToL1 hp φ z hz hφ
  let Qψ := neumannResolventToL1 hp ψ z hz hψ
  let X := neumannCorrection hp ψ z hz hψ
  let Sφ := R.comp (potentialFromL1 φ)
  let Sψ := R.comp (potentialFromL1 ψ)
  let Δ := doubleResolvent hp φ z hz - doubleResolvent hp ψ z hz
  have hS : ‖Sφ‖ ≤ c := by
    calc
      _ ≤ ‖R‖*‖potentialFromL1 φ‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ freeL1Bound p hp z hz * ‖φ‖ :=
        mul_le_mul (norm_freeResolventToL1_le hp z hz) (norm_potentialFromL1_le φ)
          (norm_nonneg _) (freeL1Bound_nonneg p hp z hz)
      _ ≤ c := hbound
  have heΔ : Δ.comp X = Sφ.comp Qψ - Sψ.comp Qψ := by
    dsimp only [Δ, Sφ, Sψ, Qψ, neumannResolventToL1, doubleResolvent, R, X]
    rw [ContinuousLinearMap.sub_comp, potentialFreeResolvent_eq_comp_L1,
      potentialFreeResolvent_eq_comp_L1]
    simp only [ContinuousLinearMap.comp_assoc]
  have he : Qφ-Qψ = Sφ.comp (Qφ-Qψ) + Δ.comp X := by
    calc
      Qφ-Qψ = (R+Sφ.comp Qφ)-(R+Sψ.comp Qψ) :=
        congrArg₂ (fun A B : PairSpace p →L[ℂ] PairSpace 1 => A-B)
          (neumannResolventToL1_eq_add hp φ z hz hφ) (neumannResolventToL1_eq_add hp ψ z hz hψ)
      _ = _ := by rw [heΔ, ContinuousLinearMap.comp_sub]; abel
  have hn : ‖Qφ-Qψ‖ ≤ c*‖Qφ-Qψ‖ + ‖Δ‖*‖X‖ := by
    calc
      _ = ‖Sφ.comp (Qφ-Qψ) + Δ.comp X‖ := congrArg norm he
      _ ≤ ‖Sφ.comp (Qφ-Qψ)‖+‖Δ.comp X‖ := norm_add_le _ _
      _ ≤ (‖Sφ‖*‖Qφ-Qψ‖)+(‖Δ‖*‖X‖) :=
        add_le_add (ContinuousLinearMap.opNorm_comp_le _ _) (ContinuousLinearMap.opNorm_comp_le _ _)
      _ ≤ _ := by gcongr
  change ‖Qφ-Qψ‖ ≤ (‖X‖/(1-c))*‖Δ‖
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (sub_pos.mpr hc)).mpr
  nlinarith

/-- Bounded coefficientwise convergence gives convergence of the full
summable-output resolvent in any common Neumann region with a strict margin. -/
theorem tendsto_neumannResolventToL1_of_bounded_coefficientwise
    (hp : p ≠ ⊤) (hp1 : 1 < p) {α : Type*} {l : Filter α}
    (φ : α → PairSpace p) (ψ : PairSpace p)
    (hb : Bornology.IsBounded (range φ))
    (ht₁ : ∀ n : ℤ, Tendsto (fun k => (φ k).1 n) l (𝓝 (ψ.1 n)))
    (ht₂ : ∀ n : ℤ, Tendsto (fun k => (φ k).2 n) l (𝓝 (ψ.2 n)))
    (z : ℂ) (hz : z ∉ freeLattice)
    (hφ : ∀ k, NeumannCondition hp (φ k) z hz) (hψ : NeumannCondition hp ψ z hz)
    (c : ℝ) (hc : c < 1) (hbound : ∀ k, freeL1Bound p hp z hz * ‖φ k‖ ≤ c) :
    Tendsto (fun k => neumannResolventToL1 hp (φ k) z hz (hφ k)) l
      (𝓝 (neumannResolventToL1 hp ψ z hz hψ)) := by
  have hd := tendsto_doubleResolvent_of_bounded_coefficientwise hp hp1 φ ψ hb ht₁ ht₂ z hz
  have hn : Tendsto (fun k => ‖doubleResolvent hp (φ k) z hz-doubleResolvent hp ψ z hz‖) l (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp hd
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _)
    (fun k => norm_neumannResolventToL1_sub_le hp (φ k) ψ z hz (hφ k) hψ c hc (hbound k))
  simpa only [mul_zero] using hn.const_mul (‖neumannCorrection hp ψ z hz hψ‖/(1-c))

/-- Forgetting the summable regularity recovers the actual full base-space resolvent. -/
theorem resolvent_eq_inclusion_neumannResolventToL1
    (hp : p ≠ ⊤) (φ : PairSpace p) (z : ℂ) (hz : z ∉ freeLattice)
    (hφ : NeumannCondition hp φ z hz) :
    resolvent hp φ z =
      ((Coeff.exponentInclusion (show 1 ≤ p from Fact.out)).prodMap
        (Coeff.exponentInclusion (show 1 ≤ p from Fact.out))).comp
        (neumannResolventToL1 hp φ z hz hφ) := by
  rw [resolvent_eq_perturbed hp φ z hz hφ]
  apply ContinuousLinearMap.ext
  intro f
  apply Prod.ext <;> ext n
  · simp [perturbedResolvent, neumannResolventToL1, freeResolvent_fst_apply]
  · simp [perturbedResolvent, neumannResolventToL1, freeResolvent_snd_apply]

/-- Operator-norm convergence of the original resolvent under bounded
coefficientwise convergence, with a common strict Neumann bound. -/
theorem tendsto_resolvent_of_bounded_coefficientwise_neumann
    (hp : p ≠ ⊤) (hp1 : 1 < p) {α : Type*} {l : Filter α}
    (φ : α → PairSpace p) (ψ : PairSpace p)
    (hb : Bornology.IsBounded (range φ))
    (ht₁ : ∀ n : ℤ, Tendsto (fun k => (φ k).1 n) l (𝓝 (ψ.1 n)))
    (ht₂ : ∀ n : ℤ, Tendsto (fun k => (φ k).2 n) l (𝓝 (ψ.2 n)))
    (z : ℂ) (hz : z ∉ freeLattice)
    (hφ : ∀ k, NeumannCondition hp (φ k) z hz) (hψ : NeumannCondition hp ψ z hz)
    (c : ℝ) (hc : c < 1) (hbound : ∀ k, freeL1Bound p hp z hz * ‖φ k‖ ≤ c) :
    Tendsto (fun k => resolvent hp (φ k) z) l (𝓝 (resolvent hp ψ z)) := by
  let ι : PairSpace 1 →L[ℂ] PairSpace p :=
    (Coeff.exponentInclusion (show 1 ≤ p from Fact.out)).prodMap
      (Coeff.exponentInclusion (show 1 ≤ p from Fact.out))
  have ht := tendsto_neumannResolventToL1_of_bounded_coefficientwise hp hp1 φ ψ hb ht₁ ht₂ z hz hφ hψ c hc hbound
  have H := ((ContinuousLinearMap.compL ℂ (PairSpace p) (PairSpace 1) (PairSpace p)) ι).continuous.continuousAt.tendsto.comp ht
  simpa only [Function.comp_def, ContinuousLinearMap.compL_apply, ι,
    ← resolvent_eq_inclusion_neumannResolventToL1] using H

/-- A common height and strict Neumann margin exist for every bounded
coefficientwise convergent family. Thus the full resolvents converge without
an externally supplied smallness or spectral-membership hypothesis. -/
theorem exists_height_resolvent_tendsto_of_bounded_coefficientwise
    (hp : p ≠ ⊤) (hp1 : 1 < p) {α : Type*} {l : Filter α}
    (φ : α → PairSpace p) (ψ : PairSpace p)
    (hb : Bornology.IsBounded (range φ))
    (ht₁ : ∀ n : ℤ, Tendsto (fun k => (φ k).1 n) l (𝓝 (ψ.1 n)))
    (ht₂ : ∀ n : ℤ, Tendsto (fun k => (φ k).2 n) l (𝓝 (ψ.2 n))) :
    ∃ H : ℝ, 0 < H ∧ ∀ z : ℂ, H ≤ |z.im| →
      z ∈ resolventSet hp ψ ∧ (∀ k, z ∈ resolventSet hp (φ k)) ∧
      Tendsto (fun k => resolvent hp (φ k) z) l (𝓝 (resolvent hp ψ z)) := by
  obtain ⟨M, hM⟩ := hb.exists_norm_le
  let B := max M ‖ψ‖ + 1
  have hB : 0 < B := by dsimp [B]; linarith [le_max_right M ‖ψ‖, norm_nonneg ψ]
  have hφB (k : α) : ‖φ k‖ ≤ B := by
    have hk := hM _ ⟨k, rfl⟩
    dsimp [B]
    linarith [le_max_left M ‖ψ‖]
  have hψB : ‖ψ‖ ≤ B := by dsimp [B]; linarith [le_max_right M ‖ψ‖]
  have ht : Tendsto (fun H : ℝ => (4*p.toReal/H^(1/p.toReal)+1/H)*B) atTop (𝓝 0) := by
    simpa only [zero_mul] using (tendsto_freeL1_heightBound_zero hp).mul_const B
  obtain ⟨H, hH, hsmall⟩ := ((eventually_gt_atTop (0 : ℝ)).and
    (ht.eventually_lt_const (by norm_num : (0:ℝ) < 1/2))).exists
  refine ⟨H, hH, ?_⟩
  intro z hz
  have him : z.im ≠ 0 := abs_pos.mp (hH.trans_le hz)
  have hzfree : z ∉ freeLattice := notMem_freeLattice_of_im_ne_zero him
  have hpR : 0 < p.toReal := ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans_le Fact.out)) hp
  have hbound (θ : PairSpace p) (hθ : ‖θ‖ ≤ B) : freeL1Bound p hp z hzfree * ‖θ‖ < 1/2 := by
    calc
      _ ≤ (4*p.toReal/|z.im|^(1/p.toReal)+1/|z.im|)*B := by
        simpa only [one_div] using mul_le_mul (freeL1Bound_le_height hp z hzfree him) hθ
          (norm_nonneg θ) (by positivity)
      _ ≤ (4*p.toReal/H^(1/p.toReal)+1/H)*B := by gcongr
      _ < 1/2 := hsmall
  have hφ : ∀ k, NeumannCondition hp (φ k) z hzfree := fun k =>
    (hbound (φ k) (hφB k)).trans (by norm_num)
  have hψ : NeumannCondition hp ψ z hzfree := (hbound ψ hψB).trans (by norm_num)
  exact ⟨mem_resolventSet_of_neumannCondition hp ψ z hzfree hψ,
    fun k => mem_resolventSet_of_neumannCondition hp (φ k) z hzfree (hφ k),
    tendsto_resolvent_of_bounded_coefficientwise_neumann hp hp1 φ ψ hb ht₁ ht₂ z hzfree hφ hψ
      (1/2) (by norm_num) (fun k => (hbound (φ k) (hφB k)).le)⟩

/-- The common-height full-resolvent limit in period-one source coordinates. -/
theorem exists_height_source_resolvent_tendsto_of_bounded_coefficientwise
    (hp : p ≠ ⊤) (hp1 : 1 < p) {α : Type*} {l : Filter α}
    (φ : α → CoeffPair p) (ψ : CoeffPair p)
    (hb : Bornology.IsBounded (range φ))
    (ht₁ : ∀ n : ℤ, Tendsto (fun k => (φ k).fst n) l (𝓝 (ψ.fst n)))
    (ht₂ : ∀ n : ℤ, Tendsto (fun k => (φ k).snd n) l (𝓝 (ψ.snd n))) :
    ∃ H : ℝ, 0 < H ∧ ∀ z : ℂ, H ≤ |z.im| →
      z ∈ resolventSet hp (periodOnePotential ψ) ∧
      (∀ k, z ∈ resolventSet hp (periodOnePotential (φ k))) ∧
      Tendsto (fun k => resolvent hp (periodOnePotential (φ k)) z) l
        (𝓝 (resolvent hp (periodOnePotential ψ) z)) := by
  have hb' : Bornology.IsBounded (range (fun k => periodOnePotential (φ k))) := by
    obtain ⟨M, hM⟩ := hb.exists_norm_le
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨M, ?_⟩
    rintro _ ⟨k, rfl⟩
    exact (norm_periodOnePotential_le (φ k)).trans (hM _ ⟨k, rfl⟩)
  exact exists_height_resolvent_tendsto_of_bounded_coefficientwise hp hp1
    (fun k => periodOnePotential (φ k)) (periodOnePotential ψ) hb'
    (tendsto_periodDouble_coefficientwise (fun k => (φ k).fst) ψ.fst ht₁)
    (tendsto_periodDouble_coefficientwise (fun k => (φ k).snd) ψ.snd ht₂)

end NLS.ZakharovShabat
