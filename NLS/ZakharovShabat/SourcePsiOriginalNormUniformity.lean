import NLS.ZakharovShabat.SourcePsiOriginalNormLimit

/-!
# Uniformity of the original Jacobian norm limit

The common joint Lipschitz bounds upgrade pointwise norm convergence to
mathlib's locally uniform convergence: the neighborhood may depend on
the error tolerance. In particular convergence is uniform on every
compact subset of the original real domain. No fixed open neighborhood
of uniform convergence is asserted.
-/

noncomputable section
open Set Complex Metric Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The full original real root/source domain in root-first coordinates. -/
def sourcePsiOriginalRealLimitDomain (W V : Set (CoeffPair p)) (D : ℤ → Set ℂ) :
    Set (Coeff p × CoeffPair p) :=
  {t | t ∈ sourcePsiOriginalLimitDomain W V D ∧ ∀ k : ℤ, (t.1 k).im = 0}

/-- Local uniformity with a tolerance-dependent neighborhood, in the joint
root/source topology throughout the original real domain. -/
theorem SourceLemma12_4Data.originalFullRootJacobian_tendstoLocallyUniformlyOn
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (H : SourceLemma12_4Data hp hp1 W) (hW : IsOpen W)
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c) (hV : IsOpen V) :
    TendstoLocallyUniformlyOn
      (fun (n : ℤ) (t : Coeff p × CoeffPair p) => sourcePsiOriginalFullRootJacobian hp hp1 n t.1 t.2)
      (fun t : Coeff p × CoeffPair p => sourcePsiOriginalLimitOperator hp hp1 t.1 t.2)
      (Filter.comap Int.natAbs atTop) (sourcePsiOriginalRealLimitDomain W V D) := by
  rw [Metric.tendstoLocallyUniformlyOn_iff]
  intro ε hε x hx
  obtain ⟨r,L,hr,hL,hb⟩ := H.originalFullRootJacobian_local_Lipschitz x.1 x.2 hx.1.2.2.1
  obtain ⟨r',L',hr',hL',hb'⟩ := H.originalLimitOperator_local_Lipschitz hD x.1 x.2 hx.1.2.2.1
  let δ := min r (min r' (ε/(3*(L+L'+1))))
  have hδ : 0 < δ := lt_min hr (lt_min hr' (by positivity))
  have hlim := H.originalFullRootJacobian_tendsto hW hD hV x.2 hx.1.1 hx.1.2.1
    hx.1.2.2.1 x.1 hx.1.2.2.2 hx.2
  refine ⟨ball x δ ∩ sourcePsiOriginalRealLimitDomain W V D,
    inter_mem (mem_nhdsWithin_of_mem_nhds (ball_mem_nhds x hδ)) self_mem_nhdsWithin,?_⟩
  filter_upwards [Metric.tendsto_nhds.mp hlim (ε/3) (by positivity)] with n hn
  intro y hy
  have hyd0 : dist y x < δ := hy.1
  have hyr : y ∈ ball x r := hyd0.trans_le (min_le_left _ _)
  have hyr' : y ∈ ball x r' := hyd0.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hyd : ‖y-x‖ < ε/(3*(L+L'+1)) := by
    simpa only [mem_ball,dist_eq_norm] using
      hyd0.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hbn := hb n y hyr hy.2.1.1 hy.2.1.2.2.1 x (mem_ball_self hr) hx.1.1 hx.1.2.2.1
  have hbs := hb' x (mem_ball_self hr') hx.1 y hyr' hy.2.1
  rw [norm_sub_rev x y] at hbs
  have hsmall : (L+L')*‖y-x‖ < ε/3 := by
    have hmul := (lt_div_iff₀ (show 0 < 3*(L+L'+1) by positivity)).mp hyd
    nlinarith [norm_nonneg (y-x)]
  rw [dist_eq_norm] at hn
  rw [dist_eq_norm,norm_sub_rev]
  have htri : ‖sourcePsiOriginalFullRootJacobian hp hp1 n y.1 y.2 -
      sourcePsiOriginalLimitOperator hp hp1 y.1 y.2‖ ≤
      ‖sourcePsiOriginalFullRootJacobian hp hp1 n y.1 y.2 - sourcePsiOriginalFullRootJacobian hp hp1 n x.1 x.2‖ +
      ‖sourcePsiOriginalFullRootJacobian hp hp1 n x.1 x.2 - sourcePsiOriginalLimitOperator hp hp1 x.1 x.2‖ +
      ‖sourcePsiOriginalLimitOperator hp hp1 x.1 x.2 - sourcePsiOriginalLimitOperator hp hp1 y.1 y.2‖ := by
    calc
      _ = ‖(sourcePsiOriginalFullRootJacobian hp hp1 n y.1 y.2 - sourcePsiOriginalFullRootJacobian hp hp1 n x.1 x.2) +
          (sourcePsiOriginalFullRootJacobian hp hp1 n x.1 x.2 - sourcePsiOriginalLimitOperator hp hp1 x.1 x.2) +
          (sourcePsiOriginalLimitOperator hp hp1 x.1 x.2 - sourcePsiOriginalLimitOperator hp hp1 y.1 y.2)‖ := by
        congr 1; abel
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (le_refl _))
  nlinarith only [htri,hbn,hbs,hn,hsmall,hε]

/-- The same convergence in the source's original real Omega coordinates. -/
theorem SourceLemma12_4Data.originalOmega_tendstoLocallyUniformlyOn
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (H : SourceLemma12_4Data hp hp1 W)
    (hW : IsOpen W) (hR : realTypeSourceLocus p ⊆ W)
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c) (hV : IsOpen V) :
    TendstoLocallyUniformlyOn
      (fun (n : ℤ) (t : realTypeSourceSubmodule p × RealCoeff p) =>
        sourcePsiOriginalFullRootJacobian hp hp1 n (RealCoeff.complexCLM p t.2) t.1)
      (fun t : realTypeSourceSubmodule p × RealCoeff p =>
        sourcePsiOriginalLimitOperator hp hp1 (RealCoeff.complexCLM p t.2) t.1)
      (Filter.comap Int.natAbs atTop) (sourcePsiOriginalOmega V D) := by
  let e : realTypeSourceSubmodule p × RealCoeff p → Coeff p × CoeffPair p :=
    fun t => (RealCoeff.complexCLM p t.2,t.1)
  have he : Continuous e := ((RealCoeff.complexCLM p).continuous.comp continuous_snd).prodMk
    (continuous_subtype_val.comp continuous_fst)
  apply (H.originalFullRootJacobian_tendstoLocallyUniformlyOn hW hD hV).comp e ?_ he.continuousOn
  intro t ht
  exact ⟨⟨hR t.1.property,ht.1,t.1.property,ht.2⟩,fun k => by simp [e]⟩

/-- Uniform operator-norm convergence on every compact subset of the full
original Omega, allowing both roots and sources to vary. -/
theorem SourceLemma12_4Data.originalOmega_tendstoUniformlyOn_compact
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (H : SourceLemma12_4Data hp hp1 W)
    (hW : IsOpen W) (hR : realTypeSourceLocus p ⊆ W)
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c) (hV : IsOpen V)
    (K : Set (realTypeSourceSubmodule p × RealCoeff p)) (hK : IsCompact K)
    (hKD : K ⊆ sourcePsiOriginalOmega V D) :
    TendstoUniformlyOn
      (fun (n : ℤ) (t : realTypeSourceSubmodule p × RealCoeff p) =>
        sourcePsiOriginalFullRootJacobian hp hp1 n (RealCoeff.complexCLM p t.2) t.1)
      (fun t : realTypeSourceSubmodule p × RealCoeff p =>
        sourcePsiOriginalLimitOperator hp hp1 (RealCoeff.complexCLM p t.2) t.1)
      (Filter.comap Int.natAbs atTop) K :=
  (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp
    ((H.originalOmega_tendstoLocallyUniformlyOn hW hR hD hV).mono hKD)

/-- Retain Proposition 12.9 and the same W while proving the norm-convergence
step of Lemma 12.10 on every original real Omega. -/
theorem sourceLemma12_10_normLimit (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ IsConnected W ∧ realTypeSourceLocus p ⊆ W ∧
      SourceProposition12_9Data hp hp1 W ∧
      ∀ {V : Set (CoeffPair p)} {D : ℤ → Set ℂ} {c : ℝ},
        SourceIsolatingNeighborhoods hp hp1 V D c → IsOpen V →
        TendstoLocallyUniformlyOn
          (fun (n : ℤ) (t : realTypeSourceSubmodule p × RealCoeff p) =>
            sourcePsiOriginalFullRootJacobian hp hp1 n (RealCoeff.complexCLM p t.2) t.1)
          (fun t : realTypeSourceSubmodule p × RealCoeff p =>
            sourcePsiOriginalLimitOperator hp hp1 (RealCoeff.complexCLM p t.2) t.1)
          (Filter.comap Int.natAbs atTop) (sourcePsiOriginalOmega V D) := by
  obtain ⟨W,ho,hc,hr,H⟩ := sourceProposition12_9 hp hp1
  exact ⟨W,ho,hc,hr,H,fun hD hV =>
    H.previous.previous.previous.previous.previous.originalOmega_tendstoLocallyUniformlyOn ho hr hD hV⟩

end NLS.ZakharovShabat
