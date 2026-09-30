import NLS.ZakharovShabat.SourceAngularAdmissiblePathTerminalSheet
import NLS.ZakharovShabat.SourceAngularEtaAdmissiblePathModel
import NLS.ZakharovShabat.SourceAngularEtaModelCoordinate

/-!
# Transporting the eta remainder along continued admissible roots

On the path interior the actual remainder is a fixed sign times its
canonical differential and primitive. Near a regular terminal it agrees
with the glued primitive on the normalized terminal sheet. Its path
integral is therefore that terminal value, even when the path traverses
several root charts or ends in the interior of the canonical cut.
-/

noncomputable section
open Set Filter Topology Metric Complex NLS.ComplexAnalysis
open scoped ENNReal unitInterval
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem sourceAngularEtaSelectedPathRoot_canonical
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (ψ : CoeffPair p) (z : ℂ)
    (hz : z ∈ sourceStandardRootOmittedDomain hp hp1 ψ n) :
    sourceAngularEtaSelectedPathRoot hp hp1 n ψ
      (fun t => sourceCanonicalRoot hp hp1 t.2 t.1) z = sourceStandardRoot hp hp1 ψ n z := by
  change sourceCanonicalRoot hp hp1 ψ z/(2*Complex.I*sourceStandardRootOmittedProduct hp hp1 n ψ z) =
    sourceStandardRoot hp hp1 ψ n z
  rw [sourceCanonicalRoot_eq_omitted hp hp1 n ψ z]
  have hK : 2*Complex.I*sourceStandardRootOmittedProduct hp hp1 n ψ z ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) I_ne_zero)
      (sourceStandardRootOmittedProduct_ne_zero hp hp1 ψ z n hz)
  rw [mul_right_comm (2*Complex.I) (sourceStandardRoot hp hp1 ψ n z)
    (sourceStandardRootOmittedProduct hp hp1 n ψ z)]
  exact mul_div_cancel_left₀ (sourceStandardRoot hp hp1 ψ n z) hK

theorem sourceAngularEtaPathModelIntegrand_canonical
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (ψ : CoeffPair p) (z : ℂ)
    (hz : z ∈ sourceStandardRootOmittedDomain hp hp1 ψ n) :
    sourceAngularEtaPathModelIntegrand hp hp1 n ψ
      (fun t => sourceCanonicalRoot hp hp1 t.2 t.1) z = sourceAngularEtaModelIntegrand hp hp1 n ψ z := by
  apply mul_left_cancel₀ I_ne_zero
  rw [I_mul_sourceAngularEtaPathModelIntegrand,I_mul_sourceAngularEtaModelIntegrand,
    sourceAngularEtaSelectedPathRoot_canonical hp hp1 n ψ z hz]

theorem sourceAngularEtaPathModelIntegrand_of_signed_root
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (ψ : CoeffPair p)
    (Q : ℂ × CoeffPair p → ℂ) (z κ : ℂ) (hκ : κ = 1 ∨ κ = -1)
    (hz : z ∈ sourceStandardRootOmittedDomain hp hp1 ψ n)
    (hroot : Q (z,ψ) = κ*sourceCanonicalRoot hp hp1 ψ z) :
    sourceAngularEtaPathModelIntegrand hp hp1 n ψ Q z =
      κ*sourceAngularEtaModelIntegrand hp hp1 n ψ z := by
  have h := sourceAngularEtaPathModelIntegrand_canonical hp hp1 n ψ z hz
  dsimp only [sourceAngularEtaPathModelIntegrand] at h ⊢
  rw [hroot]
  rcases hκ with rfl | rfl
  · simpa only [one_mul] using h
  · simpa only [neg_one_mul,div_neg] using congrArg Neg.neg h

namespace SourceAngularAdmissiblePathRootData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {n : ℤ} {ψ : CoeffPair p}
  {c : ℂ} {R : ℝ} {Q : ℂ × CoeffPair p → ℂ} {a b : ℂ} {γ : Path a b}

/-- The fixed-sign canonical primitive has precisely the value of
the normalized terminal chart as its final path limit. -/
theorem signed_primitive_terminal_limit
    (hQ : SourceAngularAdmissiblePathRootData hp hp1 n ψ c R Q γ)
    {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k} {w : ℂ} {F E : ℂ → ℂ}
    (hE : SourceAngularEtaRemainderSheetPrimitiveData hp hp1 n s ψ c R w F E)
    (hother : closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 ψ n)
    (hw : w ≠ 0) (hb : b ∈ sourceAngularRegularSheetDisc hp ψ c R w)
    (heq : Q (b,ψ) = sourceAngularRootSheet hp w (b,ψ))
    (κ : ℂ) (hκ : κ = 1 ∨ κ = -1)
    (hfixed : ∀ t ∈ Ioo (0:ℝ) 1, Q (γ.extend t,ψ) = κ*sourceCanonicalRoot hp hp1 ψ (γ.extend t)) :
    Tendsto ((fun z => κ*F z) ∘ γ.extend) (𝓝[<] (1:ℝ)) (𝓝 (E b)) := by
  have hγend : Tendsto γ.extend (𝓝 (1:ℝ)) (𝓝 b) := by
    simpa only [Path.extend_one] using
      (γ.continuous_extend.continuousAt (x := (1:ℝ))).tendsto
  have hdom : ∀ᶠ t in 𝓝 (1:ℝ), γ.extend t ∈ sourceAngularRegularSheetDisc hp ψ c R w :=
    hγend.eventually ((isOpen_sourceAngularRegularSheetDisc hp hp1 ψ c R w).mem_nhds hb)
  have hroots := hQ.eventuallyEq_terminal_sheet w hw hb.2 heq
  have hlimit := ((hE.analytic_sheet b hb).continuousAt.tendsto.comp hγend).mono_left
    (show 𝓝[<] (1:ℝ) ≤ 𝓝 1 from nhdsWithin_le_nhds)
  apply hlimit.congr'
  filter_upwards [hdom.filter_mono nhdsWithin_le_nhds,
    hroots.filter_mono nhdsWithin_le_nhds,
    Ioo_mem_nhdsLT (by norm_num : (0:ℝ) < 1)] with t htD htQ ht
  have hmatch := hE.eqOn_exterior ⟨htD,(hQ.interior t ht).2⟩
  simp only [sourceAngularExteriorPrimitive,rootRatioPrimitive,sub_zero] at hmatch
  rw [← htQ,hfixed t ht] at hmatch
  have hcan := sourceCanonicalRoot_ne_zero_off_gaps hp hp1 ψ _
    (hQ.interior_mem_canonicalRootDomain hother t ht)
  rcases hκ with rfl | rfl
  · simpa only [Function.comp_def,one_mul,div_self hcan] using hmatch
  · simpa only [Function.comp_def,neg_one_mul,div_neg,div_self hcan] using hmatch

end SourceAngularAdmissiblePathRootData

namespace SourceAngularAdmissiblePathRootData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {n : ℤ} {ψ : CoeffPair p}
  {c : ℂ} {R : ℝ} {Q : ℂ × CoeffPair p → ℂ} {b : ℂ}
  {γ : Path (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n) b}

/-- A final path limit of the fixed-sign canonical remainder evaluates
its contribution to the literal eta integral. This form also permits
singular periodic terminals where the limit is zero. -/
theorem pathIntegral_decomposition_of_remainder_limit
    (hQ : SourceAngularAdmissiblePathRootData hp hp1 n ψ c R Q γ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k)
    (hother : closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 ψ n)
    (F : ℂ → ℂ)
    (hFcan : ∀ z ∈ ball c R \ sourcePeriodicSegment hp hp1 ψ n,
      HasDerivAt F (sourceAngularEtaRemainderIntegrand hp hp1 n s ψ z) z)
    (hleft : Tendsto F (𝓝[ball c R \ sourcePeriodicSegment hp hp1 ψ n]
      (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)) (𝓝 0))
    (κ : ℂ) (hκ : κ = 1 ∨ κ = -1)
    (hfixed : ∀ t ∈ Ioo (0:ℝ) 1, Q (γ.extend t,ψ) = κ*sourceCanonicalRoot hp hp1 ψ (γ.extend t))
    (B : ℂ) (hend : Tendsto ((fun z => κ*F z) ∘ γ.extend) (𝓝[<] (1:ℝ)) (𝓝 B))
    (hγ : ContDiffOn ℝ 1 γ.extend (Icc 0 1))
    (hint : CurveIntegrable (holomorphicOneForm (fun z => sourceAngularIntegrand n s Q (z,ψ))) γ)
    (hmodel : CurveIntegrable (holomorphicOneForm (sourceAngularEtaPathModelIntegrand hp hp1 n ψ Q)) γ) :
    sourceAngularPathIntegral n s Q ψ γ =
      (∫ᶜ z in γ, holomorphicOneForm (sourceAngularEtaPathModelIntegrand hp hp1 n ψ Q) z)+B := by
  let f : ℂ → ℂ := fun z => sourceAngularIntegrand n s Q (z,ψ)
  let M := sourceAngularEtaPathModelIntegrand hp hp1 n ψ Q
  let ρ : ℂ → ℂ := fun z => f z-M z
  let q : ℂ → ℂ := fun z => κ*sourceAngularEtaRemainderIntegrand hp hp1 n s ψ z
  have hpoint (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) : ρ (γ.extend t) = q (γ.extend t) := by
    have hf : f (γ.extend t) = κ*sourceAngularIntegrand n s
        (fun u => sourceCanonicalRoot hp hp1 u.2 u.1) (γ.extend t,ψ) := by
      dsimp only [f,sourceAngularIntegrand]
      rw [hfixed t ht]
      rcases hκ with rfl | rfl <;> simp only [one_mul,neg_one_mul,div_neg]
    have hM := sourceAngularEtaPathModelIntegrand_of_signed_root hp hp1 n ψ Q (γ.extend t) κ hκ
      (hother (ball_subset_closedBall (hQ.interior t ht).1)) (hfixed t ht)
    change M (γ.extend t) = κ*sourceAngularEtaModelIntegrand hp hp1 n ψ (γ.extend t) at hM
    change f (γ.extend t)-M (γ.extend t) = κ*(_-_)
    rw [hf,hM]
    ring
  have hω : holomorphicOneForm ρ = holomorphicOneForm f-holomorphicOneForm M := by
    funext z
    exact sub_smul (f z) (M z) (ContinuousLinearMap.id ℂ ℂ)
  have hIntρ : CurveIntegrable (holomorphicOneForm ρ) γ := by rw [hω]; exact hint.sub hmodel
  have hIntq : CurveIntegrable (holomorphicOneForm q) γ :=
    (curveIntegrable_holomorphicOneForm_congr_interior ρ q γ hpoint).mp hIntρ
  have hstart : Tendsto ((fun z => κ*F z) ∘ γ.extend) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have hγstart : Tendsto γ.extend (𝓝[>] (0:ℝ))
        (𝓝[ball c R \ sourcePeriodicSegment hp hp1 ψ n]
          (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)) := by
      apply tendsto_nhdsWithin_iff.mpr
      constructor
      · simpa only [Path.extend_zero] using
          (γ.continuous_extend.continuousAt (x := (0:ℝ))).tendsto.mono_left nhdsWithin_le_nhds
      · filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ) < 1)] with t ht
        exact hQ.interior t ht
    simpa only [Function.comp_def,mul_zero] using
      (hleft.comp hγstart).const_mul κ
  have hFκ : ∀ z ∈ ball c R \ sourcePeriodicSegment hp hp1 ψ n,
      HasDerivAt (fun z => κ*F z) (q z) z := fun z hz => (hFcan z hz).const_mul κ
  have hval := curveIntegral_eq_sub_of_primitive_with_limits q (fun z => κ*F z) _ hFκ
    γ hγ hQ.interior hIntq hstart hend
  rw [← curveIntegral_holomorphicOneForm_congr_interior ρ q γ hpoint,
    hω,curveIntegral_sub hint hmodel,sub_zero] at hval
  change (∫ᶜ z in γ, holomorphicOneForm f z) = (∫ᶜ z in γ, holomorphicOneForm M z)+B
  exact sub_eq_iff_eq_add.mp hval |>.trans (add_comm _ _)

end SourceAngularAdmissiblePathRootData

namespace SourceAngularEtaRemainderSheetPrimitiveData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {n : ℤ}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k} {ψ : CoeffPair p}
  {c : ℂ} {R : ℝ} {w : ℂ} {F E : ℂ → ℂ}

/-- The literal eta integral along a continued admissible root splits
into its model integral and the single normalized terminal remainder.
The path need not stay on the terminal chart. -/
theorem admissible_pathIntegral_decomposition
    (hE : SourceAngularEtaRemainderSheetPrimitiveData hp hp1 n s ψ c R w F E)
    (hother : closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 ψ n)
    (hw : w ≠ 0) {b : ℂ}
    (hb : b ∈ sourceAngularRegularSheetDisc hp ψ c R w)
    (Q : ℂ × CoeffPair p → ℂ)
    (γ : Path (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n) b)
    (hQ : SourceAngularAdmissiblePathRootData hp hp1 n ψ c R Q γ)
    (heq : Q (b,ψ) = sourceAngularRootSheet hp w (b,ψ))
    (hγ : ContDiffOn ℝ 1 γ.extend (Icc 0 1))
    (hint : CurveIntegrable (holomorphicOneForm (fun z => sourceAngularIntegrand n s Q (z,ψ))) γ)
    (hmodel : CurveIntegrable (holomorphicOneForm (sourceAngularEtaPathModelIntegrand hp hp1 n ψ Q)) γ) :
    sourceAngularPathIntegral n s Q ψ γ =
      (∫ᶜ z in γ, holomorphicOneForm (sourceAngularEtaPathModelIntegrand hp hp1 n ψ Q) z)+E b := by
  obtain ⟨κ,hκ,hfixed⟩ := hQ.exists_fixed_sign hother
  have hend := hQ.signed_primitive_terminal_limit hE hother hw hb heq κ hκ hfixed
  exact hQ.pathIntegral_decomposition_of_remainder_limit s hother F hE.hasDerivAt_exterior
    hE.tendsto_left_exterior κ hκ hfixed (E b) hend hγ hint hmodel

end SourceAngularEtaRemainderSheetPrimitiveData
end NLS.ZakharovShabat
