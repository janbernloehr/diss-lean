import NLS.ZakharovShabat.SourceAngularEtaAdmissibleRemainder

/-!
# Off-diagonal integrals along continued admissible roots

The root need only be continuous along the entire path. Its terminal
chart may cover just the terminal neighborhood. Fixed-sign continuation
and primitive boundary limits evaluate the literal integral, also when
the terminal lies in the interior of a cut.
-/

noncomputable section
open Set Filter Topology Metric Complex NLS.ComplexAnalysis
open scoped ENNReal unitInterval
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceAngularAdmissiblePathRootData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {m : ℤ} {ψ : CoeffPair p}
  {c : ℂ} {R : ℝ} {Q : ℂ × CoeffPair p → ℂ} {a b : ℂ} {γ : Path a b}

/-- The fixed-sign canonical primitive has precisely the value of
the normalized terminal chart as its final path limit. -/
theorem signed_beta_primitive_terminal_limit
    (hQ : SourceAngularAdmissiblePathRootData hp hp1 m ψ c R Q γ)
    {n : ℤ} {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k} {w : ℂ} {F E : ℂ → ℂ} {A : ℂ}
    (hE : SourceAngularSheetPrimitiveData hp hp1 n m s ψ c R w F A E)
    (hother : closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 ψ m)
    (hw : w ≠ 0) (hb : b ∈ sourceAngularRegularSheetDisc hp ψ c R w)
    (heq : Q (b,ψ) = sourceAngularRootSheet hp w (b,ψ))
    (κ : ℂ) (hκ : κ = 1 ∨ κ = -1)
    (hfixed : ∀ t ∈ Ioo (0:ℝ) 1, Q (γ.extend t,ψ) = κ*sourceCanonicalRoot hp hp1 ψ (γ.extend t)) :
    Tendsto ((fun z => κ*(F z-A)) ∘ γ.extend) (𝓝[<] (1:ℝ)) (𝓝 (E b)) := by
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
  simp only [sourceAngularExteriorPrimitive,rootRatioPrimitive] at hmatch
  rw [← htQ,hfixed t ht] at hmatch
  have hcan := sourceCanonicalRoot_ne_zero_off_gaps hp hp1 ψ _
    (hQ.interior_mem_canonicalRootDomain hother t ht)
  rcases hκ with rfl | rfl
  · simpa only [Function.comp_def,one_mul,div_self hcan] using hmatch
  · simpa only [Function.comp_def,neg_one_mul,div_neg,div_self hcan] using hmatch


/-- A continued root evaluates any canonical primitive by its signed path limits. -/
theorem pathIntegral_eq_of_signed_primitive_limits
    (hQ : SourceAngularAdmissiblePathRootData hp hp1 m ψ c R Q γ)
    (n : ℤ) (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k)
    (F : ℂ → ℂ) (A : ℂ)
    (hF : ∀ z ∈ ball c R \ sourcePeriodicSegment hp hp1 ψ m,
      HasDerivAt F (sourceAngularIntegrand n s
        (fun t => sourceCanonicalRoot hp hp1 t.2 t.1) (z,ψ)) z)
    (hstartF : Tendsto F (𝓝[ball c R \ sourcePeriodicSegment hp hp1 ψ m] a) (𝓝 A))
    (κ : ℂ) (hκ : κ = 1 ∨ κ = -1)
    (hfixed : ∀ t ∈ Ioo (0:ℝ) 1, Q (γ.extend t,ψ) = κ*sourceCanonicalRoot hp hp1 ψ (γ.extend t))
    (B : ℂ) (hend : Tendsto ((fun z => κ*(F z-A)) ∘ γ.extend) (𝓝[<] (1:ℝ)) (𝓝 B))
    (hγ : ContDiffOn ℝ 1 γ.extend (Icc 0 1))
    (hint : CurveIntegrable (holomorphicOneForm (fun z => sourceAngularIntegrand n s Q (z,ψ))) γ) :
    sourceAngularPathIntegral n s Q ψ γ = B := by
  let f : ℂ → ℂ := fun z => sourceAngularIntegrand n s Q (z,ψ)
  let q : ℂ → ℂ := fun z => κ*sourceAngularIntegrand n s
    (fun t => sourceCanonicalRoot hp hp1 t.2 t.1) (z,ψ)
  have heq : ∀ t ∈ Ioo (0:ℝ) 1, f (γ.extend t) = q (γ.extend t) := by
    intro t ht
    dsimp only [f,q,sourceAngularIntegrand]
    rw [hfixed t ht]
    rcases hκ with rfl | rfl <;> simp only [one_mul,neg_one_mul,div_neg]
  have hintq := (curveIntegrable_holomorphicOneForm_congr_interior f q γ heq).mp hint
  have hstart : Tendsto ((fun z => κ*(F z-A)) ∘ γ.extend) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have hγstart : Tendsto γ.extend (𝓝[>] (0:ℝ))
        (𝓝[ball c R \ sourcePeriodicSegment hp hp1 ψ m] a) := by
      apply tendsto_nhdsWithin_iff.mpr
      constructor
      · simpa only [Path.extend_zero] using
          (γ.continuous_extend.continuousAt (x := (0:ℝ))).tendsto.mono_left nhdsWithin_le_nhds
      · filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ) < 1)] with t ht
        exact hQ.interior t ht
    simpa only [Function.comp_def,sub_self,mul_zero] using
      ((hstartF.comp hγstart).sub (tendsto_const_nhds (x := A))).const_mul κ
  have hFκ : ∀ z ∈ ball c R \ sourcePeriodicSegment hp hp1 ψ m,
      HasDerivAt (fun z => κ*(F z-A)) (q z) z :=
    fun z hz => ((hF z hz).sub_const A).const_mul κ
  have hv := curveIntegral_eq_sub_of_primitive_with_limits q (fun z => κ*(F z-A)) _ hFκ
    γ hγ hQ.interior hintq hstart hend
  rw [← curveIntegral_holomorphicOneForm_congr_interior f q γ heq,sub_zero] at hv
  exact hv

end SourceAngularAdmissiblePathRootData

namespace SourceAngularSheetPrimitiveData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {n m : ℤ}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k} {ψ : CoeffPair p}
  {c : ℂ} {R : ℝ} {w : ℂ} {F E : ℂ → ℂ} {A : ℂ}

/-- A general admissible root continuation gives the normalized terminal value.
Only the root value at the terminal is prescribed, not a chart for the whole path. -/
theorem admissible_pathIntegral_eq_value
    (hE : SourceAngularSheetPrimitiveData hp hp1 n m s ψ c R w F A E)
    (hother : closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 ψ m)
    (hw : w ≠ 0) {b : ℂ} (hb : b ∈ sourceAngularRegularSheetDisc hp ψ c R w)
    (Q : ℂ × CoeffPair p → ℂ)
    (γ : Path (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m) b)
    (hQ : SourceAngularAdmissiblePathRootData hp hp1 m ψ c R Q γ)
    (heq : Q (b,ψ) = sourceAngularRootSheet hp w (b,ψ))
    (hγ : ContDiffOn ℝ 1 γ.extend (Icc 0 1))
    (hint : CurveIntegrable (holomorphicOneForm (fun z => sourceAngularIntegrand n s Q (z,ψ))) γ) :
    sourceAngularPathIntegral n s Q ψ γ = E b := by
  obtain ⟨κ,hκ,hfixed⟩ := hQ.exists_fixed_sign hother
  exact hQ.pathIntegral_eq_of_signed_primitive_limits n s F A hE.hasDerivAt_exterior
    hE.tendsto_left_exterior κ hκ hfixed (E b)
    (hQ.signed_beta_primitive_terminal_limit hE hother hw hb heq κ hκ hfixed) hγ hint

end SourceAngularSheetPrimitiveData
end NLS.ZakharovShabat
