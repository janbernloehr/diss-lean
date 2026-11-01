import NLS.ZakharovShabat.AppendixFSourceSpokes
import NLS.ZakharovShabat.AppendixFRootPath
import NLS.ZakharovShabat.SourceActionChi
import NLS.ZakharovShabat.SourceLemma10_10

/-!
# Actual-source limits in the collapsing-gap argument

Squared-gap analyticity gives convergence of the gap itself to zero at
collapsed sources, without continuous endpoint labels. The exact critical
offset then gives the half-gap bound in (F.2). The actual standard root and
literal chi_n integrand converge along the moving midpoint paths.
-/

noncomputable section
open Set Metric Filter Topology Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {S : Set (CoeffPair p)}

/-- Convergence to a collapsed source gives gap convergence even if endpoint labels switch. -/
theorem SourceLemma10_2Data.appendixF_gap_tendsto_zero
    (H : SourceLemma10_2Data hp hp1 S) (φ : CoeffPair p) (hφ : φ ∈ S) (n : ℤ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n = 0)
    {ι : Type*} {l : Filter ι} (ψ : ι → CoeffPair p) (hψ : Tendsto ψ l (𝓝 φ)) :
    Tendsto (fun k => canonicalPeriodicGap hp hp1 (periodOnePotential (ψ k))
      (periodOnePotential_mem (ψ k)) n) l (𝓝 0) := by
  have hc : ContinuousAt (fun χ : CoeffPair p =>
      ‖canonicalPeriodicGap hp hp1 (periodOnePotential χ) (periodOnePotential_mem χ) n‖) φ := by
    simpa only [norm_pow,Real.sqrt_sq (norm_nonneg _)] using
      (H.squared_gap n φ hφ).continuousAt.norm.sqrt
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [Function.comp_def,hgap,norm_zero] using hc.tendsto.comp hψ

/-- Lemma 10.10 supplies the half-gap critical offset on a neighborhood of every collapsed source. -/
theorem SourceLemma10_10Data.appendixF_eventually_half_gap
    (H : SourceLemma10_10Data hp hp1 S) (hS : IsOpen S)
    (φ : CoeffPair p) (hφ : φ ∈ S) (n : ℤ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n = 0) :
    ∀ᶠ ψ in 𝓝 φ,
      ‖canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n-
        canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n‖ ≤
          ‖canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n‖/2 := by
  let A := H.previous.previous.previous.roots.roots.symmetric
  have hg := A.appendixF_gap_tendsto_zero φ hφ n hgap id tendsto_id
  have hsmall : ∀ᶠ ψ in 𝓝 φ,
      ‖canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n‖ *
        ‖sourceCriticalGapQuotient hp hp1 ψ n‖ < (1/2:ℝ) := by
    have hlim := hg.norm.mul (H.analytic n φ hφ).continuousAt.norm.tendsto
    exact hlim.eventually (gt_mem_nhds (by simp))
  filter_upwards [hsmall,hS.mem_nhds hφ] with ψ hsmall hψ
  rw [H.exact_offset ψ hψ n,add_sub_cancel_left,sourcePeriodicGapDisplacement_apply,
    norm_mul,norm_pow]
  have h := mul_le_mul_of_nonneg_left hsmall.le
    (norm_nonneg (canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n))
  nlinarith

/-- The actual standard root on each positive midpoint parameter tends to the linear root. -/
theorem SourceLemma10_2Data.appendixF_source_root_spoke_tendsto
    (H : SourceLemma10_2Data hp hp1 S) (φ : CoeffPair p) (hφ : φ ∈ S) (n : ℤ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n = 0)
    {ι : Type*} {l : Filter ι} (ψ : ι → CoeffPair p) (hψ : Tendsto ψ l (𝓝 φ))
    (ν : ℂ) (hν : ν ≠ canonicalPeriodicMidpoint hp hp1
      (periodOnePotential φ) (periodOnePotential_mem φ) n) (t : ℝ) (ht : 0 < t) :
    let τ := fun χ : CoeffPair p => canonicalPeriodicMidpoint hp hp1
      (periodOnePotential χ) (periodOnePotential_mem χ) n
    Tendsto (fun k => sourceStandardRoot hp hp1 (ψ k) n (τ (ψ k)+(t:ℂ)*(ν-τ (ψ k))))
      l (𝓝 (-(t:ℂ)*(ν-τ φ))) := by
  dsimp only
  exact appendixF_normalized_root_spoke_tendsto
    (fun k => canonicalPeriodicMidpoint hp hp1 (periodOnePotential (ψ k)) (periodOnePotential_mem (ψ k)) n)
    (fun k => canonicalPeriodicGap hp hp1 (periodOnePotential (ψ k)) (periodOnePotential_mem (ψ k)) n)
    (fun k => ν-canonicalPeriodicMidpoint hp hp1 (periodOnePotential (ψ k)) (periodOnePotential_mem (ψ k)) n)
    _ (sub_ne_zero.mpr hν) (H.appendixF_gap_tendsto_zero φ hφ n hgap ψ hψ)
    (tendsto_const_nhds.sub ((H.midpoint n φ hφ).continuousAt.tendsto.comp hψ)) t ht

/-- The two rescaled terms printed before the majorant argument both tend to t. -/
theorem SourceLemma10_10Data.appendixF_source_rescaled_terms_tendsto
    (H : SourceLemma10_10Data hp hp1 S) (φ : CoeffPair p) (hφ : φ ∈ S) (n : ℤ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n = 0)
    {ι : Type*} {l : Filter ι} (ψ : ι → CoeffPair p) (hψ : Tendsto ψ l (𝓝 φ))
    (ν : ℂ) (hν : ν ≠ canonicalPeriodicMidpoint hp hp1
      (periodOnePotential φ) (periodOnePotential_mem φ) n) (t : ℝ) (ht : 0 < t) :
    let τ := fun χ : CoeffPair p => canonicalPeriodicMidpoint hp hp1
      (periodOnePotential χ) (periodOnePotential_mem χ) n
    Tendsto (fun k => Complex.sqrt ((t:ℂ)^2-
      (canonicalPeriodicGap hp hp1 (periodOnePotential (ψ k)) (periodOnePotential_mem (ψ k)) n /
        (2*(ν-τ (ψ k))))^2)) l (𝓝 (t:ℂ)) ∧
      Tendsto (fun k => (t:ℂ)+(τ (ψ k)-canonicalCriticalPoints hp hp1
        (periodOnePotential (ψ k)) (periodOnePotential_mem (ψ k)) n)/(ν-τ (ψ k))) l (𝓝 (t:ℂ)) := by
  dsimp only
  let A := H.previous.previous.previous.roots.roots.symmetric
  have hτ := (A.midpoint n φ hφ).continuousAt.tendsto.comp hψ
  have hz := tendsto_const_nhds.sub hτ (a := ν)
  have hden : (2:ℂ)*(ν-canonicalPeriodicMidpoint hp hp1
      (periodOnePotential φ) (periodOnePotential_mem φ) n) ≠ 0 :=
    mul_ne_zero (by norm_num) (sub_ne_zero.mpr hν)
  have he := (A.appendixF_gap_tendsto_zero φ hφ n hgap ψ hψ).div
    (tendsto_const_nhds.mul hz) hden
  have hrad := tendsto_const_nhds.sub (he.pow 2) (a := (t:ℂ)^2)
  have hsq : Complex.sqrt ((t:ℂ)^2) = (t:ℂ) := by
    rw [← Complex.ofReal_pow,Complex.sqrt_of_nonneg (by exact_mod_cast sq_nonneg t)]
    simp only [Complex.ofReal_re,Real.sqrt_sq ht.le]
  have hcont : ContinuousAt Complex.sqrt ((t:ℂ)^2) :=
    Complex.continuousAt_sqrt (Or.inl (by
      rw [← Complex.ofReal_pow,Complex.ofReal_re]
      positivity))
  simp only [zero_div,zero_pow (by norm_num : (2:ℕ) ≠ 0),sub_zero] at hrad
  constructor
  · simpa only [hsq,Function.comp_def,Pi.div_apply] using hcont.tendsto.comp hrad
  · have hcrit := (A.simplicity.critical φ hφ n).1.continuousAt.tendsto.comp hψ
    have hnum := hτ.sub hcrit
    have hlim := tendsto_const_nhds.add (hnum.div hz (sub_ne_zero.mpr hν)) (a := (t:ℂ))
    simpa only [H.critical_eq_midpoint_of_gap_zero φ hφ n
      (by simpa only [sourcePeriodicGapDisplacement_apply] using hgap),sub_self,zero_div,add_zero,
      Function.comp_def,Pi.div_apply] using hlim

/-- The actual source differential integrand, with the full -i displacement coefficient, has the collapsed limit. -/
theorem SourceLemma10_10Data.appendixF_source_integrand_tendsto
    (H : SourceLemma10_10Data hp hp1 S) (hS : IsOpen S)
    {V : Set (CoeffPair p)} (hVS : V ⊆ S) {D : ℤ → Set ℂ} {c : ℝ}
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (φ : CoeffPair p) (hφ : φ ∈ V) (n : ℤ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n = 0)
    {ι : Type*} {l : Filter ι} (ψ : ι → CoeffPair p) (hψ : Tendsto ψ l (𝓝 φ))
    (ν : ℂ) (hνD : ν ∈ closure (D n))
    (hν : ν ≠ canonicalPeriodicMidpoint hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n)
    (t : ℝ) (ht : t ∈ Ioc (0:ℝ) 1) :
    let τ := fun χ : CoeffPair p => canonicalPeriodicMidpoint hp hp1
      (periodOnePotential χ) (periodOnePotential_mem χ) n
    let Z := fun χ : CoeffPair p => τ χ+(t:ℂ)*(ν-τ χ)
    Tendsto (fun k => -I*(ν-τ (ψ k))*
      ((canonicalCriticalPoints hp hp1 (periodOnePotential (ψ k)) (periodOnePotential_mem (ψ k)) n-Z (ψ k)) /
        sourceStandardRoot hp hp1 (ψ k) n (Z (ψ k)))*sourceActionChi hp hp1 n (ψ k) (Z (ψ k)))
      l (𝓝 (-I*(ν-τ φ)*sourceActionChi hp hp1 n φ (Z φ))) := by
  dsimp only
  let Q := H.previous.previous.previous
  let A := Q.roots.roots.symmetric
  let τ := fun χ : CoeffPair p => canonicalPeriodicMidpoint hp hp1
    (periodOnePotential χ) (periodOnePotential_mem χ) n
  have hτ := (A.midpoint n φ (hVS hφ)).continuousAt.tendsto.comp hψ
  have ha : Tendsto (fun k => canonicalCriticalPoints hp hp1 (periodOnePotential (ψ k))
      (periodOnePotential_mem (ψ k)) n-τ (ψ k)) l (𝓝 0) := by
    have hcrit := (A.simplicity.critical φ (hVS hφ) n).1.continuousAt.tendsto.comp hψ
    simpa only [τ,Function.comp_def,H.critical_eq_midpoint_of_gap_zero φ (hVS hφ) n
      (by simpa only [sourcePeriodicGapDisplacement_apply] using hgap),sub_self] using hcrit.sub hτ
  have hpoint : τ φ+(t:ℂ)*(ν-τ φ) ∈ closure (D n) := by
    obtain ⟨a,R,hR,he⟩ := hD.discs n
    have hτD := hD.gap φ hφ n (sourcePeriodicMidpoint_mem_segment hp hp1 φ n)
    rw [he] at hτD
    rw [he,closure_ball _ hR.ne'] at hνD ⊢
    have h := (convex_closedBall (a:ℂ) R).lineMap_mem (ball_subset_closedBall hτD) hνD
      (Ioc_subset_Icc_self ht)
    simpa only [AffineMap.lineMap_apply_module',Complex.real_smul,add_comm] using h
  have hχ := (Q.chi_joint hS n (τ φ+(t:ℂ)*(ν-τ φ),φ)
    ⟨hVS hφ,hD.closedDisk_subset_omittedDomain φ hφ n hpoint⟩).continuousAt
  have hlim := appendixF_spoke_integrand_tendsto
    (fun k => τ (ψ k))
    (fun k => canonicalPeriodicGap hp hp1 (periodOnePotential (ψ k)) (periodOnePotential_mem (ψ k)) n)
    (fun k => canonicalCriticalPoints hp hp1 (periodOnePotential (ψ k)) (periodOnePotential_mem (ψ k)) n)
    (fun k => ν-τ (ψ k)) ψ (τ φ) (ν-τ φ) φ (sub_ne_zero.mpr hν) hτ
    (A.appendixF_gap_tendsto_zero φ (hVS hφ) n hgap ψ hψ)
    (tendsto_const_nhds.sub hτ) hψ ha t ht.1
    (fun q : ℂ × CoeffPair p => sourceActionChi hp hp1 n q.2 q.1) hχ
  simpa only [sourceStandardRoot,τ,mul_assoc] using hlim.const_mul (-I)

end NLS.ZakharovShabat
