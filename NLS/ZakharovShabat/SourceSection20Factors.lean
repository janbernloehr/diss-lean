import NLS.ZakharovShabat.SourceSection20Moments
import NLS.ZakharovShabat.SourceSingleRootQuotientNormalization
import NLS.ZakharovShabat.SourceMomentFreeFactors

/-!
# Equations (4.9)–(4.10) and the diagonal auxiliary-factor correction

The printed negative product is retained, with the unused root filled by
its midpoint. Its quotient factor is regular away from that midpoint.
The claim of analyticity for every k needs k ≠ n: the actual zero source
already gives a pole at the diagonal midpoint.
-/
noncomputable section
open Set Metric Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The negative product ζ_k printed in (4.10), with σ_n^n=τ_n. -/
def sourceSection20Zeta (hp : p ≠ ⊤) (hp1 : 1 < p)
    (s : (n : ℤ) → CoeffPair p → DeletedCoeff p n) (n k : ℤ) (ψ : CoeffPair p) (z : ℂ) : ℂ :=
  -sourceSingleRootQuotientJointProduct hp hp1 k
    (z,(sourcePsiFillDeletedRoot n (s n ψ) (sourceStandardRootMidpoint hp hp1 ψ n),ψ))

/-- The literal quotient ζ_k^n in (4.10), including its printed diagonal case. -/
def sourceSection20PrintedAuxiliary (hp : p ≠ ⊤) (hp1 : 1 < p)
    (s : (n : ℤ) → CoeffPair p → DeletedCoeff p n) (n k : ℤ) (ψ : CoeffPair p) (z : ℂ) : ℂ :=
  -Complex.I/(sourceStandardRootMidpoint hp hp1 ψ n-z)*sourceSection20Zeta hp hp1 s n k ψ z

namespace SourceSection20Data
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W V Wa B U : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
  {D : SourceSection17OriginalData hp hp1 W₀ W V s}
  {A : SourceAbelianMomentAtlas hp hp1 Wa s} (Q : SourceSection20Data D A B U)
include Q

/-- The regular negative product is analytic across the selected gap. -/
theorem zeta_analytic (ψ : CoeffPair p) (hψ : ψ ∈ U) (n k : ℤ) :
    AnalyticOnNhd ℂ (sourceSection20Zeta hp hp1 s n k ψ) (sourceStandardRootOmittedDomain hp hp1 ψ k) := by
  have hψ₀ := D.previous.previous.previous.subset (D.complex.source_subset (Q.original_subset hψ))
  exact (D.previous.previous.previous.psi.previous.quotients.spectral ψ hψ₀
    (sourcePsiFillDeletedRoot n (s n ψ) (sourceStandardRootMidpoint hp hp1 ψ n)) k).neg

/-- The auxiliary quotient is analytic where the omitted midpoint is absent. -/
theorem auxiliary_analytic (ψ : CoeffPair p) (hψ : ψ ∈ U) (n k : ℤ) :
    AnalyticOnNhd ℂ (sourceSection20PrintedAuxiliary hp hp1 s n k ψ)
      (sourceStandardRootOmittedDomain hp hp1 ψ k ∩ {z | z ≠ sourceStandardRootMidpoint hp hp1 ψ n}) := by
  intro z hz
  exact (analyticAt_const.div (analyticAt_const.sub analyticAt_id)
    (sub_ne_zero.mpr hz.2.symm)).mul (Q.zeta_analytic ψ hψ n k z hz.1)

omit Q in
/-- The first equality in (4.9), with its literal leading minus sign. -/
theorem diagonal_factor (ψ : CoeffPair p) (n : ℤ) (z : ℂ) :
    sourcePsiCandidate n (z,(s n ψ : Coeff p))/sourceCanonicalRoot hp hp1 ψ z =
      (-Complex.I/sourceStandardRoot hp hp1 ψ n z)*sourceSection20Zeta hp hp1 s n n ψ z := by
  change sourcePsiContourIntegrandJoint hp hp1 n (z,((s n ψ : Coeff p),ψ)) = _
  rw [sourcePsiContourIntegrand_eq_regular_div_root hp hp1 n n,
    ← sourceMomentRegularNumerator_fillDeletedRoot hp hp1 n n (s n ψ) (sourceStandardRootMidpoint hp hp1 ψ n),
    sourceMomentRegularNumerator_diagonal]
  unfold sourceSection20Zeta
  ring

omit Q in
/-- Away from the diagonal, the printed auxiliary factor is the convergent
double-omitted product; its unused numerator-root pole cancels. -/
theorem auxiliary_eq_zeta (ψ : CoeffPair p) (n k : ℤ) (hkn : k ≠ n) (z : ℂ)
    (hz : z ∈ sourceStandardRootOmittedDomain hp hp1 ψ k)
    (hn : z ≠ sourceStandardRootMidpoint hp hp1 ψ n) :
    sourceSection20PrintedAuxiliary hp hp1 s n k ψ z = sourcePsiZeta hp hp1 n k (s n ψ : Coeff p) ψ z := by
  rw [← sourcePsiZeta_fillDeletedRoot hp hp1 n k (s n ψ) (sourceStandardRootMidpoint hp hp1 ψ n)]
  rw [← sourcePsiGapRegularFactor_eq_zeta hp hp1 n k hkn _ ψ z hz
    (by simpa only [displacedRoots_sourcePsiFillDeletedRoot_same] using hn)]
  unfold sourceSection20PrintedAuxiliary sourceSection20Zeta sourcePsiGapRegularFactor
  rw [displacedRoots_sourcePsiFillDeletedRoot_same]
  ring

omit Q in
/-- The literal convergent product of (4.10), retaining the midpoint-filled roots. -/
theorem zeta_product (ψ : CoeffPair p) (n k : ℤ) (z : ℂ)
    (hz : z ∈ sourceStandardRootOmittedDomain hp hp1 ψ k) :
    HasProd (fun m : {m : ℤ // m ≠ k} =>
      (displacedRoots (sourcePsiFillDeletedRoot n (s n ψ) (sourceStandardRootMidpoint hp hp1 ψ n)) m-z)/
        sourceStandardRoot hp hp1 ψ m z) (-sourceSection20Zeta hp hp1 s n k ψ z) := by
  simpa only [sourceSection20Zeta,neg_neg] using
    hasProd_sourceSingleRootQuotient_subtype hp hp1 ψ
      (sourcePsiFillDeletedRoot n (s n ψ) (sourceStandardRootMidpoint hp hp1 ψ n)) z k hz

omit Q in
/-- The off-diagonal equality of (4.9), with the printed auxiliary quotient. -/
theorem offDiagonal_factor (ψ : CoeffPair p) (n k : ℤ) (hkn : k ≠ n) (z : ℂ)
    (hz : z ∈ sourceCanonicalRootDomain hp hp1 ψ) :
    sourcePsiCandidate n (z,(s n ψ : Coeff p))/sourceCanonicalRoot hp hp1 ψ z =
      ((displacedRoots (s n ψ : Coeff p) k-z)/sourceStandardRoot hp hp1 ψ k z)*
        sourceSection20PrintedAuxiliary hp hp1 s n k ψ z := by
  have hn : z ≠ sourceStandardRootMidpoint hp hp1 ψ n := by
    intro he
    exact hz n (he ▸ sourcePeriodicMidpoint_mem_segment hp hp1 ψ n)
  rw [auxiliary_eq_zeta ψ n k hkn z (fun j _ => hz j) hn]
  exact sourcePsiContourIntegrandJoint_eq_zeta hp hp1 n k hkn (s n ψ : Coeff p) ψ z hz

/-- A formal counterexample to the unrestricted analyticity claim after (4.9).
At the actual zero source, the printed diagonal factor has a genuine pole. -/
theorem printed_diagonal_auxiliary_not_continuous (n : ℤ) :
    ¬ ContinuousAt (sourceSection20PrintedAuxiliary hp hp1 s n n 0) ((Real.pi : ℂ)*n) := by
  let a : ℂ := (Real.pi : ℂ)*n
  have hmid : sourceStandardRootMidpoint hp hp1 (0 : CoeffPair p) n = a := by
    simp only [sourceStandardRootMidpoint,map_zero,canonicalPeriodicMidpoint_zero,a]
  have hfill : sourcePsiFillDeletedRoot n (s n 0) (sourceStandardRootMidpoint hp hp1 (0 : CoeffPair p) n) = 0 := by
    rw [Q.roots.toSourcePsiIsolatingComplexExtension.branch_zero,hmid]
    simp [sourcePsiFillDeletedRoot,a]
  have hG := isOpen_sourceStandardRootOmittedDomain_of_realType hp hp1 (0 : CoeffPair p)
    (by simp [realTypeSourceLocus] : (0 : CoeffPair p) ∈ realTypeSourceLocus p) n
  have ha := sourceStandardRootOmittedDomain_zero_source_contains_center hp hp1 n
  have he : ∀ᶠ z in 𝓝 a, sourceSection20PrintedAuxiliary hp hp1 s n n 0 z = Complex.I/(a-z) := by
    filter_upwards [hG.mem_nhds ha] with z hz
    unfold sourceSection20PrintedAuxiliary sourceSection20Zeta
    rw [hfill,hmid,sourceSingleRootQuotient_zero_free hp hp1 n z hz]
    ring
  intro hc
  have hlim : Tendsto (fun z => (a-z)*sourceSection20PrintedAuxiliary hp hp1 s n n 0 z)
      (𝓝[≠] a) (𝓝 0) := by
    have hc' : ContinuousAt (fun z : ℂ => (a-z)*sourceSection20PrintedAuxiliary hp hp1 s n n 0 z) a :=
      (continuousAt_const.sub continuousAt_id).mul hc
    simpa only [sub_self,zero_mul] using
      hc'.tendsto.mono_left (nhdsWithin_le_nhds (s := {a}ᶜ))
  have hlimI : Tendsto (fun z => (a-z)*sourceSection20PrintedAuxiliary hp hp1 s n n 0 z)
      (𝓝[≠] a) (𝓝 Complex.I) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [nhdsWithin_le_nhds he,self_mem_nhdsWithin] with z hz hza
    rw [hz]
    have hne : a-z ≠ 0 := sub_ne_zero.mpr (by simpa only [mem_compl_iff,mem_singleton_iff] using Ne.symm hza)
    field_simp
  exact Complex.I_ne_zero (tendsto_nhds_unique hlim hlimI).symm

end SourceSection20Data
end NLS.ZakharovShabat
