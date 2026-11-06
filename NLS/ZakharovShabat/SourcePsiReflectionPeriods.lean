import NLS.ZakharovShabat.SourceCanonicalRootReflection
import NLS.ZakharovShabat.SourceTheorem12_1
import NLS.ComplexAnalysis.CircleIntegralReflection
import NLS.ComplexAnalysis.OddSquareDescent

/-! Exact periods after odd quadratic descent of the actual normalized
Dirac numerator. Reflection preserves the circle orientation and root sign;
its opposite-index period is subtracted, with no extra factor of two. -/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual reflected original isolating circle at the opposite signed index. -/
def SourcePeriodicReflection.periodCircleNeg
    {hp : p ≠ ⊤} {hp1 : 1 < p} {ψ : CoeffPair p} (h : SourcePeriodicReflection hp hp1 ψ)
    {m : ℤ} (D : SourceCriticalRootPeriodCircle hp hp1 ψ m) :
    SourceCriticalRootPeriodCircle hp hp1 ψ (-m) where
  center := -D.center
  radius := D.radius
  radius_pos := D.radius_pos
  gap := by
    intro z hz
    have hn : -z ∈ sourcePeriodicSegment hp hp1 ψ m :=
      (h.neg_mem_segment_iff m (-z)).mp (by simpa only [neg_neg] using hz)
    have hb := D.gap hn
    simp only [mem_ball,dist_eq_norm,ofReal_neg] at hb ⊢
    have he : z-(-(D.center:ℂ)) = -((-z)-(D.center:ℂ)) := by ring
    simpa only [he,norm_neg] using hb
  other := by
    intro k hk z hz
    have hn : -z ∈ sourcePeriodicSegment hp hp1 ψ (-k) :=
      (h.neg_mem_segment_iff (-k) (-z)).mp (by simpa only [neg_neg] using hz)
    have hkm : -k ≠ m := by intro he; apply hk; simpa only [neg_neg] using congrArg Neg.neg he
    have hh := D.other (-k) hkm (-z) hn
    simp only [Complex.neg_re] at hh
    rcases hh with hh | hh
    · exact Or.inr (by linarith)
    · exact Or.inl (by linarith)

/-- Circle integrability of an entire numerator divided by the actual canonical root. -/
theorem SourceCriticalRootPeriodCircle.psi_div_root_circleIntegrable
    {hp : p ≠ ⊤} {hp1 : 1 < p} {ψ : CoeffPair p} {m : ℤ}
    (D : SourceCriticalRootPeriodCircle hp hp1 ψ m) (n : ℤ) (a : Coeff p) (b : ℂ) :
    CircleIntegrable (fun z => sourcePsiCandidate n (b*z,a)/sourceCanonicalRoot hp hp1 ψ z)
      (D.center:ℂ) D.radius := by
  apply ContinuousOn.circleIntegrable D.radius_pos.le
  intro z hz
  have hn : AnalyticAt ℂ (fun w => sourcePsiCandidate n (b*w,a)) z :=
    (analyticOnNhd_sourcePsiCandidate hp hp1 n (b*z,a) (mem_univ _)).comp
      (f := fun w : ℂ => (b*w,a)) ((analyticAt_const.mul analyticAt_id).prod analyticAt_const)
  exact (hn.div (sourceCanonicalRoot_analyticOnNhd hp hp1 ψ z (D.sphere_subset_rootDomain hz))
    (sourceCanonicalRoot_ne_zero_off_gaps hp hp1 ψ z (D.sphere_subset_rootDomain hz))).continuousAt.continuousWithinAt

/-- Odd numerators have the difference of the actual signed Kronecker periods. -/
theorem SourceTheorem12_1Data.odd_numerator_period
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W : Set (CoeffPair p)}
    {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
    (H : SourceTheorem12_1Data hp hp1 W₀ W s)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (h : SourcePeriodicReflection hp hp1 ψ)
    (n m : ℤ) (D : SourceCriticalRootPeriodCircle hp hp1 ψ m) :
    (2*Real.pi:ℂ)⁻¹*(∮ z in C((D.center:ℂ),D.radius),
      (sourcePsiCandidate n (z,(s n ψ:Coeff p))-sourcePsiCandidate n (-z,(s n ψ:Coeff p)))/
        sourceCanonicalRoot hp hp1 ψ z) =
      (if m = n then 1 else 0)-(if -m = n then 1 else 0) := by
  let a : Coeff p := s n ψ
  let f : ℂ → ℂ := fun z => sourcePsiCandidate n (z,a)/sourceCanonicalRoot hp hp1 ψ z
  have he (z : ℂ) : sourcePsiCandidate n (-z,a)/sourceCanonicalRoot hp hp1 ψ z = -f (-z) := by
    dsimp only [f]
    rw [h.canonicalRoot_neg z]
    simp only [div_neg,neg_neg]
  have hi : (∮ z in C((D.center:ℂ),D.radius), sourcePsiCandidate n (-z,a)/sourceCanonicalRoot hp hp1 ψ z) =
      ∮ z in C((-(D.center):ℂ),D.radius), f z := by
    simp_rw [he]
    simpa only [ofReal_neg] using circleIntegral_neg_pullback f (D.center:ℂ) D.radius
  have hf : CircleIntegrable f (D.center:ℂ) D.radius := by
    simpa only [f,one_mul] using D.psi_div_root_circleIntegrable n a 1
  have hg : CircleIntegrable (fun z => sourcePsiCandidate n (-z,a)/sourceCanonicalRoot hp hp1 ψ z)
      (D.center:ℂ) D.radius := by
    simpa only [neg_one_mul] using D.psi_div_root_circleIntegrable n a (-1)
  simp_rw [sub_div]
  rw [circleIntegral.integral_sub hf hg,hi,mul_sub,← ofReal_neg D.center]
  change sourcePsiContour hp hp1 n a ψ (D.center:ℂ) D.radius-
    sourcePsiContour hp hp1 n a ψ (((h.periodCircleNeg D).center):ℂ) (h.periodCircleNeg D).radius = _
  rw [H.period ψ hψ n m D,H.period ψ hψ n (-m) (h.periodCircleNeg D)]

/-- Actual original period circles exist at EVERY source and signed index in W. -/
theorem SourceTheorem12_1Data.nonempty_periodCircle
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W : Set (CoeffPair p)}
    {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
    (H : SourceTheorem12_1Data hp hp1 W₀ W s)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (m : ℤ) :
    Nonempty (SourceCriticalRootPeriodCircle hp hp1 ψ m) := by
  obtain ⟨V,_,_,hψV,_,D,c,hD⟩ :=
    H.previous.previous.previous.criticalOffsets.previous.previous.neighborhoods ψ (H.subset hψ)
  obtain ⟨a,r,hr,he⟩ := hD.discs m
  exact ⟨hD.toSourceIsolatingNeighborhoods.periodCircle ψ hψV m a r hr he⟩

/-- The actual selected entire Dirac numerator family. -/
def sourceSelectedPsiNumerator (s : (n : ℤ) → CoeffPair p → DeletedCoeff p n) (n : ℤ)
    (t : ℂ × CoeffPair p) : ℂ := sourcePsiDeletedCandidate n (t.1,s n t.2)

/-- Its odd quadratic descent, with the removable zero-frequency value filled. -/
def sourcePsiEnergyNumerator (s : (n : ℤ) → CoeffPair p → DeletedCoeff p n) (n : ℤ) :
    ℂ × CoeffPair p → ℂ := oddSquareDescent (sourceSelectedPsiNumerator s n)

theorem SourceTheorem12_1Data.analytic_selectedPsiNumerator
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W : Set (CoeffPair p)}
    {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
    (H : SourceTheorem12_1Data hp hp1 W₀ W s) (n : ℤ) :
    AnalyticOnNhd ℂ (sourceSelectedPsiNumerator s n) (univ ×ˢ W) := by
  intro t ht
  exact (analyticOnNhd_sourcePsiDeletedCandidate hp hp1 n (t.1,s n t.2) (mem_univ _)).comp
    (f := fun x : ℂ × CoeffPair p => (x.1,s n x.2))
    (analyticAt_fst.prod ((H.analytic n t.2 ht.2).comp (f := Prod.snd) analyticAt_snd))

theorem SourceTheorem12_1Data.analytic_energyNumerator
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W : Set (CoeffPair p)}
    {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
    (H : SourceTheorem12_1Data hp hp1 W₀ W s) (hW : IsOpen W) (n : ℤ) :
    AnalyticOnNhd ℂ (sourcePsiEnergyNumerator s n) (univ ×ˢ W) :=
  analyticOnNhd_oddSquareDescent _ W hW (H.analytic_selectedPsiNumerator n)

/-- Exact Hill energy pullback periods, with the literal original 1/(2π). -/
theorem SourceTheorem12_1Data.energyNumerator_pullback_period
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W : Set (CoeffPair p)}
    {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
    (H : SourceTheorem12_1Data hp hp1 W₀ W s)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (h : SourcePeriodicReflection hp hp1 ψ)
    (n m : ℤ) (D : SourceCriticalRootPeriodCircle hp hp1 ψ m) :
    (2*Real.pi:ℂ)⁻¹*(∮ z in C((D.center:ℂ),D.radius),
      (2*z*sourcePsiEnergyNumerator s n (z^2,ψ))/sourceCanonicalRoot hp hp1 ψ z) =
      (if m = n then 1 else 0)-(if -m = n then 1 else 0) := by
  have he (z : ℂ) : 2*z*sourcePsiEnergyNumerator s n (z^2,ψ) =
      sourcePsiCandidate n (z,(s n ψ:Coeff p))-sourcePsiCandidate n (-z,(s n ψ:Coeff p)) :=
    two_mul_frequency_oddSquareDescent (sourceSelectedPsiNumerator s n) ψ z
  simp_rw [he]
  exact H.odd_numerator_period ψ hψ h n m D

end NLS.ZakharovShabat
