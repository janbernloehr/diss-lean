import NLS.KdV.HillHminusOneCanonicalActions
import NLS.KdV.MiuraPeriodicReflection
import NLS.ZakharovShabat.SourceHigherActionCoefficientContinuity

/-! Actual Miura higher actions and canonical endpoint slots preserve
bounded L2 coefficient limits. A positive central right endpoint excludes
zero Dirac frequency, with the complete original labeling retained. -/
noncomputable section
open Set Filter Topology Complex NLS.ZakharovShabat
namespace NLS.KdV

theorem bounded_hillMiuraDiagonal {α : Type*} (a : α → Coeff 2)
    (hb : Bornology.IsBounded (range a)) : Bornology.IsBounded (range (fun k => hillMiuraDiagonal (a k))) := by
  apply (hillMiuraDiagonal.lipschitz.isBounded_image hb).subset
  rintro _ ⟨k,rfl⟩
  exact ⟨a k,⟨k,rfl⟩,rfl⟩

theorem tendsto_hillHminusMiuraIndexedAction_of_bounded_coefficients
    {α : Type*} {l : Filter α} [l.IsCountablyGenerated]
    (u : α → PeriodOneRealL2) (v : PeriodOneRealL2)
    (hb : Bornology.IsBounded (range (fun k => (u k).val)))
    (ht : ∀ j : ℤ, Tendsto (fun k => (u k).val j) l (𝓝 (v.val j))) (n : ℤ) :
    Tendsto (fun k => hillHminusMiuraIndexedAction (u k).val n) l
      (𝓝 (hillHminusMiuraIndexedAction v.val n)) := by
  exact (tendsto_sourceIndexedHigherAction_of_bounded_coefficientwise
    (fun k => hillMiuraDiagonal (u k).val) (hillMiuraDiagonal v.val)
    (bounded_hillMiuraDiagonal _ hb) (fun k => (hillMiuraRealSource (u k)).property)
    (hillMiuraRealSource v).property (fun j => by simpa only [hillMiuraDiagonal_fst] using ht j) n 1).const_mul 2

theorem tendsto_hillMiuraDiracRight_of_bounded_coefficients
    {α : Type*} {l : Filter α} (u : α → PeriodOneRealL2) (v : PeriodOneRealL2)
    (hb : Bornology.IsBounded (range (fun k => (u k).val)))
    (ht : ∀ j : ℤ, Tendsto (fun k => (u k).val j) l (𝓝 (v.val j))) (n : ℤ) :
    Tendsto (fun k => hillMiuraDiracRight (u k).val n) l (𝓝 (hillMiuraDiracRight v.val n)) :=
  (tendsto_source_canonicalPeriodicEndpoints_of_bounded_coefficientwise (by simp) (by norm_num)
    (fun k => hillMiuraDiagonal (u k).val) (hillMiuraDiagonal v.val) (bounded_hillMiuraDiagonal _ hb)
    (fun k => (hillMiuraRealSource (u k)).property) (hillMiuraRealSource v).property (fun j => by simpa only [hillMiuraDiagonal_fst] using ht j) n).2

theorem zero_not_mem_hillMiura_spectrum_of_central_right_pos (u : PeriodOneRealL2)
    (hp : 0 < (hillMiuraDiracRight u.val 0).re) :
    (0:ℂ) ∉ periodicSpectrum (by simp) (periodOnePotential (hillMiuraDiagonal u.val)) := by
  intro hz
  obtain ⟨n,hn⟩ := (canonicalPeriodicEndpoints_exhaustive (by simp) (by norm_num)
    (periodOnePotential (hillMiuraDiagonal u.val)) (periodOnePotential_mem _) 0).mp hz
  have he : (hillMiuraDiracLeft u.val n).re=0 ∨ (hillMiuraDiracRight u.val n).re=0 := by
    rcases hn with h | h
    · exact Or.inl (congrArg Complex.re h)
    · exact Or.inr (congrArg Complex.re h)
  have ho := hillMiuraDiracPair_ordered u.val n
  rcases lt_trichotomy n 0 with hneg | hzero | hpos
  · have h := hillMiura_negative_gap_right_neg u n hneg
    change (hillMiuraDiracRight u.val n).re < 0 at h
    rcases he with he | he <;> linarith
  · subst n
    have href := congrArg Complex.re ((hillMiuraDiracPair_neg u.val).1 0)
    simp only [neg_zero,neg_re] at href
    rcases he with he | he <;> linarith
  · have h := hillMiura_positive_gap_left_pos u n hpos
    change 0 < (hillMiuraDiracLeft u.val n).re at h
    rcases he with he | he <;> linarith

end NLS.KdV
