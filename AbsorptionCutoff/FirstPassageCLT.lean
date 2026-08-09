/-
Copyright (c) 2026 Benny Avelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benny Avelin
-/
import Mathlib.Probability.CDF
import Mathlib.Probability.CentralLimitTheorem
import Mathlib.Probability.IdentDistribIndep
import Mathlib.Probability.Process.HittingTime
import Mathlib.Probability.StrongLaw

/-!
# First-passage central limit theorem

Path functionals for the positive-drift random-walk first-passage theorem used
in the fixed-width cutoff argument. This module is a pure-Mathlib leaf.
-/

open MeasureTheory
open Filter

namespace AbsorptionCutoff

variable {Ω : Type*}

/-- Partial sums of a real-valued process, with `partialSum X n` summing the
increments at indices strictly below `n`. -/
def partialSum (X : ℕ → Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  fun ω ↦ ∑ j ∈ Finset.range n, X j ω

/-- Running maximum of the partial sums through time `n`. -/
def runningMax (X : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => fun _ ↦ 0
  | n + 1 => fun ω ↦ max (runningMax X n ω) (partialSum X (n + 1) ω)

/-- Drawdown of the terminal partial sum from the running maximum. -/
def terminalDrawdown (X : ℕ → Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  fun ω ↦ runningMax X n ω - partialSum X n ω

/-- First weak ascending passage time of the partial sums above `u`. -/
noncomputable def firstPassageTime (X : ℕ → Ω → ℝ) (u : ℝ) : Ω → WithTop ℕ :=
  hittingAfter (partialSum X) (Set.Ici u) 0

/-- Reversal of a finite increment block. -/
def finiteReversal (n : ℕ) : Equiv.Perm (Fin n) :=
  Fin.revPerm

@[simp]
lemma finiteReversal_apply (n : ℕ) (j : Fin n) :
    finiteReversal n j = j.rev := by
  simp [finiteReversal]

/-- Sum of the last `j` increments in the block ending at time `n`. The
intended range is `j ≤ n`. -/
def backwardPartialSum (X : ℕ → Ω → ℝ) (n j : ℕ) : Ω → ℝ :=
  fun ω ↦ ∑ r ∈ Finset.range j, X (n - 1 - r) ω

/-- Maximum of the negatives of the backward partial sums through time `n`. -/
noncomputable def negativeBackwardRunningMax
    (X : ℕ → Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  fun ω ↦ (Finset.range (n + 1)).sup' (by simp)
    (fun j ↦ -backwardPartialSum X n j ω)

/-- Read a coordinate from a finite block, returning zero past the block. -/
def finiteBlockValue (n : ℕ) (x : Fin n → ℝ) (j : ℕ) : ℝ :=
  if h : j < n then x ⟨j, h⟩ else 0

/-- The largest negative partial sum of a finite real block. -/
noncomputable def finiteNegativeRunningMax (n : ℕ) : (Fin n → ℝ) → ℝ :=
  fun x ↦ (Finset.range (n + 1)).sup' (by simp)
    (fun j ↦ -(∑ r ∈ Finset.range j, finiteBlockValue n x r))

/-- The first `n` coordinates of an increment process. -/
def finiteIncrementBlock (X : ℕ → Ω → ℝ) (n : ℕ) : Ω → Fin n → ℝ :=
  fun ω j ↦ X j ω

/-- Maximum of the negative forward partial sums through time `n`. -/
noncomputable def negativeRunningMax (X : ℕ → Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  fun ω ↦ finiteNegativeRunningMax n (finiteIncrementBlock X n ω)

/-- Event that every partial sum stays above the integer lower bound `-m`. -/
def lowerBoundEvent (X : ℕ → Ω → ℝ) (m : ℕ) : Set Ω :=
  {ω | ∀ j : ℕ, -(m : ℝ) ≤ partialSum X j ω}

@[simp]
lemma mem_lowerBoundEvent (X : ℕ → Ω → ℝ) (m : ℕ) (ω : Ω) :
    ω ∈ lowerBoundEvent X m ↔ ∀ j : ℕ, -(m : ℝ) ≤ partialSum X j ω :=
  Iff.rfl

lemma monotone_lowerBoundEvent (X : ℕ → Ω → ℝ) :
    Monotone (lowerBoundEvent X) := by
  intro m n hmn ω hω
  rw [mem_lowerBoundEvent] at hω ⊢
  intro j
  exact (neg_le_neg (Nat.cast_le.mpr hmn)).trans (hω j)

@[simp]
lemma partialSum_zero (X : ℕ → Ω → ℝ) : partialSum X 0 = 0 := by
  ext ω
  simp [partialSum]

lemma partialSum_succ (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    partialSum X (n + 1) ω = partialSum X n ω + X n ω := by
  simp [partialSum, Finset.sum_range_succ]

/-- A backward partial sum is the terminal sum minus the partial sum before
that terminal block. -/
lemma backwardPartialSum_eq_sub (X : ℕ → Ω → ℝ) (n j : ℕ)
    (hjn : j ≤ n) (ω : Ω) :
    backwardPartialSum X n j ω =
      partialSum X n ω - partialSum X (n - j) ω := by
  rw [backwardPartialSum]
  have hreflect := Finset.sum_range_reflect
    (fun r ↦ X ((n - j) + r) ω) j
  have hreverse :
      ∑ r ∈ Finset.range j, X (n - 1 - r) ω =
        ∑ r ∈ Finset.range j, X ((n - j) + (j - 1 - r)) ω := by
    apply Finset.sum_congr rfl
    intro r hr
    congr 2
    simp only [Finset.mem_range] at hr
    omega
  rw [hreverse, hreflect]
  have hadd := Finset.sum_range_add (fun r ↦ X r ω) (n - j) j
  rw [Nat.sub_add_cancel hjn] at hadd
  simp only [partialSum] at hadd ⊢
  linarith

lemma negativeRunningMax_eq (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    negativeRunningMax X n ω =
      (Finset.range (n + 1)).sup' (by simp)
        (fun j ↦ -partialSum X j ω) := by
  unfold negativeRunningMax finiteNegativeRunningMax
  apply Finset.sup'_congr _ rfl
  intro j hj
  congr 1
  rw [partialSum]
  apply Finset.sum_congr rfl
  intro r hr
  have hrn : r < n := lt_of_lt_of_le (Finset.mem_range.mp hr)
    (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
  simp [finiteBlockValue, finiteIncrementBlock, hrn]

lemma finiteNegativeRunningMax_reversed_eq
    (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    finiteNegativeRunningMax n (fun i ↦ X (finiteReversal n i) ω) =
      negativeBackwardRunningMax X n ω := by
  unfold finiteNegativeRunningMax negativeBackwardRunningMax
  apply Finset.sup'_congr _ rfl
  intro j hj
  congr 1
  rw [backwardPartialSum]
  apply Finset.sum_congr rfl
  intro r hr
  have hrn : r < n := lt_of_lt_of_le (Finset.mem_range.mp hr)
    (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
  rw [finiteBlockValue, dif_pos hrn]
  congr 2
  simp [finiteReversal, Fin.val_rev]
  omega

/-- A real sequence whose normalized values converge to a positive limit is
bounded below by the negative of some natural number. -/
lemma exists_nat_neg_le_forall_of_tendsto_div_atTop
    (S : ℕ → ℝ) {a : ℝ} (ha : 0 < a)
    (h : Tendsto (fun n : ℕ ↦ S n / (n : ℝ)) atTop (nhds a)) :
    ∃ m : ℕ, ∀ n : ℕ, -(m : ℝ) ≤ S n := by
  have hev : ∀ᶠ n : ℕ in atTop, 0 < S n / (n : ℝ) :=
    (tendsto_order.mp h).1 0 ha
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
  obtain ⟨m, hm⟩ := exists_nat_ge (∑ k ∈ Finset.range N, |S k|)
  refine ⟨m, fun n ↦ ?_⟩
  by_cases hn : n < N
  · have hterm : |S n| ≤ ∑ k ∈ Finset.range N, |S k| :=
      Finset.single_le_sum (fun k _ ↦ abs_nonneg (S k)) (Finset.mem_range.mpr hn)
    exact neg_le_of_abs_le (hterm.trans hm)
  · have hratio := hN n (le_of_not_gt hn)
    rcases div_pos_iff.mp hratio with hpos | hneg
    · exact (neg_nonpos.mpr (Nat.cast_nonneg m)).trans hpos.1.le
    · exact (not_lt_of_ge (Nat.cast_nonneg n) hneg.2).elim

/-- The recursive running maximum is below `u` precisely when every partial
sum through its terminal time is below `u`. -/
lemma runningMax_lt_iff (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) (u : ℝ) :
    runningMax X n ω < u ↔ ∀ k ≤ n, partialSum X k ω < u := by
  induction n with
  | zero => simp [runningMax, partialSum]
  | succ n ih =>
      rw [runningMax, max_lt_iff, ih]
      constructor
      · rintro ⟨hprev, hlast⟩ k hk
        rcases lt_or_eq_of_le hk with hk | rfl
        · exact hprev k (Nat.lt_succ_iff.mp hk)
        · exact hlast
      · intro h
        exact ⟨fun k hk ↦ h k (hk.trans n.le_succ), h (n + 1) le_rfl⟩

lemma partialSum_le_runningMax (X : ℕ → Ω → ℝ)
    {k n : ℕ} (hkn : k ≤ n) (ω : Ω) :
    partialSum X k ω ≤ runningMax X n ω := by
  by_contra h
  have hlt : runningMax X n ω < partialSum X k ω := lt_of_not_ge h
  exact (lt_irrefl (partialSum X k ω))
    ((runningMax_lt_iff X n ω (partialSum X k ω)).mp hlt k hkn)

lemma exists_runningMax_eq_partialSum (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    ∃ k ≤ n, runningMax X n ω = partialSum X k ω := by
  induction n with
  | zero =>
      exact ⟨0, le_rfl, by simp [runningMax]⟩
  | succ n ih =>
      rcases max_choice (runningMax X n ω) (partialSum X (n + 1) ω) with h | h
      · obtain ⟨k, hkn, hk⟩ := ih
        exact ⟨k, hkn.trans n.le_succ, by simpa [runningMax, h] using hk⟩
      · exact ⟨n + 1, le_rfl, by simp [runningMax, h]⟩

/-- Pathwise finite-reversal identity: terminal drawdown is the largest
negative backward partial sum. -/
lemma terminalDrawdown_eq_negativeBackwardRunningMax
    (X : ℕ → Ω → ℝ) (n : ℕ) :
    terminalDrawdown X n = negativeBackwardRunningMax X n := by
  ext ω
  apply le_antisymm
  · obtain ⟨k, hkn, hk⟩ := exists_runningMax_eq_partialSum X n ω
    have hmem : n - k ∈ Finset.range (n + 1) := by
      simp only [Finset.mem_range]
      exact Nat.lt_succ_of_le (Nat.sub_le n k)
    calc
      terminalDrawdown X n ω =
          partialSum X k ω - partialSum X n ω := by rw [terminalDrawdown, hk]
      _ = -backwardPartialSum X n (n - k) ω := by
        rw [backwardPartialSum_eq_sub X n (n - k) (Nat.sub_le n k)]
        rw [Nat.sub_sub_self hkn]
        ring
      _ ≤ negativeBackwardRunningMax X n ω := by
        exact Finset.le_sup'
          (fun j : ℕ ↦ (-backwardPartialSum X n j ω : ℝ)) hmem
  · rw [negativeBackwardRunningMax, Finset.sup'_le_iff]
    intro j hj
    have hjle : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    have hpath := partialSum_le_runningMax X (Nat.sub_le n j) ω
    rw [backwardPartialSum_eq_sub X n j hjle, terminalDrawdown]
    linarith

/-- Survival through time `n` is the event that the running maximum through
`n` remains strictly below the weak-passage level `u`. -/
lemma firstPassageTime_gt_iff_runningMax_lt (X : ℕ → Ω → ℝ)
    (u : ℝ) (n : ℕ) (ω : Ω) :
    (n : WithTop ℕ) < firstPassageTime X u ω ↔ runningMax X n ω < u := by
  constructor
  · intro hhit
    rw [runningMax_lt_iff]
    intro k hk
    by_contra hku
    have hle' : hittingAfter (partialSum X) (Set.Ici u) 0 ω ≤ (n : WithTop ℕ) :=
      (hittingAfter_le_iff (u := partialSum X) (s := Set.Ici u)
        (n := 0) (i := n) (ω := ω)).mpr ⟨k, by simp [hk], le_of_not_gt hku⟩
    exact (not_le_of_gt hhit) (by simpa [firstPassageTime] using hle')
  · intro hmax
    rw [← not_le]
    intro hle
    have hle' : hittingAfter (partialSum X) (Set.Ici u) 0 ω ≤ (n : WithTop ℕ) := by
      simpa [firstPassageTime] using hle
    obtain ⟨k, hk, hku⟩ :=
      (hittingAfter_le_iff (u := partialSum X) (s := Set.Ici u)
        (n := 0) (i := n) (ω := ω)).mp hle'
    exact (not_lt_of_ge hku) ((runningMax_lt_iff X n ω u).mp hmax k hk.2)

lemma firstPassageTime_gt_set_eq (X : ℕ → Ω → ℝ) (u : ℝ) (n : ℕ) :
    {ω | (n : WithTop ℕ) < firstPassageTime X u ω} =
      {ω | runningMax X n ω < u} :=
  Set.ext fun ω ↦ firstPassageTime_gt_iff_runningMax_lt X u n ω

variable [MeasurableSpace Ω]

lemma measurable_finiteBlockValue (n j : ℕ) :
    Measurable (fun x : Fin n → ℝ ↦ finiteBlockValue n x j) := by
  unfold finiteBlockValue
  split_ifs with h
  · exact measurable_pi_apply (⟨j, h⟩ : Fin n)
  · exact measurable_const

lemma measurable_finiteNegativeRunningMax (n : ℕ) :
    Measurable (finiteNegativeRunningMax n) := by
  unfold finiteNegativeRunningMax
  let hs : (Finset.range (n + 1)).Nonempty := ⟨0, by simp⟩
  have h : Measurable ((Finset.range (n + 1)).sup' hs
      (fun j x ↦ -(∑ r ∈ Finset.range j, finiteBlockValue n x r))) := by
    apply Finset.measurable_sup'
    intro j hj
    exact (Finset.measurable_sum _ fun r _ ↦ measurable_finiteBlockValue n r).neg
  convert h using 1
  ext x
  exact (Finset.sup'_apply hs
    (fun j x ↦ -(∑ r ∈ Finset.range j, finiteBlockValue n x r)) x).symm

lemma measurable_finiteIncrementBlock (X : ℕ → Ω → ℝ)
    (hX : ∀ j, Measurable (X j)) (n : ℕ) :
    Measurable (finiteIncrementBlock X n) := by
  exact measurable_pi_lambda _ fun j ↦ hX j

lemma measurable_negativeRunningMax (X : ℕ → Ω → ℝ)
    (hX : ∀ j, Measurable (X j)) (n : ℕ) :
    Measurable (negativeRunningMax X n) :=
  (measurable_finiteNegativeRunningMax n).comp
    (measurable_finiteIncrementBlock X hX n)

lemma measurable_partialSum (X : ℕ → Ω → ℝ) (hX : ∀ j, Measurable (X j)) (n : ℕ) :
    Measurable (partialSum X n) := by
  exact Finset.measurable_sum _ fun j _ ↦ hX j

lemma measurableSet_lowerBoundEvent (X : ℕ → Ω → ℝ)
    (hX : ∀ j, Measurable (X j)) (m : ℕ) :
    MeasurableSet (lowerBoundEvent X m) := by
  rw [show lowerBoundEvent X m =
      ⋂ j : ℕ, {ω | -(m : ℝ) ≤ partialSum X j ω} by ext ω; simp]
  exact MeasurableSet.iInter fun j ↦
    (measurable_partialSum X hX j) measurableSet_Ici

lemma measurable_runningMax (X : ℕ → Ω → ℝ) (hX : ∀ j, Measurable (X j)) :
    ∀ n, Measurable (runningMax X n)
  | 0 => measurable_const
  | n + 1 => (measurable_runningMax X hX n).max (measurable_partialSum X hX (n + 1))

lemma measurable_terminalDrawdown (X : ℕ → Ω → ℝ) (hX : ∀ j, Measurable (X j))
    (n : ℕ) : Measurable (terminalDrawdown X n) :=
  (measurable_runningMax X hX n).sub (measurable_partialSum X hX n)

lemma measurableSet_firstPassageTime_gt (X : ℕ → Ω → ℝ)
    (hX : ∀ j, Measurable (X j)) (u : ℝ) (n : ℕ) :
    MeasurableSet {ω | (n : WithTop ℕ) < firstPassageTime X u ω} := by
  rw [firstPassageTime_gt_set_eq]
  exact (measurable_runningMax X hX n) measurableSet_Iio

variable {μ : Measure Ω}

/-- An iid finite increment block has the same law after reversal. -/
lemma identDistrib_reversed_finiteIncrementBlock
    (X : ℕ → Ω → ℝ) (n : ℕ)
    (hIndep : ProbabilityTheory.iIndepFun X μ)
    (hIdent : ∀ j, ProbabilityTheory.IdentDistrib (X j) (X 0) μ μ) :
    ProbabilityTheory.IdentDistrib
      (fun ω i ↦ X (finiteReversal n i) ω) (finiteIncrementBlock X n) μ μ := by
  apply ProbabilityTheory.IdentDistrib.pi
  · intro i
    exact (hIdent (finiteReversal n i)).trans (hIdent i).symm
  · exact hIndep.precomp (Fin.val_injective.comp (finiteReversal n).injective)
  · exact hIndep.precomp Fin.val_injective

/-- Finite reversal identifies the negative backward and forward running
maxima in distribution. -/
lemma identDistrib_negativeBackwardRunningMax_negativeRunningMax
    (X : ℕ → Ω → ℝ) (n : ℕ)
    (hIndep : ProbabilityTheory.iIndepFun X μ)
    (hIdent : ∀ j, ProbabilityTheory.IdentDistrib (X j) (X 0) μ μ) :
    ProbabilityTheory.IdentDistrib
      (negativeBackwardRunningMax X n) (negativeRunningMax X n) μ μ := by
  have hblock := identDistrib_reversed_finiteIncrementBlock X n hIndep hIdent
  have hmax := hblock.comp (measurable_finiteNegativeRunningMax n)
  convert hmax using 1
  · funext ω
    exact (finiteNegativeRunningMax_reversed_eq X n ω).symm
  · rfl

/-- The terminal drawdown and the negative running maximum are identically
distributed for iid increments. -/
lemma identDistrib_terminalDrawdown_negativeRunningMax
    (X : ℕ → Ω → ℝ) (n : ℕ)
    (hIndep : ProbabilityTheory.iIndepFun X μ)
    (hIdent : ∀ j, ProbabilityTheory.IdentDistrib (X j) (X 0) μ μ) :
    ProbabilityTheory.IdentDistrib
      (terminalDrawdown X n) (negativeRunningMax X n) μ μ := by
  rw [terminalDrawdown_eq_negativeBackwardRunningMax]
  exact identDistrib_negativeBackwardRunningMax_negativeRunningMax X n hIndep hIdent

/-- Positive drift and the strong law imply that the partial-sum path is
almost surely bounded below by a random integer. -/
lemma ae_exists_nat_neg_le_partialSum
    (X : ℕ → Ω → ℝ)
    (hInt : Integrable (X 0) μ)
    (hIndep : ProbabilityTheory.iIndepFun X μ)
    (hIdent : ∀ j, ProbabilityTheory.IdentDistrib (X j) (X 0) μ μ)
    (hMean : 0 < ∫ ω, X 0 ω ∂μ) :
    ∀ᵐ ω ∂μ, ∃ m : ℕ, ∀ j : ℕ, -(m : ℝ) ≤ partialSum X j ω := by
  have hslln := ProbabilityTheory.strong_law_ae_real X hInt
    (fun i j hij ↦ hIndep.indepFun hij) hIdent
  filter_upwards [hslln] with ω hω
  exact exists_nat_neg_le_forall_of_tendsto_div_atTop
    (fun n ↦ partialSum X n ω) hMean (by simpa only [partialSum] using hω)

lemma ae_mem_iUnion_lowerBoundEvent
    (X : ℕ → Ω → ℝ)
    (hInt : Integrable (X 0) μ)
    (hIndep : ProbabilityTheory.iIndepFun X μ)
    (hIdent : ∀ j, ProbabilityTheory.IdentDistrib (X j) (X 0) μ μ)
    (hMean : 0 < ∫ ω, X 0 ω ∂μ) :
    ∀ᵐ ω ∂μ, ω ∈ ⋃ m : ℕ, lowerBoundEvent X m := by
  filter_upwards [ae_exists_nat_neg_le_partialSum X hInt hIndep hIdent hMean]
    with ω hω
  obtain ⟨m, hm⟩ := hω
  exact Set.mem_iUnion.mpr ⟨m, hm⟩

/-- The increasing lower-bound events exhaust a set of probability one. -/
lemma measure_iUnion_lowerBoundEvent_eq_one
    (X : ℕ → Ω → ℝ)
    (hInt : Integrable (X 0) μ)
    (hIndep : ProbabilityTheory.iIndepFun X μ)
    (hIdent : ∀ j, ProbabilityTheory.IdentDistrib (X j) (X 0) μ μ)
    (hMean : 0 < ∫ ω, X 0 ω ∂μ) :
    μ (⋃ m : ℕ, lowerBoundEvent X m) = 1 := by
  letI : IsProbabilityMeasure μ := hIndep.isProbabilityMeasure
  calc
    μ (⋃ m : ℕ, lowerBoundEvent X m) = μ Set.univ := by
      apply measure_congr
      filter_upwards [ae_mem_iUnion_lowerBoundEvent X hInt hIndep hIdent hMean]
        with ω hω
      exact propext ⟨fun _ ↦ Set.mem_univ ω, fun _ ↦ hω⟩
    _ = 1 := measure_univ

omit [MeasurableSpace Ω] in
lemma negativeRunningMax_le_of_mem_lowerBoundEvent
    (X : ℕ → Ω → ℝ) (m n : ℕ) {ω : Ω}
    (hω : ω ∈ lowerBoundEvent X m) :
    negativeRunningMax X n ω ≤ m := by
  rw [negativeRunningMax_eq, Finset.sup'_le_iff]
  intro j hj
  have hlower := hω j
  linarith

omit [MeasurableSpace Ω] in
lemma negativeRunningMax_gt_subset_compl_lowerBoundEvent
    (X : ℕ → Ω → ℝ) (m n : ℕ) :
    {ω | (m : ℝ) < negativeRunningMax X n ω} ⊆
      (lowerBoundEvent X m)ᶜ := by
  intro ω hω
  rw [Set.mem_compl_iff]
  exact fun hmem ↦
    (not_lt_of_ge (negativeRunningMax_le_of_mem_lowerBoundEvent X m n hmem)) hω

lemma measure_terminalDrawdown_gt_le_compl_lowerBoundEvent
    (X : ℕ → Ω → ℝ) (m n : ℕ)
    (hIndep : ProbabilityTheory.iIndepFun X μ)
    (hIdent : ∀ j, ProbabilityTheory.IdentDistrib (X j) (X 0) μ μ) :
    μ {ω | (m : ℝ) < terminalDrawdown X n ω} ≤
      μ (lowerBoundEvent X m)ᶜ := by
  calc
    μ {ω | (m : ℝ) < terminalDrawdown X n ω} =
        μ {ω | (m : ℝ) < negativeRunningMax X n ω} := by
      change μ (terminalDrawdown X n ⁻¹' Set.Ioi (m : ℝ)) =
        μ (negativeRunningMax X n ⁻¹' Set.Ioi (m : ℝ))
      exact
        (identDistrib_terminalDrawdown_negativeRunningMax X n hIndep hIdent).measure_preimage_eq
          measurableSet_Ioi
    _ ≤ μ (lowerBoundEvent X m)ᶜ :=
      measure_mono (negativeRunningMax_gt_subset_compl_lowerBoundEvent X m n)

lemma tendsto_measure_compl_lowerBoundEvent_atTop
    (X : ℕ → Ω → ℝ)
    (hX : ∀ j, Measurable (X j))
    (hInt : Integrable (X 0) μ)
    (hIndep : ProbabilityTheory.iIndepFun X μ)
    (hIdent : ∀ j, ProbabilityTheory.IdentDistrib (X j) (X 0) μ μ)
    (hMean : 0 < ∫ ω, X 0 ω ∂μ) :
    Tendsto (μ ∘ fun m : ℕ ↦ (lowerBoundEvent X m)ᶜ) atTop (nhds 0) := by
  letI : IsProbabilityMeasure μ := hIndep.isProbabilityMeasure
  have hUmeas : MeasurableSet (⋃ m : ℕ, lowerBoundEvent X m) :=
    MeasurableSet.iUnion fun m ↦ measurableSet_lowerBoundEvent X hX m
  have hU : μ (⋃ m : ℕ, lowerBoundEvent X m) = 1 :=
    measure_iUnion_lowerBoundEvent_eq_one X hInt hIndep hIdent hMean
  have hInter : μ (⋂ m : ℕ, (lowerBoundEvent X m)ᶜ) = 0 := by
    rw [← Set.compl_iUnion]
    calc
      μ (⋃ m : ℕ, lowerBoundEvent X m)ᶜ =
          μ Set.univ - μ (⋃ m : ℕ, lowerBoundEvent X m) :=
        measure_compl hUmeas (by rw [hU]; simp)
      _ = 0 := by rw [measure_univ, hU]; simp
  have hfinite : μ (lowerBoundEvent X 0)ᶜ ≠ ⊤ := by
    apply ne_of_lt
    calc
      μ (lowerBoundEvent X 0)ᶜ ≤ μ Set.univ :=
        measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
      _ < ⊤ := ENNReal.one_lt_top
  have ht := tendsto_measure_iInter_atTop
    (s := fun m : ℕ ↦ (lowerBoundEvent X m)ᶜ)
    (fun m ↦ (measurableSet_lowerBoundEvent X hX m).compl.nullMeasurableSet)
    (fun m n hmn ↦ Set.compl_subset_compl.mpr (monotone_lowerBoundEvent X hmn))
    ⟨0, hfinite⟩
  rw [hInter] at ht
  exact ht

lemma tendsto_measureReal_compl_lowerBoundEvent_atTop
    (X : ℕ → Ω → ℝ)
    (hX : ∀ j, Measurable (X j))
    (hInt : Integrable (X 0) μ)
    (hIndep : ProbabilityTheory.iIndepFun X μ)
    (hIdent : ∀ j, ProbabilityTheory.IdentDistrib (X j) (X 0) μ μ)
    (hMean : 0 < ∫ ω, X 0 ω ∂μ) :
    Tendsto (fun m : ℕ ↦ μ.real (lowerBoundEvent X m)ᶜ) atTop (nhds 0) := by
  have ht := tendsto_measure_compl_lowerBoundEvent_atTop
    X hX hInt hIndep hIdent hMean
  have hreal := (ENNReal.tendsto_toReal (a := 0) (by simp)).comp ht
  convert hreal using 1 <;> rfl

/-- The terminal drawdowns of a positive-drift iid walk are uniformly tight. -/
lemma exists_uniform_terminalDrawdown_tail_lt
    (X : ℕ → Ω → ℝ)
    (hX : ∀ j, Measurable (X j))
    (hInt : Integrable (X 0) μ)
    (hIndep : ProbabilityTheory.iIndepFun X μ)
    (hIdent : ∀ j, ProbabilityTheory.IdentDistrib (X j) (X 0) μ μ)
    (hMean : 0 < ∫ ω, X 0 ω ∂μ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ m : ℕ, ∀ n : ℕ,
      μ.real {ω | (m : ℝ) < terminalDrawdown X n ω} < ε := by
  letI : IsProbabilityMeasure μ := hIndep.isProbabilityMeasure
  have ht := tendsto_measureReal_compl_lowerBoundEvent_atTop
    X hX hInt hIndep hIdent hMean
  have hev : ∀ᶠ m : ℕ in atTop, μ.real (lowerBoundEvent X m)ᶜ < ε :=
    (tendsto_order.mp ht).2 ε hε
  obtain ⟨m, hm⟩ := Filter.eventually_atTop.mp hev
  refine ⟨m, fun n ↦ ?_⟩
  have hle := measure_terminalDrawdown_gt_le_compl_lowerBoundEvent
    X m n hIndep hIdent
  have hfinite : μ (lowerBoundEvent X m)ᶜ ≠ ⊤ := by
    apply ne_of_lt
    calc
      μ (lowerBoundEvent X m)ᶜ ≤ μ Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
      _ < ⊤ := ENNReal.one_lt_top
  have hreal : μ.real {ω | (m : ℝ) < terminalDrawdown X n ω} ≤
      μ.real (lowerBoundEvent X m)ᶜ := by
    rw [Measure.real_def, Measure.real_def]
    exact ENNReal.toReal_mono hfinite hle
  exact hreal.trans_lt (hm m le_rfl)

omit [MeasurableSpace Ω] in
lemma terminalDrawdown_nonneg (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    0 ≤ terminalDrawdown X n ω :=
  sub_nonneg.mpr (partialSum_le_runningMax X le_rfl ω)

/-- Uniform drawdown tightness makes the drawdown negligible on every positive
scale tending to infinity. -/
lemma tendstoInMeasure_terminalDrawdown_div
    (X : ℕ → Ω → ℝ)
    (hX : ∀ j, Measurable (X j))
    (hInt : Integrable (X 0) μ)
    (hIndep : ProbabilityTheory.iIndepFun X μ)
    (hIdent : ∀ j, ProbabilityTheory.IdentDistrib (X j) (X 0) μ μ)
    (hMean : 0 < ∫ ω, X 0 ω ∂μ)
    (b : ℕ → ℝ) (hbpos : ∀ᶠ n in atTop, 0 < b n)
    (hb : Tendsto b atTop atTop) :
    TendstoInMeasure μ (fun n ω ↦ terminalDrawdown X n ω / b n) atTop 0 := by
  letI : IsProbabilityMeasure μ := hIndep.isProbabilityMeasure
  rw [tendstoInMeasure_iff_measureReal_norm]
  intro δ hδ
  refine tendsto_order.mpr ⟨?_, ?_⟩
  · intro a ha
    exact Filter.Eventually.of_forall fun n ↦ ha.trans_le ENNReal.toReal_nonneg
  · intro ε hε
    obtain ⟨m, hm⟩ := exists_uniform_terminalDrawdown_tail_lt
      X hX hInt hIndep hIdent hMean hε
    have hscaleTop : Tendsto (fun n ↦ δ * b n) atTop atTop :=
      hb.const_mul_atTop hδ
    have hscale : ∀ᶠ n : ℕ in atTop, (m : ℝ) < δ * b n := by
      filter_upwards [tendsto_atTop.mp hscaleTop ((m : ℝ) + 1)] with n hn
      linarith
    filter_upwards [hscale, hbpos] with n hmn hbn
    have hsubset :
        {ω | δ ≤ ‖terminalDrawdown X n ω / b n - (0 : Ω → ℝ) ω‖} ⊆
          {ω | (m : ℝ) < terminalDrawdown X n ω} := by
      intro ω hω
      have hD := terminalDrawdown_nonneg X n ω
      have hdiv : 0 ≤ terminalDrawdown X n ω / b n :=
        div_nonneg hD hbn.le
      have hratio : δ ≤ terminalDrawdown X n ω / b n := by
        simpa only [Set.mem_setOf_eq, Pi.zero_apply, sub_zero, Real.norm_eq_abs,
          abs_of_nonneg hdiv] using hω
      exact hmn.trans_le ((le_div_iff₀ hbn).mp hratio)
    have hle :
        μ {ω | δ ≤ ‖terminalDrawdown X n ω / b n - (0 : Ω → ℝ) ω‖} ≤
          μ {ω | (m : ℝ) < terminalDrawdown X n ω} :=
      measure_mono hsubset
    have hfinite : μ {ω | (m : ℝ) < terminalDrawdown X n ω} ≠ ⊤ := by
      apply ne_of_lt
      calc
        μ {ω | (m : ℝ) < terminalDrawdown X n ω} ≤ μ Set.univ :=
          measure_mono (Set.subset_univ _)
        _ = 1 := measure_univ
        _ < ⊤ := ENNReal.one_lt_top
    have hreal :
        μ.real {ω | δ ≤ ‖terminalDrawdown X n ω / b n - (0 : Ω → ℝ) ω‖} ≤
          μ.real {ω | (m : ℝ) < terminalDrawdown X n ω} := by
      rw [Measure.real_def, Measure.real_def]
      exact ENNReal.toReal_mono hfinite hle
    exact hreal.trans_lt (hm n)

/-- The centered running maximum has the same central-limit scaling as the
terminal partial sum. The limit is expressed on the natural variance scale;
standardization is a deterministic rescaling of this statement. -/
lemma tendstoInDistribution_inv_sqrt_mul_runningMax_sub
    {Ω' : Type*} [MeasurableSpace Ω']
    {μ : Measure Ω} {μ' : Measure Ω'}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    (X : ℕ → Ω → ℝ) (Y : Ω' → ℝ)
    (hY : ProbabilityTheory.HasLaw Y
      (ProbabilityTheory.gaussianReal 0
        (ProbabilityTheory.variance (X 0) μ).toNNReal) μ')
    (hX : ∀ j, Measurable (X j))
    (hLp : MemLp (X 0) 2 μ)
    (hIndep : ProbabilityTheory.iIndepFun X μ)
    (hIdent : ∀ j, ProbabilityTheory.IdentDistrib (X j) (X 0) μ μ)
    (hMean : 0 < ∫ ω, X 0 ω ∂μ) :
    TendstoInDistribution
      (fun (n : ℕ) ω ↦ (Real.sqrt (n : ℝ))⁻¹ *
        (runningMax X n ω - (n : ℝ) * ∫ x, X 0 x ∂μ))
      atTop Y (fun _ ↦ μ) μ' := by
  have hsum :=
    ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum_sub
      hY hLp hIndep hIdent
  have hsqrt_pos : ∀ᶠ n : ℕ in atTop, 0 < Real.sqrt (n : ℝ) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    exact Real.sqrt_pos.2 (Nat.cast_pos.mpr (Nat.zero_lt_of_lt hn))
  have hsqrt_top :
      Tendsto (fun n : ℕ ↦ Real.sqrt (n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hdraw := tendstoInMeasure_terminalDrawdown_div
    X hX (hLp.integrable (by norm_num)) hIndep hIdent hMean
      (fun n ↦ Real.sqrt (n : ℝ)) hsqrt_pos hsqrt_top
  have hadd := hsum.add_of_tendstoInMeasure_const (c := (0 : ℝ)) hdraw fun n ↦
    ((measurable_terminalDrawdown X hX n).div_const _).aemeasurable
  apply hadd.congr
  · intro n
    exact Filter.Eventually.of_forall fun ω ↦ by
      simp only [Pi.add_apply, terminalDrawdown, partialSum, div_eq_mul_inv]
      ring
  · exact Filter.Eventually.of_forall fun ω ↦ by simp

/-- Standard-Gaussian form of the positive-drift running-maximum CLT. -/
lemma tendstoInDistribution_runningMax_standardGaussian
    {Ω' : Type*} [MeasurableSpace Ω']
    {μ : Measure Ω} {μ' : Measure Ω'}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    (X : ℕ → Ω → ℝ) (Z : Ω' → ℝ)
    (hZ : ProbabilityTheory.HasLaw Z
      (ProbabilityTheory.gaussianReal 0 1) μ')
    (hX : ∀ j, Measurable (X j))
    (hLp : MemLp (X 0) 2 μ)
    (hIndep : ProbabilityTheory.iIndepFun X μ)
    (hIdent : ∀ j, ProbabilityTheory.IdentDistrib (X j) (X 0) μ μ)
    (hMean : 0 < ∫ ω, X 0 ω ∂μ)
    (σ : ℝ) (hσ : 0 < σ)
    (hVar : ProbabilityTheory.variance (X 0) μ = σ ^ 2) :
    TendstoInDistribution
      (fun (n : ℕ) ω ↦ (σ * Real.sqrt (n : ℝ))⁻¹ *
        (runningMax X n ω - (n : ℝ) * ∫ x, X 0 x ∂μ))
      atTop Z (fun _ ↦ μ) μ' := by
  have hσZ : ProbabilityTheory.HasLaw (fun ω ↦ σ * Z ω)
      (ProbabilityTheory.gaussianReal 0
        (ProbabilityTheory.variance (X 0) μ).toNNReal) μ' := by
    rw [hVar]
    simpa [Real.toNNReal_of_nonneg (sq_nonneg σ)] using
      (ProbabilityTheory.gaussianReal_const_mul hZ σ)
  have hraw := tendstoInDistribution_inv_sqrt_mul_runningMax_sub
    X (fun ω ↦ σ * Z ω) hσZ hX hLp hIndep hIdent hMean
  have hscaled := hraw.continuous_comp (continuous_id.div_const σ)
  apply hscaled.congr
  · intro n
    exact Filter.Eventually.of_forall fun ω ↦ by
      simp only [Function.comp_apply, id_eq]
      rw [div_eq_mul_inv, mul_inv_rev]
      ring
  · exact Filter.Eventually.of_forall fun ω ↦ by
      simp [Function.comp_apply, hσ.ne']

/-- The strict lower tail of a translated standard Gaussian agrees with the
standard Gaussian CDF at the translation parameter. -/
lemma gaussianReal_sub_const_Iio_zero_real_eq_cdf (c : ℝ) :
    (ProbabilityTheory.gaussianReal (-c) 1).real (Set.Iio 0) =
      ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) c := by
  rw [ProbabilityTheory.cdf_eq_real]
  calc
    (ProbabilityTheory.gaussianReal (-c) 1).real (Set.Iio 0) =
        (ProbabilityTheory.gaussianReal 0 1).real (Set.Iio c) := by
      rw [Measure.real_def, Measure.real_def]
      have hmap := ProbabilityTheory.gaussianReal_map_sub_const
        (μ := (0 : ℝ)) (v := (1 : NNReal)) c
      simp only [zero_sub] at hmap
      rw [← hmap]
      rw [Measure.map_apply
        (show Measurable (fun x : ℝ ↦ x - c) by fun_prop) measurableSet_Iio]
      congr 2
      ext x
      simp
    _ = (ProbabilityTheory.gaussianReal 0 1).real (Set.Iic c) := by
      rw [Measure.real_def, Measure.real_def]
      haveI : NullSingletonClass (ProbabilityTheory.gaussianReal 0 1) :=
        ProbabilityTheory.nullSingletonClass_gaussianReal (by norm_num)
      exact congrArg ENNReal.toReal (measure_congr Iio_ae_eq_Iic)

/-- Sequence-indexed positive-drift first-passage profile. If the observation
times diverge and the centered moving levels converge on the CLT scale, then
the survival probabilities converge to the standard Gaussian CDF. -/
lemma tendsto_measureReal_firstPassageTime_gt
    {Ω' : Type*} [MeasurableSpace Ω']
    {μ : Measure Ω} {μ' : Measure Ω'}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    (X : ℕ → Ω → ℝ) (Z : Ω' → ℝ)
    (hZ : ProbabilityTheory.HasLaw Z
      (ProbabilityTheory.gaussianReal 0 1) μ')
    (hX : ∀ j, Measurable (X j))
    (hLp : MemLp (X 0) 2 μ)
    (hIndep : ProbabilityTheory.iIndepFun X μ)
    (hIdent : ∀ j, ProbabilityTheory.IdentDistrib (X j) (X 0) μ μ)
    (hMean : 0 < ∫ ω, X 0 ω ∂μ)
    (σ : ℝ) (hσ : 0 < σ)
    (hVar : ProbabilityTheory.variance (X 0) μ = σ ^ 2)
    (n : ℕ → ℕ) (u : ℕ → ℝ) (c : ℝ)
    (hn_pos : ∀ᶠ r in atTop, 1 ≤ n r)
    (hn_top : Tendsto n atTop atTop)
    (hcenter : Tendsto
      (fun r ↦ (u r - (n r : ℝ) * ∫ x, X 0 x ∂μ) /
        (σ * Real.sqrt (n r : ℝ)))
      atTop (nhds c)) :
    Tendsto
      (fun r ↦ μ.real
        {ω | (n r : WithTop ℕ) < firstPassageTime X (u r) ω})
      atTop (nhds (ProbabilityTheory.cdf
        (ProbabilityTheory.gaussianReal 0 1) c)) := by
  have hmax := tendstoInDistribution_runningMax_standardGaussian
    X Z hZ hX hLp hIndep hIdent hMean σ hσ hVar
  have hmax_sub :
      TendstoInDistribution
        (fun r ω ↦ (σ * Real.sqrt (n r : ℝ))⁻¹ *
          (runningMax X (n r) ω -
            (n r : ℝ) * ∫ x, X 0 x ∂μ))
        atTop Z (fun _ ↦ μ) μ' := by
    refine ⟨fun r ↦ hmax.forall_aemeasurable (n r),
      hmax.aemeasurable_limit, ?_⟩
    exact hmax.tendsto.comp hn_top
  have hcenter_measure :
      TendstoInMeasure μ
        (fun r (_ : Ω) ↦
          (u r - (n r : ℝ) * ∫ x, X 0 x ∂μ) /
            (σ * Real.sqrt (n r : ℝ)))
        atTop (fun _ ↦ c) := by
    apply tendstoInMeasure_of_tendsto_ae
    · intro r
      exact measurable_const.aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun _ ↦ hcenter
  have hshift :=
    hmax_sub.continuous_comp_prodMk_of_tendstoInMeasure_const
      (g := fun p : ℝ × ℝ ↦ p.1 - p.2) (by fun_prop) hcenter_measure
        (fun _ ↦ measurable_const.aemeasurable)
  have hshiftLaw := ProbabilityTheory.gaussianReal_sub_const hZ c
  have hfront :
      (μ'.map (fun ω ↦ Z ω - c)) (frontier (Set.Iio 0)) = 0 := by
    rw [hshiftLaw.map_eq]
    haveI : NullSingletonClass
        (ProbabilityTheory.gaussianReal (0 - c) 1) :=
      ProbabilityTheory.nullSingletonClass_gaussianReal (by norm_num)
    rw [frontier_Iio]
    exact measure_singleton 0
  have hport :=
    ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
      hshift.tendsto hfront
  have hlimit_ne_top :
      (μ'.map (fun ω ↦ Z ω - c)) (Set.Iio 0) ≠ ⊤ :=
    measure_ne_top _ _
  have hreal := (ENNReal.tendsto_toReal hlimit_ne_top).comp hport
  change Tendsto
    (fun r ↦ (μ.map (fun ω ↦
      (σ * Real.sqrt (n r : ℝ))⁻¹ *
          (runningMax X (n r) ω -
            (n r : ℝ) * ∫ x, X 0 x ∂μ) -
        (u r - (n r : ℝ) * ∫ x, X 0 x ∂μ) /
          (σ * Real.sqrt (n r : ℝ)))).real (Set.Iio 0))
    atTop (nhds ((μ'.map (fun ω ↦ Z ω - c)).real (Set.Iio 0))) at hreal
  have hsource : ∀ᶠ r in atTop,
      (μ.map (fun ω ↦
        (σ * Real.sqrt (n r : ℝ))⁻¹ *
            (runningMax X (n r) ω -
              (n r : ℝ) * ∫ x, X 0 x ∂μ) -
          (u r - (n r : ℝ) * ∫ x, X 0 x ∂μ) /
            (σ * Real.sqrt (n r : ℝ)))).real (Set.Iio 0) =
        μ.real {ω | (n r : WithTop ℕ) < firstPassageTime X (u r) ω} := by
    filter_upwards [hn_pos] with r hnr
    rw [Measure.real_def, Measure.real_def,
      Measure.map_apply_of_aemeasurable
        (hshift.forall_aemeasurable r) measurableSet_Iio]
    congr 2
    rw [firstPassageTime_gt_set_eq]
    ext ω
    simp only [Set.mem_preimage, Set.mem_Iio, Set.mem_setOf_eq]
    have hn_nat : 0 < n r := Nat.zero_lt_of_lt hnr
    have hden : 0 < σ * Real.sqrt (n r : ℝ) :=
      mul_pos hσ (Real.sqrt_pos.2 (Nat.cast_pos.mpr hn_nat))
    have heq :
        (σ * Real.sqrt (n r : ℝ))⁻¹ *
              (runningMax X (n r) ω -
                (n r : ℝ) * ∫ x, X 0 x ∂μ) -
            (u r - (n r : ℝ) * ∫ x, X 0 x ∂μ) /
              (σ * Real.sqrt (n r : ℝ)) =
          (runningMax X (n r) ω - u r) /
            (σ * Real.sqrt (n r : ℝ)) := by
      field_simp
      ring
    rw [heq, div_lt_iff₀ hden, zero_mul, sub_neg]
  have htarget :
      (μ'.map (fun ω ↦ Z ω - c)).real (Set.Iio 0) =
        ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) c := by
    rw [hshiftLaw.map_eq]
    simpa only [zero_sub] using gaussianReal_sub_const_Iio_zero_real_eq_cdf c
  have hreal' := hreal.congr' hsource
  simpa only [htarget] using hreal'

/-- Real argument whose natural-valued floor is the canonical observation
time for the first-passage profile. We write `μ * sqrt μ` for `μ^(3/2)`. -/
noncomputable def canonicalTimeArgument
    (μ σ a : ℝ) (L q : ℕ → ℝ) (r : ℕ) : ℝ :=
  L r / μ + (a * σ / (μ * Real.sqrt μ)) * Real.sqrt (L r) + q r

/-- Canonical natural-valued observation time, with negative arguments
clamped to zero by `Nat.floor`. -/
noncomputable def canonicalTime
    (μ σ a : ℝ) (L q : ℕ → ℝ) (r : ℕ) : ℕ :=
  ⌊canonicalTimeArgument μ σ a L q r⌋₊

/-- Paper-facing time convention in which a perturbation is added after the
canonical unperturbed time has already been floored. -/
noncomputable def postFloorTime
    (μ σ a : ℝ) (L v : ℕ → ℝ) (r : ℕ) : ℕ :=
  ⌊(canonicalTime μ σ a L 0 r : ℝ) + v r⌋₊

/-- Error bounds for the natural-valued floor of a nonnegative real number. -/
lemma natFloor_sub_bounds (x : ℝ) (hx : 0 ≤ x) :
    -1 < (⌊x⌋₊ : ℝ) - x ∧ (⌊x⌋₊ : ℝ) - x ≤ 0 := by
  constructor
  · have h := Nat.sub_one_lt_floor x
    linarith
  · exact sub_nonpos.mpr (Nat.floor_le hx)

/-- Flooring after first flooring a nonnegative base can lower the one-step
floor by at most one. -/
lemma natFloor_add_floor_bounds (x v : ℝ) (hx : 0 ≤ x) :
    ⌊(⌊x⌋₊ : ℝ) + v⌋₊ ≤ ⌊x + v⌋₊ ∧
      ⌊x + v⌋₊ ≤ ⌊(⌊x⌋₊ : ℝ) + v⌋₊ + 1 := by
  constructor
  · apply Nat.floor_mono
    simpa [add_comm] using add_le_add_right (Nat.floor_le hx) v
  · by_cases hxv : 0 ≤ x + v
    · have hx_lt : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
      have hy_lt :
          (⌊x⌋₊ : ℝ) + v <
            (⌊(⌊x⌋₊ : ℝ) + v⌋₊ : ℝ) + 1 :=
        Nat.lt_floor_add_one _
      have hsum :
          x + v < (⌊(⌊x⌋₊ : ℝ) + v⌋₊ : ℝ) + 2 := by
        linarith
      have hfloor : ⌊x + v⌋₊ < ⌊(⌊x⌋₊ : ℝ) + v⌋₊ + 2 := by
        rw [Nat.floor_lt hxv]
        exact_mod_cast hsum
      omega
    · have hzero : ⌊x + v⌋₊ = 0 := by
        rw [Nat.floor_eq_zero]
        linarith
      omega

/-- Natural-valued flooring preserves divergence to positive infinity. -/
lemma tendsto_natFloor_atTop {x : ℕ → ℝ}
    (hx : Tendsto x atTop atTop) :
    Tendsto (fun r ↦ ⌊x r⌋₊) atTop atTop := by
  rw [tendsto_atTop]
  intro b
  filter_upwards [tendsto_atTop.mp hx (b : ℝ)] with r hr
  exact Nat.le_floor hr

/-- A natural-floor error is negligible relative to any positive scale tending
to infinity. -/
lemma tendsto_natFloor_sub_div {x L : ℕ → ℝ}
    (hx_nonneg : ∀ᶠ r in atTop, 0 ≤ x r)
    (hL : Tendsto L atTop atTop) :
    Tendsto (fun r ↦ ((⌊x r⌋₊ : ℝ) - x r) / L r)
      atTop (nhds 0) := by
  have hLpos : ∀ᶠ r in atTop, 0 < L r := hL.eventually_gt_atTop 0
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (hL.const_div_atTop (-1)) tendsto_const_nhds
  · filter_upwards [hx_nonneg, hLpos] with r hxr hLr
    exact (div_le_div_iff_of_pos_right hLr).2
      (natFloor_sub_bounds (x r) hxr).1.le
  · filter_upwards [hx_nonneg, hLpos] with r hxr hLr
    rw [show (0 : ℝ) = 0 / L r by simp]
    exact (div_le_div_iff_of_pos_right hLr).2
      (natFloor_sub_bounds (x r) hxr).2

/-- A bounded natural-floor error does not change a ratio limit on a positive
diverging scale. -/
lemma tendsto_natFloor_div {x L : ℕ → ℝ} {a : ℝ}
    (hx_nonneg : ∀ᶠ r in atTop, 0 ≤ x r)
    (hL : Tendsto L atTop atTop)
    (hratio : Tendsto (fun r ↦ x r / L r) atTop (nhds a)) :
    Tendsto (fun r ↦ (⌊x r⌋₊ : ℝ) / L r) atTop (nhds a) := by
  have herr := tendsto_natFloor_sub_div hx_nonneg hL
  convert hratio.add herr using 1
  · ext r
    ring
  · simp

/-- The pre-floor canonical observation time is asymptotic to `L / μ`. -/
lemma tendsto_canonicalTimeArgument_div
    {L q : ℕ → ℝ} {μ σ a : ℝ}
    (hL : Tendsto L atTop atTop)
    (hq : Tendsto (fun r ↦ q r / Real.sqrt (L r)) atTop (nhds 0)) :
    Tendsto (fun r ↦ canonicalTimeArgument μ σ a L q r / L r)
      atTop (nhds (1 / μ)) := by
  have hLpos : ∀ᶠ r in atTop, 0 < L r := hL.eventually_gt_atTop 0
  have hsqrt : Tendsto (fun r ↦ Real.sqrt (L r)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hL
  have hmain :
      Tendsto (fun r ↦ 1 / μ +
          (a * σ / (μ * Real.sqrt μ)) / Real.sqrt (L r) +
          (q r / Real.sqrt (L r)) / Real.sqrt (L r))
        atTop (nhds (1 / μ)) := by
    simpa using (tendsto_const_nhds.add
      (hsqrt.const_div_atTop (a * σ / (μ * Real.sqrt μ)))).add
        (hq.div_atTop hsqrt)
  apply hmain.congr'
  filter_upwards [hLpos] with r hLr
  symm
  unfold canonicalTimeArgument
  let s := Real.sqrt (L r)
  have hs_pos : 0 < s := Real.sqrt_pos.2 hLr
  have hsq : s ^ 2 = L r := Real.sq_sqrt hLr.le
  have hL_eq : L r = s * s := by nlinarith
  change (L r / μ + a * σ / (μ * √μ) * s + q r) / L r =
    1 / μ + a * σ / (μ * √μ) / s + q r / s / s
  calc
    (L r / μ + a * σ / (μ * √μ) * s + q r) / L r =
        (L r / μ) / L r +
          (a * σ / (μ * √μ) * s) / L r + q r / L r := by ring
    _ = 1 / μ +
          (a * σ / (μ * √μ)) / s +
          (q r / s) / s := by
      rw [hL_eq]
      field_simp [hs_pos.ne']

/-- At positive drift, the pre-floor canonical observation time diverges. -/
lemma tendsto_canonicalTimeArgument_atTop
    {L q : ℕ → ℝ} {μ σ a : ℝ}
    (hμ : 0 < μ)
    (hL : Tendsto L atTop atTop)
    (hq : Tendsto (fun r ↦ q r / Real.sqrt (L r)) atTop (nhds 0)) :
    Tendsto (canonicalTimeArgument μ σ a L q) atTop atTop := by
  have hratio := tendsto_canonicalTimeArgument_div
    (μ := μ) (σ := σ) (a := a) hL hq
  have hprod := hratio.pos_mul_atTop (one_div_pos.mpr hμ) hL
  apply hprod.congr'
  filter_upwards [hL.eventually_gt_atTop 0] with r hLr
  field_simp [hLr.ne']

/-- At positive drift, the natural-valued canonical observation time
diverges. -/
lemma tendsto_canonicalTime_atTop
    {L q : ℕ → ℝ} {μ σ a : ℝ}
    (hμ : 0 < μ)
    (hL : Tendsto L atTop atTop)
    (hq : Tendsto (fun r ↦ q r / Real.sqrt (L r)) atTop (nhds 0)) :
    Tendsto (canonicalTime μ σ a L q) atTop atTop := by
  rw [show canonicalTime μ σ a L q =
      fun r ↦ ⌊canonicalTimeArgument μ σ a L q r⌋₊ by rfl]
  exact tendsto_natFloor_atTop
    (tendsto_canonicalTimeArgument_atTop hμ hL hq)

/-- The natural-valued canonical observation time is asymptotic to `L / μ`. -/
lemma tendsto_canonicalTime_div
    {L q : ℕ → ℝ} {μ σ a : ℝ}
    (hμ : 0 < μ)
    (hL : Tendsto L atTop atTop)
    (hq : Tendsto (fun r ↦ q r / Real.sqrt (L r)) atTop (nhds 0)) :
    Tendsto (fun r ↦ (canonicalTime μ σ a L q r : ℝ) / L r)
      atTop (nhds (1 / μ)) := by
  have harg := tendsto_canonicalTimeArgument_atTop
    (σ := σ) (a := a) hμ hL hq
  have harg_nonneg : ∀ᶠ r in atTop,
      0 ≤ canonicalTimeArgument μ σ a L q r :=
    (harg.eventually_gt_atTop 0).mono fun _ h ↦ h.le
  simpa [canonicalTime] using tendsto_natFloor_div harg_nonneg hL
    (tendsto_canonicalTimeArgument_div
      (μ := μ) (σ := σ) (a := a) hL hq)

/-- Square-root form of the canonical time asymptotic. -/
lemma tendsto_sqrt_canonicalTime_div_sqrt
    {L q : ℕ → ℝ} {μ σ a : ℝ}
    (hμ : 0 < μ)
    (hL : Tendsto L atTop atTop)
    (hq : Tendsto (fun r ↦ q r / Real.sqrt (L r)) atTop (nhds 0)) :
    Tendsto (fun r ↦ Real.sqrt (canonicalTime μ σ a L q r : ℝ) /
      Real.sqrt (L r)) atTop (nhds (1 / Real.sqrt μ)) := by
  have hratio := tendsto_canonicalTime_div
    (σ := σ) (a := a) hμ hL hq
  have hsqrt := (Real.continuous_sqrt.tendsto (1 / μ)).comp hratio
  simpa only [Function.comp_def, Real.sqrt_div (Nat.cast_nonneg _),
    one_div, Real.sqrt_inv] using hsqrt

/-- Centered canonical levels on the `sqrt L` scale, before changing the
denominator from `sqrt L` to `sqrt n`. -/
lemma tendsto_canonicalTime_centered_div_sqrt
    {L Ltilde q : ℕ → ℝ} {μ σ a : ℝ}
    (hμ : 0 < μ)
    (hL : Tendsto L atTop atTop)
    (hq : Tendsto (fun r ↦ q r / Real.sqrt (L r)) atTop (nhds 0))
    (hlevel : Tendsto
      (fun r ↦ (Ltilde r - L r) / Real.sqrt (L r))
      atTop (nhds 0)) :
    Tendsto
      (fun r ↦ (Ltilde r - μ * (canonicalTime μ σ a L q r : ℝ)) /
        Real.sqrt (L r))
      atTop (nhds (-a * σ / Real.sqrt μ)) := by
  have harg := tendsto_canonicalTimeArgument_atTop
    (σ := σ) (a := a) hμ hL hq
  have harg_nonneg : ∀ᶠ r in atTop,
      0 ≤ canonicalTimeArgument μ σ a L q r :=
    (harg.eventually_gt_atTop 0).mono fun _ h ↦ h.le
  have hsqrt : Tendsto (fun r ↦ Real.sqrt (L r)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hL
  have herr :
      Tendsto
        (fun r ↦ ((canonicalTime μ σ a L q r : ℝ) -
          canonicalTimeArgument μ σ a L q r) / Real.sqrt (L r))
        atTop (nhds 0) := by
    simpa [canonicalTime] using
      tendsto_natFloor_sub_div harg_nonneg hsqrt
  have hconst : Tendsto (fun _ : ℕ ↦ a * σ / Real.sqrt μ) atTop
      (nhds (a * σ / Real.sqrt μ)) := tendsto_const_nhds
  have hmain :
      Tendsto
        (fun r ↦
          (Ltilde r - L r) / Real.sqrt (L r) -
            a * σ / Real.sqrt μ -
            μ * (q r / Real.sqrt (L r)) -
            μ * (((canonicalTime μ σ a L q r : ℝ) -
              canonicalTimeArgument μ σ a L q r) / Real.sqrt (L r)))
        atTop (nhds (-(a * σ / Real.sqrt μ))) := by
    simpa only [sub_zero, mul_zero, zero_sub] using
      (((hlevel.sub hconst).sub (hq.const_mul μ)).sub (herr.const_mul μ))
  have hactual :
      Tendsto
        (fun r ↦ (Ltilde r - μ * (canonicalTime μ σ a L q r : ℝ)) /
          Real.sqrt (L r))
        atTop (nhds (-(a * σ / Real.sqrt μ))) := by
    apply hmain.congr'
    filter_upwards [hL.eventually_gt_atTop 0] with r hLr
    symm
    unfold canonicalTimeArgument
    have hsqrtL_ne : Real.sqrt (L r) ≠ 0 := (Real.sqrt_pos.2 hLr).ne'
    have hsqrtμ_ne : Real.sqrt μ ≠ 0 := (Real.sqrt_pos.2 hμ).ne'
    field_simp [hμ.ne', hsqrtL_ne, hsqrtμ_ne]
    ring
  simpa only [neg_div, neg_mul] using hactual

/-- Canonical-floor asymptotic in the normalization required by the moving
first-passage profile. -/
lemma tendsto_canonicalTime_centered
    {L Ltilde q : ℕ → ℝ} {μ σ a : ℝ}
    (hμ : 0 < μ) (hσ : 0 < σ)
    (hL : Tendsto L atTop atTop)
    (hq : Tendsto (fun r ↦ q r / Real.sqrt (L r)) atTop (nhds 0))
    (hlevel : Tendsto
      (fun r ↦ (Ltilde r - L r) / Real.sqrt (L r))
      atTop (nhds 0)) :
    Tendsto
      (fun r ↦ (Ltilde r - μ * (canonicalTime μ σ a L q r : ℝ)) /
        (σ * Real.sqrt (canonicalTime μ σ a L q r : ℝ)))
      atTop (nhds (-a)) := by
  have hnum := tendsto_canonicalTime_centered_div_sqrt
    (σ := σ) (a := a) hμ hL hq hlevel
  have hsqrtRatio := tendsto_sqrt_canonicalTime_div_sqrt
    (σ := σ) (a := a) hμ hL hq
  have hden := hsqrtRatio.const_mul σ
  have hsqrtμ_ne : Real.sqrt μ ≠ 0 := (Real.sqrt_pos.2 hμ).ne'
  have hden_ne : σ * (1 / Real.sqrt μ) ≠ 0 :=
    mul_ne_zero hσ.ne' (one_div_ne_zero hsqrtμ_ne)
  have hquot := hnum.div hden hden_ne
  have hactual :
      Tendsto
        (fun r ↦ (Ltilde r - μ * (canonicalTime μ σ a L q r : ℝ)) /
          (σ * Real.sqrt (canonicalTime μ σ a L q r : ℝ)))
        atTop (nhds ((-a * σ / Real.sqrt μ) /
          (σ * (1 / Real.sqrt μ)))) := by
    apply hquot.congr'
    filter_upwards [hL.eventually_gt_atTop 0,
      (tendsto_canonicalTime_atTop
        (σ := σ) (a := a) hμ hL hq).eventually_gt_atTop 0]
      with r hLr hnr
    have hsqrtL_ne : Real.sqrt (L r) ≠ 0 := (Real.sqrt_pos.2 hLr).ne'
    have hsqrtn_ne : Real.sqrt (canonicalTime μ σ a L q r : ℝ) ≠ 0 :=
      (Real.sqrt_pos.2 (Nat.cast_pos.mpr hnr)).ne'
    change
      ((Ltilde r - μ * (canonicalTime μ σ a L q r : ℝ)) /
          Real.sqrt (L r)) /
          (σ * (Real.sqrt (canonicalTime μ σ a L q r : ℝ) /
            Real.sqrt (L r))) =
        (Ltilde r - μ * (canonicalTime μ σ a L q r : ℝ)) /
          (σ * Real.sqrt (canonicalTime μ σ a L q r : ℝ))
    field_simp [hσ.ne', hsqrtL_ne, hsqrtn_ne]
  convert hactual using 1
  field_simp [hσ.ne', hsqrtμ_ne]

/-- Moving-level and canonical-time first-passage profile. -/
lemma tendsto_measureReal_firstPassageTime_gt_canonicalTime
    {Ω' : Type*} [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'}
    [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (X : ℕ → Ω → ℝ) (Z : Ω' → ℝ)
    (hZ : ProbabilityTheory.HasLaw Z
      (ProbabilityTheory.gaussianReal 0 1) P')
    (hX : ∀ j, Measurable (X j))
    (hLp : MemLp (X 0) 2 P)
    (hIndep : ProbabilityTheory.iIndepFun X P)
    (hIdent : ∀ j, ProbabilityTheory.IdentDistrib (X j) (X 0) P P)
    (hMean : 0 < ∫ ω, X 0 ω ∂P)
    (σ : ℝ) (hσ : 0 < σ)
    (hVar : ProbabilityTheory.variance (X 0) P = σ ^ 2)
    (L Ltilde q : ℕ → ℝ) (a : ℝ)
    (hL : Tendsto L atTop atTop)
    (hq : Tendsto (fun r ↦ q r / Real.sqrt (L r)) atTop (nhds 0))
    (hlevel : Tendsto
      (fun r ↦ (Ltilde r - L r) / Real.sqrt (L r))
      atTop (nhds 0)) :
    Tendsto
      (fun r ↦ P.real {ω |
        (canonicalTime (∫ x, X 0 x ∂P) σ a L q r : WithTop ℕ) <
          firstPassageTime X (Ltilde r) ω})
      atTop (nhds (ProbabilityTheory.cdf
        (ProbabilityTheory.gaussianReal 0 1) (-a))) := by
  have hn_top := tendsto_canonicalTime_atTop
    (σ := σ) (a := a) hMean hL hq
  have hn_pos : ∀ᶠ r in atTop,
      1 ≤ canonicalTime (∫ x, X 0 x ∂P) σ a L q r := by
    filter_upwards [hn_top.eventually_gt_atTop 0] with r hr
    omega
  apply tendsto_measureReal_firstPassageTime_gt
    (X := X) (Z := Z) hZ hX hLp hIndep hIdent hMean σ hσ hVar
      (n := canonicalTime (∫ x, X 0 x ∂P) σ a L q)
      (u := Ltilde) (c := -a) hn_pos hn_top
  simpa [mul_comm] using
    (tendsto_canonicalTime_centered (σ := σ) (a := a)
      hMean hσ hL hq hlevel)

/-- Along a diverging positive-drift scale, the post-floor time is eventually
at most the one-floor perturbed time and at most one below it. -/
lemma eventually_postFloorTime_bounds
    {L v : ℕ → ℝ} {μ σ a : ℝ}
    (hμ : 0 < μ) (hL : Tendsto L atTop atTop) :
    ∀ᶠ r in atTop,
      postFloorTime μ σ a L v r ≤ canonicalTime μ σ a L v r ∧
        canonicalTime μ σ a L v r ≤ postFloorTime μ σ a L v r + 1 := by
  have hq0 : Tendsto (fun r ↦ (0 : ℝ) / Real.sqrt (L r))
      atTop (nhds 0) := by simp
  have harg := tendsto_canonicalTimeArgument_atTop
    (σ := σ) (a := a) hμ hL hq0
  filter_upwards [(harg.eventually_gt_atTop 0).mono fun _ h ↦ h.le] with r hr
  simpa [postFloorTime, canonicalTime, canonicalTimeArgument] using
    natFloor_add_floor_bounds
      (canonicalTimeArgument μ σ a L 0 r) (v r) hr

/-- The post-floor observation time diverges under a `sqrt L`-negligible time
perturbation. -/
lemma tendsto_postFloorTime_atTop
    {L v : ℕ → ℝ} {μ σ a : ℝ}
    (hμ : 0 < μ) (hL : Tendsto L atTop atTop)
    (hv : Tendsto (fun r ↦ v r / Real.sqrt (L r)) atTop (nhds 0)) :
    Tendsto (postFloorTime μ σ a L v) atTop atTop := by
  have hcanon := tendsto_canonicalTime_atTop
    (σ := σ) (a := a) hμ hL hv
  rw [tendsto_atTop]
  intro b
  filter_upwards [eventually_postFloorTime_bounds
      (v := v) (σ := σ) (a := a) hμ hL,
    tendsto_atTop.mp hcanon (b + 1)] with r hr hbr
  omega

/-- Natural sequences separated by an eventual ordered gap of at most one
have ratio tending to one when the lower sequence diverges. -/
lemma tendsto_natCast_div_of_unit_gap
    {m n : ℕ → ℕ}
    (hm : Tendsto m atTop atTop)
    (hgap : ∀ᶠ r in atTop, m r ≤ n r ∧ n r ≤ m r + 1) :
    Tendsto (fun r ↦ (n r : ℝ) / (m r : ℝ)) atTop (nhds 1) := by
  have hmR : Tendsto (fun r ↦ (m r : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hm
  have hupper :
      Tendsto (fun r ↦ 1 + 1 / (m r : ℝ)) atTop (nhds 1) := by
    simpa using tendsto_const_nhds.add (hmR.const_div_atTop 1)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hupper
  · filter_upwards [hgap, hm.eventually_gt_atTop 0] with r hr hmr
    rw [le_div_iff₀ (Nat.cast_pos.mpr hmr)]
    simpa using (Nat.cast_le.mpr hr.1 : (m r : ℝ) ≤ (n r : ℝ))
  · filter_upwards [hgap, hm.eventually_gt_atTop 0] with r hr hmr
    rw [div_le_iff₀ (Nat.cast_pos.mpr hmr)]
    have hcast : (n r : ℝ) ≤ (m r : ℝ) + 1 := by exact_mod_cast hr.2
    calc
      (n r : ℝ) ≤ (m r : ℝ) + 1 := hcast
      _ = (1 + 1 / (m r : ℝ)) * (m r : ℝ) := by
        field_simp [Nat.cast_ne_zero.mpr hmr.ne']

/-- Square-root ratio form of `tendsto_natCast_div_of_unit_gap`. -/
lemma tendsto_sqrt_natCast_div_of_unit_gap
    {m n : ℕ → ℕ}
    (hm : Tendsto m atTop atTop)
    (hgap : ∀ᶠ r in atTop, m r ≤ n r ∧ n r ≤ m r + 1) :
    Tendsto (fun r ↦ Real.sqrt (n r : ℝ) / Real.sqrt (m r : ℝ))
      atTop (nhds 1) := by
  have hratio := tendsto_natCast_div_of_unit_gap hm hgap
  have hsqrt := (Real.continuous_sqrt.tendsto 1).comp hratio
  simpa only [Function.comp_def, Real.sqrt_div (Nat.cast_nonneg _),
    Real.sqrt_one] using hsqrt

/-- An eventual ordered unit gap is negligible on the square-root scale of
the lower diverging sequence. -/
lemma tendsto_natCast_sub_div_sqrt_of_unit_gap
    {m n : ℕ → ℕ}
    (hm : Tendsto m atTop atTop)
    (hgap : ∀ᶠ r in atTop, m r ≤ n r ∧ n r ≤ m r + 1) :
    Tendsto (fun r ↦ ((n r : ℝ) - (m r : ℝ)) / Real.sqrt (m r : ℝ))
      atTop (nhds 0) := by
  have hmR : Tendsto (fun r ↦ (m r : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hm
  have hsqrtm : Tendsto (fun r ↦ Real.sqrt (m r : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hmR
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds (hsqrtm.const_div_atTop 1)
  · filter_upwards [hgap, hm.eventually_gt_atTop 0] with r hr hmr
    exact div_nonneg (sub_nonneg.mpr (Nat.cast_le.mpr hr.1))
      (Real.sqrt_nonneg _)
  · filter_upwards [hgap, hm.eventually_gt_atTop 0] with r hr hmr
    rw [div_le_div_iff_of_pos_right
      (Real.sqrt_pos.2 (Nat.cast_pos.mpr hmr))]
    have hcast : (n r : ℝ) ≤ (m r : ℝ) + 1 := by exact_mod_cast hr.2
    linarith

/-- The paper's post-floor time convention has the same centered asymptotic as
the corresponding one-floor canonical time. -/
lemma tendsto_postFloorTime_centered
    {L Ltilde v : ℕ → ℝ} {μ σ a : ℝ}
    (hμ : 0 < μ) (hσ : 0 < σ)
    (hL : Tendsto L atTop atTop)
    (hv : Tendsto (fun r ↦ v r / Real.sqrt (L r)) atTop (nhds 0))
    (hlevel : Tendsto
      (fun r ↦ (Ltilde r - L r) / Real.sqrt (L r))
      atTop (nhds 0)) :
    Tendsto
      (fun r ↦ (Ltilde r - μ * (postFloorTime μ σ a L v r : ℝ)) /
        (σ * Real.sqrt (postFloorTime μ σ a L v r : ℝ)))
      atTop (nhds (-a)) := by
  let m := postFloorTime μ σ a L v
  let n := canonicalTime μ σ a L v
  have hm : Tendsto m atTop atTop := by
    exact tendsto_postFloorTime_atTop (σ := σ) (a := a) hμ hL hv
  have hgap : ∀ᶠ r in atTop, m r ≤ n r ∧ n r ≤ m r + 1 := by
    exact eventually_postFloorTime_bounds
      (v := v) (σ := σ) (a := a) hμ hL
  have hcanon :
      Tendsto (fun r ↦ (Ltilde r - μ * (n r : ℝ)) /
        (σ * Real.sqrt (n r : ℝ))) atTop (nhds (-a)) := by
    exact tendsto_canonicalTime_centered hμ hσ hL hv hlevel
  have hsqrtRatio :
      Tendsto (fun r ↦ Real.sqrt (n r : ℝ) / Real.sqrt (m r : ℝ))
        atTop (nhds 1) :=
    tendsto_sqrt_natCast_div_of_unit_gap hm hgap
  have hgapNorm :
      Tendsto (fun r ↦ ((n r : ℝ) - (m r : ℝ)) / Real.sqrt (m r : ℝ))
        atTop (nhds 0) :=
    tendsto_natCast_sub_div_sqrt_of_unit_gap hm hgap
  have hmain :
      Tendsto
        (fun r ↦ ((Ltilde r - μ * (n r : ℝ)) /
              (σ * Real.sqrt (n r : ℝ))) *
            (Real.sqrt (n r : ℝ) / Real.sqrt (m r : ℝ)) +
          (μ / σ) * (((n r : ℝ) - (m r : ℝ)) /
            Real.sqrt (m r : ℝ)))
        atTop (nhds (-a)) := by
    simpa using hcanon.mul hsqrtRatio |>.add (hgapNorm.const_mul (μ / σ))
  change Tendsto
    (fun r ↦ (Ltilde r - μ * (m r : ℝ)) /
      (σ * Real.sqrt (m r : ℝ))) atTop (nhds (-a))
  apply hmain.congr'
  filter_upwards [hm.eventually_gt_atTop 0,
    (tendsto_canonicalTime_atTop
      (σ := σ) (a := a) hμ hL hv).eventually_gt_atTop 0]
    with r hmr hnr
  have hsqrtm_ne : Real.sqrt (m r : ℝ) ≠ 0 :=
    (Real.sqrt_pos.2 (Nat.cast_pos.mpr hmr)).ne'
  have hsqrtn_ne : Real.sqrt (n r : ℝ) ≠ 0 :=
    (Real.sqrt_pos.2 (Nat.cast_pos.mpr hnr)).ne'
  field_simp [hσ.ne', hsqrtm_ne, hsqrtn_ne]
  ring

/-- A fixed shift of a moving level is negligible after normalization by the
square root of a diverging reference level. -/
lemma tendsto_level_sub_const_div_sqrt
    (L Ltilde : ℕ → ℝ) (B : ℝ)
    (hL : Tendsto L atTop atTop)
    (hlevel : Tendsto
      (fun r ↦ (Ltilde r - L r) / Real.sqrt (L r))
      atTop (nhds 0)) :
    Tendsto
      (fun r ↦ ((Ltilde r - B) - L r) / Real.sqrt (L r))
      atTop (nhds 0) := by
  have hsqrt : Tendsto (fun r ↦ Real.sqrt (L r)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hL
  have h := hlevel.sub (hsqrt.const_div_atTop B)
  convert h using 1
  · funext r
    ring
  · norm_num

/-- The iterated square root is a diverging scale negligible compared with
the square root of the original diverging scale. -/
lemma tendsto_sqrt_sqrt_div_sqrt_of_tendsto_atTop
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop) :
    Tendsto (fun r ↦ Real.sqrt (Real.sqrt (L r)) / Real.sqrt (L r))
      atTop (nhds 0) := by
  have hBtop :
      Tendsto (fun r ↦ Real.sqrt (Real.sqrt (L r))) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (Real.tendsto_sqrt_atTop.comp hL)
  apply (hBtop.const_div_atTop 1).congr'
  filter_upwards [hL.eventually_gt_atTop 0] with r hr
  have hBpos : 0 < Real.sqrt (Real.sqrt (L r)) :=
    Real.sqrt_pos.2 (Real.sqrt_pos.2 hr)
  have hsquare :
      Real.sqrt (Real.sqrt (L r)) ^ 2 = Real.sqrt (L r) :=
    Real.sq_sqrt (Real.sqrt_nonneg _)
  calc
    1 / Real.sqrt (Real.sqrt (L r)) =
        Real.sqrt (Real.sqrt (L r)) /
          Real.sqrt (Real.sqrt (L r)) ^ 2 := by field_simp
    _ = Real.sqrt (Real.sqrt (L r)) / Real.sqrt (L r) := by rw [hsquare]

/-- First-passage profile for the paper's post-floor time perturbation
convention. -/
lemma tendsto_measureReal_firstPassageTime_gt_postFloorTime
    {Ω' : Type*} [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'}
    [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (X : ℕ → Ω → ℝ) (Z : Ω' → ℝ)
    (hZ : ProbabilityTheory.HasLaw Z
      (ProbabilityTheory.gaussianReal 0 1) P')
    (hX : ∀ j, Measurable (X j))
    (hLp : MemLp (X 0) 2 P)
    (hIndep : ProbabilityTheory.iIndepFun X P)
    (hIdent : ∀ j, ProbabilityTheory.IdentDistrib (X j) (X 0) P P)
    (hMean : 0 < ∫ ω, X 0 ω ∂P)
    (σ : ℝ) (hσ : 0 < σ)
    (hVar : ProbabilityTheory.variance (X 0) P = σ ^ 2)
    (L Ltilde v : ℕ → ℝ) (a : ℝ)
    (hL : Tendsto L atTop atTop)
    (hv : Tendsto (fun r ↦ v r / Real.sqrt (L r)) atTop (nhds 0))
    (hlevel : Tendsto
      (fun r ↦ (Ltilde r - L r) / Real.sqrt (L r))
      atTop (nhds 0)) :
    Tendsto
      (fun r ↦ P.real {ω |
        (postFloorTime (∫ x, X 0 x ∂P) σ a L v r : WithTop ℕ) <
          firstPassageTime X (Ltilde r) ω})
      atTop (nhds (ProbabilityTheory.cdf
        (ProbabilityTheory.gaussianReal 0 1) (-a))) := by
  have hn_top := tendsto_postFloorTime_atTop
    (σ := σ) (a := a) hMean hL hv
  have hn_pos : ∀ᶠ r in atTop,
      1 ≤ postFloorTime (∫ x, X 0 x ∂P) σ a L v r := by
    filter_upwards [hn_top.eventually_gt_atTop 0] with r hr
    omega
  apply tendsto_measureReal_firstPassageTime_gt
    (X := X) (Z := Z) hZ hX hLp hIndep hIdent hMean σ hσ hVar
      (n := postFloorTime (∫ x, X 0 x ∂P) σ a L v)
      (u := Ltilde) (c := -a) hn_pos hn_top
  simpa [mul_comm] using
    (tendsto_postFloorTime_centered (σ := σ) (a := a)
      hMean hσ hL hv hlevel)

omit [MeasurableSpace Ω] in
/-- Compare two weak hitting times when hitting the second target at any time
forces the first target to be hit at that same time. -/
lemma hittingAfter_le_hittingAfter_of_mem_imp
    {β : Type*} {u v : ℕ → Ω → β} {s t : Set β} {ω : Ω}
    (hmem : ∀ i, v i ω ∈ t → u i ω ∈ s) :
    hittingAfter u s 0 ω ≤ hittingAfter v t 0 ω := by
  by_cases htop : hittingAfter v t 0 ω = ⊤
  · simp [htop]
  · obtain ⟨i, hi⟩ := WithTop.ne_top_iff_exists.mp htop
    rw [← hi]
    apply hittingAfter_le_iff.mpr
    have hvle : hittingAfter v t 0 ω ≤ (i : WithTop ℕ) := by
      calc
        hittingAfter v t 0 ω = (i : WithTop ℕ) := hi.symm
        _ ≤ (i : WithTop ℕ) := le_rfl
    obtain ⟨j, hj, hjs⟩ := hittingAfter_le_iff.mp hvle
    exact ⟨j, hj, hmem j hjs⟩

omit [MeasurableSpace Ω] in
/-- First weak passage time above `u` for partial sums with an additive
correction process. -/
noncomputable def correctedFirstPassageTime
    (X E : ℕ → Ω → ℝ) (u : ℝ) : Ω → WithTop ℕ :=
  hittingAfter (fun n ω ↦ partialSum X n ω + E n ω) (Set.Ici u) 0

omit [MeasurableSpace Ω] in
/-- Corrected survival through time `n` means that every corrected partial sum
through `n` remains strictly below the weak-passage level. -/
lemma correctedFirstPassageTime_gt_iff
    (X E : ℕ → Ω → ℝ) (u : ℝ) (n : ℕ) (ω : Ω) :
    (n : WithTop ℕ) < correctedFirstPassageTime X E u ω ↔
      ∀ k ≤ n, partialSum X k ω + E k ω < u := by
  constructor
  · intro hhit k hk
    by_contra hku
    have hle : correctedFirstPassageTime X E u ω ≤ (n : WithTop ℕ) := by
      refine le_trans ?_
        (show (k : WithTop ℕ) ≤ (n : WithTop ℕ) by exact_mod_cast hk)
      apply hittingAfter_le_of_mem (n := 0) (i := k) (by omega)
      exact le_of_not_gt hku
    exact (not_le_of_gt hhit) hle
  · intro hpath
    rw [← not_le]
    intro hle
    obtain ⟨k, hk, hku⟩ := (hittingAfter_le_iff
      (u := fun n ω ↦ partialSum X n ω + E n ω)
      (s := Set.Ici u) (n := 0) (i := n) (ω := ω)).mp hle
    exact (not_lt_of_ge hku) (hpath k hk.2)

/-- Measurability of a finite-time corrected survival event. -/
lemma measurableSet_correctedFirstPassageTime_gt
    (X E : ℕ → Ω → ℝ)
    (hX : ∀ j, Measurable (X j)) (hE : ∀ j, Measurable (E j))
    (u : ℝ) (n : ℕ) :
    MeasurableSet {ω | (n : WithTop ℕ) < correctedFirstPassageTime X E u ω} := by
  rw [show {ω | (n : WithTop ℕ) < correctedFirstPassageTime X E u ω} =
      ⋂ k : Fin (n + 1), {ω | partialSum X k ω + E k ω < u} by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    rw [correctedFirstPassageTime_gt_iff]
    constructor
    · intro h k
      exact h k (Nat.le_of_lt_succ k.isLt)
    · intro h k hk
      exact h ⟨k, Nat.lt_succ_iff.mpr hk⟩]
  exact MeasurableSet.iInter fun k ↦
    ((measurable_partialSum X hX k).add (hE k)) measurableSet_Iio

omit [MeasurableSpace Ω] in
/-- An upper bound `E_n ≤ B` delays uncorrected passage above `u - B` no
later than corrected passage above `u`. -/
lemma firstPassageTime_sub_le_correctedFirstPassageTime
    (X E : ℕ → Ω → ℝ) (u B : ℝ) (ω : Ω)
    (hE : ∀ n, E n ω ≤ B) :
    firstPassageTime X (u - B) ω ≤ correctedFirstPassageTime X E u ω := by
  apply hittingAfter_le_hittingAfter_of_mem_imp
  intro i hi
  change u ≤ partialSum X i ω + E i ω at hi
  change u - B ≤ partialSum X i ω
  linarith [hE i]

omit [MeasurableSpace Ω] in
/-- A nonnegative correction makes corrected passage occur no later than
uncorrected passage at the same level. -/
lemma correctedFirstPassageTime_le_firstPassageTime
    (X E : ℕ → Ω → ℝ) (u : ℝ) (ω : Ω)
    (hE : ∀ n, 0 ≤ E n ω) :
    correctedFirstPassageTime X E u ω ≤ firstPassageTime X u ω := by
  apply hittingAfter_le_hittingAfter_of_mem_imp
  intro i hi
  change u ≤ partialSum X i ω at hi
  change u ≤ partialSum X i ω + E i ω
  linarith [hE i]

omit [MeasurableSpace Ω] in
/-- Pathwise corrected-passage sandwich on any path where the correction lies
between zero and `B`. -/
lemma correctedFirstPassageTime_sandwich
    (X E : ℕ → Ω → ℝ) (u B : ℝ) (ω : Ω)
    (hE0 : ∀ n, 0 ≤ E n ω) (hEB : ∀ n, E n ω ≤ B) :
    firstPassageTime X (u - B) ω ≤ correctedFirstPassageTime X E u ω ∧
      correctedFirstPassageTime X E u ω ≤ firstPassageTime X u ω :=
  ⟨firstPassageTime_sub_le_correctedFirstPassageTime X E u B ω hEB,
    correctedFirstPassageTime_le_firstPassageTime X E u ω hE0⟩

omit [MeasurableSpace Ω] in
/-- Common path event carrying nonnegativity, monotonicity, and an almost-sure
finite upper envelope for the correction. -/
def correctionGoodEvent (E : ℕ → Ω → ℝ) (Einf : Ω → ℝ) : Set Ω :=
  {ω | (∀ n, 0 ≤ E n ω) ∧ Monotone (fun n ↦ E n ω) ∧
    ∀ n, E n ω ≤ Einf ω}

omit [MeasurableSpace Ω] in
/-- Corrected survival is contained in uncorrected survival at the same level,
up to failure of the common correction event. -/
lemma correctedSurvival_subset_firstPassage_survival_union_compl
    (X E : ℕ → Ω → ℝ) (Einf : Ω → ℝ) (u : ℝ) (n : ℕ) :
    {ω | (n : WithTop ℕ) < correctedFirstPassageTime X E u ω} ⊆
      {ω | (n : WithTop ℕ) < firstPassageTime X u ω} ∪
        (correctionGoodEvent E Einf)ᶜ := by
  intro ω hω
  by_cases hgood : ω ∈ correctionGoodEvent E Einf
  · left
    exact hω.trans_le
      (correctedFirstPassageTime_le_firstPassageTime X E u ω hgood.1)
  · exact Or.inr hgood

omit [MeasurableSpace Ω] in
/-- Uncorrected survival at level `u - B` is contained in corrected survival at
`u`, up to the envelope tail and failure of the common correction event. -/
lemma firstPassage_survival_subset_correctedSurvival_union_tail_union_compl
    (X E : ℕ → Ω → ℝ) (Einf : Ω → ℝ) (u B : ℝ) (n : ℕ) :
    {ω | (n : WithTop ℕ) < firstPassageTime X (u - B) ω} ⊆
      {ω | (n : WithTop ℕ) < correctedFirstPassageTime X E u ω} ∪
        {ω | B < Einf ω} ∪ (correctionGoodEvent E Einf)ᶜ := by
  intro ω hω
  by_cases hgood : ω ∈ correctionGoodEvent E Einf
  · by_cases htail : B < Einf ω
    · exact Or.inl (Or.inr htail)
    · exact Or.inl (Or.inl (hω.trans_le
        (firstPassageTime_sub_le_correctedFirstPassageTime X E u B ω
          (fun k ↦ (hgood.2.2 k).trans (le_of_not_gt htail)))))
  · exact Or.inr hgood

/-- Probability sandwich for corrected survival when the common correction
event has full measure. -/
lemma measureReal_correctedSurvival_sandwich
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X E : ℕ → Ω → ℝ) (Einf : Ω → ℝ) (u B : ℝ) (n : ℕ)
    (hgood : μ (correctionGoodEvent E Einf)ᶜ = 0) :
    μ.real {ω | (n : WithTop ℕ) < firstPassageTime X (u - B) ω} -
        μ.real {ω | B < Einf ω} ≤
      μ.real {ω | (n : WithTop ℕ) < correctedFirstPassageTime X E u ω} ∧
    μ.real {ω | (n : WithTop ℕ) < correctedFirstPassageTime X E u ω} ≤
      μ.real {ω | (n : WithTop ℕ) < firstPassageTime X u ω} := by
  have hupper_enn :
      μ {ω | (n : WithTop ℕ) < correctedFirstPassageTime X E u ω} ≤
        μ {ω | (n : WithTop ℕ) < firstPassageTime X u ω} := by
    calc
      _ ≤ μ ({ω | (n : WithTop ℕ) < firstPassageTime X u ω} ∪
          (correctionGoodEvent E Einf)ᶜ) :=
        measure_mono
          (correctedSurvival_subset_firstPassage_survival_union_compl
            X E Einf u n)
      _ ≤ μ {ω | (n : WithTop ℕ) < firstPassageTime X u ω} +
          μ (correctionGoodEvent E Einf)ᶜ := measure_union_le _ _
      _ = μ {ω | (n : WithTop ℕ) < firstPassageTime X u ω} := by
        rw [hgood, add_zero]
  have hupper :
      μ.real {ω | (n : WithTop ℕ) < correctedFirstPassageTime X E u ω} ≤
        μ.real {ω | (n : WithTop ℕ) < firstPassageTime X u ω} := by
    rw [Measure.real_def, Measure.real_def]
    exact ENNReal.toReal_mono (measure_ne_top μ _) hupper_enn
  have hlower_enn :
      μ {ω | (n : WithTop ℕ) < firstPassageTime X (u - B) ω} ≤
        μ {ω | (n : WithTop ℕ) < correctedFirstPassageTime X E u ω} +
          μ {ω | B < Einf ω} := by
    calc
      _ ≤ μ ({ω | (n : WithTop ℕ) < correctedFirstPassageTime X E u ω} ∪
          {ω | B < Einf ω} ∪ (correctionGoodEvent E Einf)ᶜ) :=
        measure_mono
          (firstPassage_survival_subset_correctedSurvival_union_tail_union_compl
            X E Einf u B n)
      _ ≤ μ ({ω | (n : WithTop ℕ) < correctedFirstPassageTime X E u ω} ∪
          {ω | B < Einf ω}) + μ (correctionGoodEvent E Einf)ᶜ :=
        measure_union_le _ _
      _ ≤ (μ {ω | (n : WithTop ℕ) < correctedFirstPassageTime X E u ω} +
          μ {ω | B < Einf ω}) + μ (correctionGoodEvent E Einf)ᶜ := by
        gcongr
        exact measure_union_le _ _
      _ = μ {ω | (n : WithTop ℕ) < correctedFirstPassageTime X E u ω} +
          μ {ω | B < Einf ω} := by rw [hgood, add_zero]
  have hlower_add :
      μ.real {ω | (n : WithTop ℕ) < firstPassageTime X (u - B) ω} ≤
        μ.real {ω | (n : WithTop ℕ) < correctedFirstPassageTime X E u ω} +
          μ.real {ω | B < Einf ω} := by
    rw [Measure.real_def, Measure.real_def, Measure.real_def,
      ← ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _)]
    exact ENNReal.toReal_mono
      (ENNReal.add_ne_top.mpr ⟨measure_ne_top μ _, measure_ne_top μ _⟩)
      hlower_enn
  constructor
  · linarith
  · exact hupper

/-- The real measure of the strict upper tail of a measurable real-valued
function vanishes as the threshold tends to infinity. -/
lemma tendsto_measureReal_upperTail_atTop
    {μ : Measure Ω} [IsFiniteMeasure μ] (f : Ω → ℝ) (hf : Measurable f) :
    Tendsto (fun B : ℝ ↦ μ.real {ω | B < f ω}) atTop (nhds 0) := by
  have hinter : ⋂ B : ℝ, {ω | B < f ω} = ∅ := by
    ext ω
    simp only [Set.mem_iInter, Set.mem_setOf_eq, Set.mem_empty_iff_false,
      iff_false]
    intro hω
    exact (lt_irrefl (f ω)) (hω (f ω))
  have hmeasure :
      Tendsto (fun B : ℝ ↦ μ {ω | B < f ω}) atTop (nhds 0) := by
    have h := tendsto_measure_iInter_atTop
      (μ := μ) (s := fun B : ℝ ↦ {ω | B < f ω})
      (fun B ↦ (hf measurableSet_Ioi).nullMeasurableSet)
      (fun _ _ hab _ hmem ↦ hab.trans_lt hmem)
      ⟨0, measure_ne_top μ _⟩
    rw [hinter, measure_empty] at h
    simpa only [Function.comp_def] using h
  simpa only [Measure.real_def, Function.comp_def, ENNReal.toReal_zero] using
    (ENNReal.tendsto_toReal (by simp)).comp hmeasure

/-- First-passage profile for partial sums with a nonnegative correction that
is almost surely bounded by a measurable real-valued envelope. -/
lemma tendsto_measureReal_correctedFirstPassageTime_gt_postFloorTime
    {Ω' : Type*} [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'}
    [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (X E : ℕ → Ω → ℝ) (Einf : Ω → ℝ) (Z : Ω' → ℝ)
    (hZ : ProbabilityTheory.HasLaw Z
      (ProbabilityTheory.gaussianReal 0 1) P')
    (hX : ∀ j, Measurable (X j))
    (hLp : MemLp (X 0) 2 P)
    (hIndep : ProbabilityTheory.iIndepFun X P)
    (hIdent : ∀ j, ProbabilityTheory.IdentDistrib (X j) (X 0) P P)
    (hMean : 0 < ∫ ω, X 0 ω ∂P)
    (σ : ℝ) (hσ : 0 < σ)
    (hVar : ProbabilityTheory.variance (X 0) P = σ ^ 2)
    (hEinf : Measurable Einf)
    (hgood : P (correctionGoodEvent E Einf)ᶜ = 0)
    (L Ltilde v : ℕ → ℝ) (a : ℝ)
    (hL : Tendsto L atTop atTop)
    (hv : Tendsto (fun r ↦ v r / Real.sqrt (L r)) atTop (nhds 0))
    (hlevel : Tendsto
      (fun r ↦ (Ltilde r - L r) / Real.sqrt (L r))
      atTop (nhds 0)) :
    Tendsto
      (fun r ↦ P.real {ω |
        (postFloorTime (∫ x, X 0 x ∂P) σ a L v r : WithTop ℕ) <
          correctedFirstPassageTime X E (Ltilde r) ω})
      atTop (nhds (ProbabilityTheory.cdf
        (ProbabilityTheory.gaussianReal 0 1) (-a))) := by
  let B : ℕ → ℝ := fun r ↦ Real.sqrt (Real.sqrt (L r))
  have hBtop : Tendsto B atTop atTop := by
    exact Real.tendsto_sqrt_atTop.comp (Real.tendsto_sqrt_atTop.comp hL)
  have hBsmall :
      Tendsto (fun r ↦ B r / Real.sqrt (L r)) atTop (nhds 0) := by
    exact tendsto_sqrt_sqrt_div_sqrt_of_tendsto_atTop L hL
  have hshiftLevel :
      Tendsto
        (fun r ↦ ((Ltilde r - B r) - L r) / Real.sqrt (L r))
        atTop (nhds 0) := by
    have h := hlevel.sub hBsmall
    convert h using 1
    · funext r
      ring
    · norm_num
  have hlowerPass :=
    tendsto_measureReal_firstPassageTime_gt_postFloorTime
      (P := P) (P' := P') X Z hZ hX hLp hIndep hIdent hMean σ hσ hVar
      L (fun r ↦ Ltilde r - B r) v a hL hv hshiftLevel
  have hupperPass :=
    tendsto_measureReal_firstPassageTime_gt_postFloorTime
      (P := P) (P' := P') X Z hZ hX hLp hIndep hIdent hMean σ hσ hVar
      L Ltilde v a hL hv hlevel
  have htail :
      Tendsto (fun r ↦ P.real {ω | B r < Einf ω}) atTop (nhds 0) :=
    (tendsto_measureReal_upperTail_atTop (μ := P) Einf hEinf).comp hBtop
  have hlower := hlowerPass.sub htail
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (by simpa only [sub_zero] using hlower) hupperPass
  · exact Filter.Eventually.of_forall fun r ↦
      (measureReal_correctedSurvival_sandwich
        (μ := P) X E Einf (Ltilde r) (B r)
        (postFloorTime (∫ x, X 0 x ∂P) σ a L v r) hgood).1
  · exact Filter.Eventually.of_forall fun r ↦
      (measureReal_correctedSurvival_sandwich
        (μ := P) X E Einf (Ltilde r) (B r)
        (postFloorTime (∫ x, X 0 x ∂P) σ a L v r) hgood).2

end AbsorptionCutoff
