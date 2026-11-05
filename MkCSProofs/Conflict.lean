module

public import MkCSProofs.Definitions
public import Mathlib.Tactic

/-! Compatibility port of Chapter09.lean; exact retained proofs at accepted source pin.
The completed proof is checked separately from the advertised Challenge. -/
@[expose] public section
noncomputable section
open scoped BigOperators
namespace Chapter09
variable {α : Type*} [DecidableEq α]
theorem conflicts_empty_iff (E : Finset (α × α)) (S : Finset α) :
    conflicts E S = ∅ ↔ feasible E S := by
  simp only [conflicts, feasible, Finset.filter_eq_empty_iff]

theorem cover_subset (E : Finset (α × α)) (S : Finset α) : cover E S ⊆ S := by
  intro a ha
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp ha
  exact (Finset.mem_filter.mp he).2.1

theorem repair_subset (E : Finset (α × α)) (S : Finset α) : repair E S ⊆ S :=
  Finset.sdiff_subset

theorem repair_feasible (E : Finset (α × α)) (S : Finset α) :
    feasible E (repair E S) := by
  intro e he hboth
  have h1 := Finset.mem_sdiff.mp hboth.1
  have h2 := Finset.mem_sdiff.mp hboth.2
  have hec : e ∈ conflicts E S := Finset.mem_filter.mpr ⟨he, h1.1, h2.1⟩
  exact h1.2 (Finset.mem_image.mpr ⟨e, hec, rfl⟩)

theorem feasible_score (E : Finset (α × α)) (w : α × α → ℝ) (S : Finset α)
    (h : feasible E S) : score E w S = (S.card : ℝ) := by
  simp [score, (conflicts_empty_iff E S).mpr h]

theorem weighted_repair_bound (E : Finset (α × α)) (w : α × α → ℝ)
    (hw : ∀ e ∈ E, 1 ≤ w e) (S : Finset α) :
    score E w S ≤ ((repair E S).card : ℝ) := by
  have hweights : ((conflicts E S).card : ℝ) ≤ ∑ e ∈ conflicts E S, w e := by
    calc
      ((conflicts E S).card : ℝ) = ∑ _e ∈ conflicts E S, (1 : ℝ) := by simp
      _ ≤ ∑ e ∈ conflicts E S, w e := Finset.sum_le_sum (fun e he => hw e (Finset.mem_filter.mp he).1)
  have hcover : ((cover E S).card : ℝ) ≤ ((conflicts E S).card : ℝ) := by
    exact_mod_cast (Finset.card_image_le : (cover E S).card ≤ (conflicts E S).card)
  have hcard : ((repair E S).card : ℝ) + ((cover E S).card : ℝ) = (S.card : ℝ) := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card (cover_subset E S)
  unfold score
  linarith

theorem strict_weighted_repair_bound (E : Finset (α × α)) (w : α × α → ℝ)
    (hw : ∀ e ∈ E, 1 < w e) (S : Finset α) (hbad : ¬ feasible E S) :
    score E w S < ((repair E S).card : ℝ) := by
  have hne : (conflicts E S).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hz
    exact hbad ((conflicts_empty_iff E S).mp hz)
  obtain ⟨e, he⟩ := hne
  have hweights : ((conflicts E S).card : ℝ) < ∑ e ∈ conflicts E S, w e := by
    calc
      ((conflicts E S).card : ℝ) = ∑ _e ∈ conflicts E S, (1 : ℝ) := by simp
      _ < ∑ e ∈ conflicts E S, w e := Finset.sum_lt_sum
        (fun j hj => (hw j (Finset.mem_filter.mp hj).1).le)
        ⟨e, he, hw e (Finset.mem_filter.mp he).1⟩
  have hcover : ((cover E S).card : ℝ) ≤ ((conflicts E S).card : ℝ) := by
    exact_mod_cast (Finset.card_image_le : (cover E S).card ≤ (conflicts E S).card)
  have hcard : ((repair E S).card : ℝ) + ((cover E S).card : ℝ) = (S.card : ℝ) := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card (cover_subset E S)
  unfold score
  linarith

def isScoreMax (E : Finset (α × α)) (w : α × α → ℝ) (S : Finset α) : Prop :=
  ∀ T : Finset α, score E w T ≤ score E w S

theorem weak_penalty_optimum_repair (E : Finset (α × α)) (w : α × α → ℝ)
    (hw : ∀ e ∈ E, 1 ≤ w e) (S : Finset α) (hmax : isScoreMax E w S) :
    feasible E (repair E S) ∧
    score E w S = ((repair E S).card : ℝ) ∧
    ∀ T : Finset α, feasible E T → (T.card : ℝ) ≤ ((repair E S).card : ℝ) := by
  have hf := repair_feasible E S
  have hr := feasible_score E w (repair E S) hf
  have heq : score E w S = ((repair E S).card : ℝ) :=
    le_antisymm (weighted_repair_bound E w hw S) (by simpa [hr] using hmax (repair E S))
  refine ⟨hf, heq, ?_⟩
  intro T ht
  simpa [feasible_score E w T ht, heq] using hmax T

theorem strict_penalty_optimizer_feasible (E : Finset (α × α)) (w : α × α → ℝ)
    (hw : ∀ e ∈ E, 1 < w e) (S : Finset α) (hmax : isScoreMax E w S) :
    feasible E S ∧ ∀ T : Finset α, feasible E T → (T.card : ℝ) ≤ (S.card : ℝ) := by
  have hf : feasible E S := by
    by_contra hbad
    have hb := strict_weighted_repair_bound E w hw S hbad
    have hr := feasible_score E w (repair E S) (repair_feasible E S)
    have hm := hmax (repair E S)
    rw [hr] at hm
    linarith
  refine ⟨hf, ?_⟩
  intro T ht
  simpa [feasible_score E w T ht, feasible_score E w S hf] using hmax T

end Chapter09
