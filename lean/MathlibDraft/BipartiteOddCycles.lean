/-
Copyright (c) 2026 Johnathon Kyle Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johnathon Kyle Armstrong
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
# Characterization of bipartite simple graphs by absence of odd cycles

Mathlib-generalized port of `MixedSignCoxeter.OddCycles` (PR #46507).
-/

@[expose] public section

namespace SimpleGraph

namespace Walk

variable {V : Type*} {G : SimpleGraph V}

/-- Every walk from `v` to `u` either admits a path from `v` to `u` of the same length parity,
or the graph contains an odd cycle. -/
theorem exists_isPath_even_length_iff_or_exists_isCycle_odd_length {v u : V} (p : G.Walk v u) :
    (∃ q : G.Walk v u, q.IsPath ∧ (Even q.length ↔ Even p.length)) ∨
      ∃ (x : V) (c : G.Walk x x), c.IsCycle ∧ Odd c.length := by
  classical
  induction p with
  | nil => exact Or.inl ⟨.nil, by simp⟩
  | @cons v w u h' p₀ ih =>
    rcases ih with ⟨r₀, hr₀, hpar⟩ | hodd
    · by_cases hv : v ∈ r₀.support
      · set a := r₀.takeUntil v hv
        set b := r₀.dropUntil v hv
        have hlen : a.length + b.length = r₀.length := by
          rw [← length_append, r₀.take_spec hv]
        have ha : a.IsPath := hr₀.takeUntil hv
        have hb : b.IsPath := hr₀.dropUntil hv
        have ha0 : a.length ≠ 0 := fun h0 ↦ h'.ne (eq_of_length_eq_zero h0).symm
        by_cases hae : Even a.length
        · right
          refine ⟨v, .cons h' a, ?_, ?_⟩
          · rw [isCycle_iff_isPath_tail_and_le_length]
            refine ⟨by simpa using ha, ?_⟩
            obtain ⟨k, hk⟩ := hae
            simp only [length_cons]
            omega
          · simpa only [length_cons] using hae.add_one
        · left
          refine ⟨b, hb, ?_⟩
          have ha_odd : Odd a.length := Nat.not_even_iff_odd.mp hae
          simp only [length_cons, Nat.even_add_one, ← hpar, ← hlen, Nat.even_add,
            Nat.not_even_iff_odd.mpr ha_odd, false_iff, not_not]
      · left
        refine ⟨.cons h' r₀, hr₀.cons hv, ?_⟩
        simp only [length_cons, Nat.even_add_one, hpar]
    · exact Or.inr hodd

/-- Every closed walk of odd length implies the existence of an odd cycle. -/
theorem exists_isCycle_odd_length {u : V} {p : G.Walk u u} (hp : Odd p.length) :
    ∃ (x : V) (c : G.Walk x x), c.IsCycle ∧ Odd c.length := by
  rcases p.exists_isPath_even_length_iff_or_exists_isCycle_odd_length with ⟨r, hr, hpar⟩ | h
  · cases r with
    | nil =>
      simp only [length_nil, Even.zero, true_iff] at hpar
      exact absurd hpar (Nat.not_even_iff_odd.mpr hp)
    | cons _ _ =>
      exact absurd (isPath_iff_nil.mp hr) (by simp)
  · exact h

end Walk

/-- A simple graph is bipartite if and only if every cycle has even length. -/
theorem isBipartite_iff_forall_isCycle_even_length {V : Type*} {G : SimpleGraph V} :
    G.IsBipartite ↔ ∀ (v : V) (c : G.Walk v v), c.IsCycle → Even c.length := by
  rw [IsBipartite, two_colorable_iff_forall_loop_even]
  refine ⟨fun h v c _ ↦ h v c, fun h v p ↦ ?_⟩
  by_contra hp
  obtain ⟨x, c, hc, hodd⟩ := p.exists_isCycle_odd_length (Nat.not_even_iff_odd.mp hp)
  exact Nat.not_even_iff_odd.mpr hodd (h x c hc)

/-- A simple graph is bipartite if and only if it is free of odd cycle graphs `cycleGraph n`
for all `n ≥ 3`. -/
theorem isBipartite_iff_forall_odd_free_cycleGraph {V : Type*} {G : SimpleGraph V} :
    G.IsBipartite ↔ ∀ n ≥ 3, Odd n → (cycleGraph n).Free G := by
  rw [isBipartite_iff_forall_isCycle_even_length]
  refine ⟨fun h n hn hodd hle ↦ ?_, fun h v c hc ↦ ?_⟩
  · obtain ⟨v, c, hc, rfl⟩ := (cycleGraph_isContained_iff hn).mp hle
    exact Nat.not_even_iff_odd.mpr hodd (h v c hc)
  · by_contra heven
    exact h c.length hc.three_le_length (Nat.not_even_iff_odd.mp heven)
      ((cycleGraph_isContained_iff hc.three_le_length).mpr ⟨v, c, hc, rfl⟩)

/-- A simple graph is bipartite if and only if it is `(cycleGraph (2 * n + 3)).Free` for all `n`. -/
theorem isBipartite_iff_free_cycleGraph_two_mul_add_three {V : Type*} {G : SimpleGraph V} :
    G.IsBipartite ↔ ∀ n : ℕ, (cycleGraph (2 * n + 3)).Free G := by
  rw [isBipartite_iff_forall_odd_free_cycleGraph]
  refine ⟨fun h n ↦ h (2 * n + 3) (by omega) ⟨n + 1, by omega⟩, fun h n hn ⟨k, hk⟩ ↦ ?_⟩
  have heq : n = 2 * (k - 1) + 3 := by omega
  exact heq ▸ h (k - 1)

end SimpleGraph
