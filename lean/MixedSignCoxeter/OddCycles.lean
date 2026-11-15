/-
Copyright (c) 2026 Johnathon Kyle Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
import MixedSignCoxeter.TreeConjugacy

/-!
# A graph is bipartite iff it has no odd cycle (Proposition 2.41)

Formalization of Proposition 2.41 of:
Johnathon Kyle Armstrong, *Principal Elements of Mixed-Sign Coxeter Systems* (FSU, 2012).

Mathlib provides one direction (a 2-colouring forces every closed walk to have even length,
`SimpleGraph.Coloring.even_length_iff_congr`). We prove the converse and the reduction from
odd closed walks to odd cycles, for an arbitrary simple graph, and then specialise to
reflection diagrams `Γ(B)` and the `BipartiteReflectionSystem` structure of Definition 2.40.

## Main results
* `SimpleGraph.Walk.exists_odd_cycle_of_odd_length`: every odd closed walk contains (gives
  rise to) an odd cycle.
* `SimpleGraph.isBipartite_iff_forall_closedWalk_even`: `G` is 2-colourable iff every closed
  walk has even length.
* `SimpleGraph.isBipartite_iff_no_odd_cycle` (**Proposition 2.41**): `G` is bipartite iff `G`
  contains no odd cycle.
* `ReflectionSystem.exists_bipartition_iff_no_odd_cycle` (**Proposition 2.41 for reflection
  diagrams**): the nodes of `Γ(B)` split into two parts with no edges inside either part iff
  `Γ(B)` has no odd cycle.
* `ReflectionSystem.toBipartite_of_no_odd_cycle`: a reflection system without odd cycles
  is a `BipartiteReflectionSystem`, so Theorem 1.4 applies to it.
-/

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

namespace Walk

/-- Every walk from `v` to `u` either has a *path* from `v` to `u` of the same length parity,
or the graph contains an odd cycle. -/
theorem exists_path_same_parity_or_odd_cycle [DecidableEq V] :
    ∀ {v u : V} (q : G.Walk v u),
      (∃ r : G.Walk v u, r.IsPath ∧ (Even r.length ↔ Even q.length)) ∨
        ∃ (x : V) (c : G.Walk x x), c.IsCycle ∧ Odd c.length
  | _, _, .nil => Or.inl ⟨.nil, by simp⟩
  | v, u, .cons (v := w) h' q₀ => by
    rcases exists_path_same_parity_or_odd_cycle q₀ with ⟨r₀, hr₀, hpar⟩ | hodd
    · by_cases hv : v ∈ r₀.support
      · set a := r₀.takeUntil v hv
        set b := r₀.dropUntil v hv
        have hspec : a.append b = r₀ := r₀.take_spec hv
        have hlen : a.length + b.length = r₀.length := by
          rw [← hspec, length_append]
        have ha : a.IsPath := hr₀.takeUntil hv
        have hb : b.IsPath := hr₀.dropUntil hv
        have hwv : w ≠ v := fun e => h'.ne e.symm
        have ha0 : a.length ≠ 0 := by
          intro h0
          exact hwv (eq_of_length_eq_zero h0)
        by_cases hae : Even a.length
        · -- the closed walk `v → w ⇝ v` is an odd cycle
          right
          refine ⟨v, .cons h' a, ?_, ?_⟩
          · rw [isCycle_iff_isPath_tail_and_le_length]
            refine ⟨by simpa using ha, ?_⟩
            obtain ⟨k, hk⟩ := hae
            simp only [length_cons]
            omega
          · simp only [length_cons]
            exact hae.add_one
        · left
          refine ⟨b, hb, ?_⟩
          simp only [length_cons]
          rw [Nat.even_iff] at hae ⊢
          simp only [Nat.even_iff] at hpar
          rw [Nat.even_iff]
          have ha_odd : a.length % 2 = 1 := Nat.mod_two_ne_zero.mp hae
          by_cases hq : q₀.length % 2 = 0
          · have hr0 : r₀.length % 2 = 0 := hpar.mpr hq
            have hb1 : b.length % 2 = 1 := by omega
            simp [hq, hb1]; omega
          · have hq1 : q₀.length % 2 = 1 := Nat.mod_two_ne_zero.mp hq
            have hr1 : r₀.length % 2 = 1 := Nat.mod_two_ne_zero.mp (fun h => hq (hpar.mp h))
            have hb0 : b.length % 2 = 0 := by omega
            simp [hb0]; omega
      · left
        refine ⟨.cons h' r₀, hr₀.cons hv, ?_⟩
        simp only [length_cons, Nat.even_add_one, hpar]
    · exact Or.inr hodd

/-- An odd closed walk gives an odd cycle. -/
theorem exists_odd_cycle_of_odd_length {u : V} (p : G.Walk u u) (hp : Odd p.length) :
    ∃ (x : V) (c : G.Walk x x), c.IsCycle ∧ Odd c.length := by
  classical
  rcases exists_path_same_parity_or_odd_cycle p with ⟨r, hr, hpar⟩ | h
  · cases r with
    | nil =>
      simp only [length_nil, Even.zero, true_iff] at hpar
      exact absurd hpar (Nat.not_even_iff_odd.mpr hp)
    | cons _ _ =>
      exact absurd ((isPath_iff_nil.mp hr)) (by simp)
  · exact h

end Walk

/-- If every closed walk has even length, `G` is 2-colourable: colour each vertex by the parity
of a walk from a fixed representative of its connected component. -/
theorem isBipartite_of_forall_closedWalk_even
    (h : ∀ (u : V) (p : G.Walk u u), Even p.length) : Nonempty (G.Coloring Bool) := by
  classical
  have hreach : ∀ v : V, G.Reachable (G.connectedComponentMk v).out v := by
    intro v
    exact ConnectedComponent.eq.mp (Quot.out_eq (G.connectedComponentMk v))
  let W : ∀ v : V, G.Walk (G.connectedComponentMk v).out v := fun v => (hreach v).some
  refine ⟨Coloring.mk (fun v => decide (Even (W v).length)) ?_⟩
  intro u v huv
  have hcomp : G.connectedComponentMk u = G.connectedComponentMk v :=
    ConnectedComponent.connectedComponentMk_eq_of_adj huv
  have hrep : (G.connectedComponentMk v).out = (G.connectedComponentMk u).out := by
    rw [hcomp]
  let c : G.Walk (G.connectedComponentMk u).out (G.connectedComponentMk u).out :=
    ((W u).append (Walk.cons huv (W v).reverse)).copy rfl hrep
  have hc := h _ c
  simp only [c, Walk.length_copy, Walk.length_append, Walk.length_cons,
    Walk.length_reverse] at hc
  simp only [ne_eq, decide_eq_decide]
  rw [Nat.even_iff] at hc ⊢
  rw [Nat.even_iff]
  omega

/-- `G` is 2-colourable iff every closed walk has even length. -/
theorem isBipartite_iff_forall_closedWalk_even :
    G.IsBipartite ↔ ∀ (u : V) (p : G.Walk u u), Even p.length := by
  constructor
  · rintro ⟨c⟩ u p
    let c' : G.Coloring Bool := G.recolorOfEquiv finTwoEquiv c
    exact (c'.even_length_iff_congr p).mpr Iff.rfl
  · intro h
    obtain ⟨c⟩ := isBipartite_of_forall_closedWalk_even h
    simpa using c.colorable

/-- **Proposition 2.41**: A graph is bipartite if and only if it contains no odd cycle. -/
theorem isBipartite_iff_no_odd_cycle :
    G.IsBipartite ↔ ∀ (u : V) (c : G.Walk u u), c.IsCycle → ¬ Odd c.length := by
  rw [isBipartite_iff_forall_closedWalk_even]
  constructor
  · intro h u c _ hodd
    exact (Nat.not_even_iff_odd.mpr hodd) (h u c)
  · intro h u p
    by_contra hp
    obtain ⟨x, c, hc, hodd⟩ := p.exists_odd_cycle_of_odd_length (Nat.not_even_iff_odd.mp hp)
    exact h x c hc hodd

end SimpleGraph

namespace ReflectionSystem

variable {n : ℕ}

/-- **Proposition 2.41 (reflection diagrams)**: the nodes of `Γ(B)` can be split into two parts
`N₁`, `N₂` with every edge joining `N₁` to `N₂` (Definition 2.40) if and only if `Γ(B)`
contains no odd cycle. -/
theorem exists_bipartition_iff_no_odd_cycle (S : ReflectionSystem n) :
    (∃ part : Fin n → Bool, ∀ i j : Fin n, part i = part j → i ≠ j → S.B i j = 0) ↔
      ∀ (u : Fin n) (c : S.diagram.Walk u u), c.IsCycle → ¬ Odd c.length := by
  rw [← SimpleGraph.isBipartite_iff_no_odd_cycle]
  constructor
  · rintro ⟨part, hpart⟩
    refine ⟨SimpleGraph.Coloring.mk (fun i => (finTwoEquiv.symm (part i))) ?_⟩
    intro i j hij heq
    exact hij.2 (hpart i j (finTwoEquiv.symm.injective heq) hij.1)
  · rintro ⟨c⟩
    refine ⟨fun i => finTwoEquiv (c i), fun i j hpart hij => ?_⟩
    by_contra hB
    exact c.valid ⟨hij, hB⟩ (finTwoEquiv.injective hpart)

/-- A reflection system whose diagram has no odd cycle carries a bipartite structure
(Definition 2.40); in particular Theorem 1.4 (`bipartite_conjugation_theorem`) applies. -/
theorem nonempty_bipartite_of_no_odd_cycle (S : ReflectionSystem n)
    (h : ∀ (u : Fin n) (c : S.diagram.Walk u u), c.IsCycle → ¬ Odd c.length) :
    ∃ G : BipartiteReflectionSystem n, G.toReflectionSystem = S := by
  obtain ⟨part, hpart⟩ := (exists_bipartition_iff_no_odd_cycle S).mpr h
  exact ⟨⟨S, part, hpart⟩, rfl⟩

/-- Forests (in particular trees) have no odd cycles, hence are bipartite. -/
theorem no_odd_cycle_of_isAcyclic (S : ReflectionSystem n) (hG : S.diagram.IsAcyclic) :
    ∀ (u : Fin n) (c : S.diagram.Walk u u), c.IsCycle → ¬ Odd c.length :=
  fun _u c hc _ => hG c hc

end ReflectionSystem
