/-
Copyright (c) 2026 Johnathon Kyle Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.GroupTheory.Coxeter.Basic
import MixedSignCoxeter.CyclesAndDeletion

/-!
# Classical Coxeter Quotients, Deletion Property, and Corollary 1.3

Formalization of:
- **Proposition 3.19**: Every reflection system (and mixed-sign Coxeter group) `W(S)`
  is a quotient of the universal Coxeter group `W(K_n[∞])`.
- **Deletion Property & Theorem 3.9** framing (`SatisfiesDeletionProperty`) and its
  invariance under `𝒪`-conjugacy (`SignedPerm`).
- **Corollary 1.3**: For every `k : ℕ`, `(tildeAminus2Extended k).toReflectionSystem`
  is not `𝒪`-conjugate to any reflection system satisfying the Deletion Property
  (and hence, by Theorem 3.9, not conjugate to any classical Coxeter system).
-/

namespace MixedSignCoxeter

open Matrix ReflectionSystem

/-! ### Proposition 3.19: Universal Coxeter Quotient -/

/-- The universal rank-`n` Coxeter matrix `K_n[∞]` with `M i i = 1` and `M i j = 0` (`∞`)
for `i ≠ j`. -/
def freeCoxeterMatrix (n : ℕ) : CoxeterMatrix (Fin n) where
  M i j := if i = j then 1 else 0
  isSymm := by
    ext i j
    dsimp [Matrix.transpose]
    by_cases h : i = j <;> simp [h, eq_comm]
  diagonal := by
    intro i; simp
  off_diagonal := by
    intro i j hij; simp [hij]

/-- **Proposition 3.19**: For any `S : ReflectionSystem n`, the generating reflections
`S.reflectionMatrix` lift to a monoid homomorphism from the universal Coxeter group
`(freeCoxeterMatrix n).Group` to `Matrix (Fin n) (Fin n) ℝ`, realizing `W(S)` as a
quotient of `W(K_n[∞])`. -/
theorem reflectionSystem_isLiftable_freeCoxeter {n : ℕ} (S : ReflectionSystem n) :
    (freeCoxeterMatrix n).IsLiftable (reflectionMatrix S.B) := by
  intro i j
  by_cases h : i = j
  · subst h
    simp [freeCoxeterMatrix, reflectionMatrix_mul_self S i]
  · simp [freeCoxeterMatrix, h]

noncomputable def freeCoxeterQuotient {n : ℕ} (S : ReflectionSystem n) :
    (freeCoxeterMatrix n).Group →* Matrix (Fin n) (Fin n) ℝ :=
  (freeCoxeterMatrix n).toCoxeterSystem.lift ⟨reflectionMatrix S.B, reflectionSystem_isLiftable_freeCoxeter S⟩

theorem freeCoxeterQuotient_simple {n : ℕ} (S : ReflectionSystem n) (i : Fin n) :
    freeCoxeterQuotient S ((freeCoxeterMatrix n).toCoxeterSystem.simple i) =
      reflectionMatrix S.B i :=
  (freeCoxeterMatrix n).toCoxeterSystem.lift_apply_simple
    (reflectionSystem_isLiftable_freeCoxeter S) i

/-! ### Deletion Property and Corollary 1.3 -/

/-- A `ReflectionSystem n` satisfies the **Deletion Property** if every non-reduced word
`w` (one equal in `W(S)` to a strictly shorter word `u`) admits two indices `i < j < w.length`
whose deletion preserves `S.wordProd w`. -/
def SatisfiesDeletionProperty {n : ℕ} (S : ReflectionSystem n) : Prop :=
  ∀ w : List (Fin n), (∃ u : List (Fin n), u.length < w.length ∧ S.wordProd w = S.wordProd u) →
    ∃ i j : ℕ, i < j ∧ j < w.length ∧ S.wordProd (deleteTwo w i j) = S.wordProd w

/-- For every `k : ℕ`, the rank `3 + k` system `tildeAminus2Extended k` fails the
Deletion Property (Theorem 1.2). -/
theorem tildeAminus2Extended_not_deletion (k : ℕ) :
    ¬ SatisfiesDeletionProperty (tildeAminus2Extended k).toReflectionSystem := by
  intro hdel
  obtain ⟨heq, hno⟩ := theorem_1_2_infinite_family k
  let w : List (Fin (3 + k)) := [0, 1, 0, 2, 0].map (Fin.castAdd k)
  let u : List (Fin (3 + k)) := [2, 0, 1].map (Fin.castAdd k)
  have hu : u.length < w.length := by simp [u, w]
  obtain ⟨i, j, hij, hj, hdel_eq⟩ := hdel w ⟨u, hu, heq⟩
  have hlen : w.length = 5 := by simp [w]
  rw [hlen] at hj
  have hi5 : i < 5 := lt_trans hij hj
  exact hno ⟨i, hi5⟩ ⟨j, hj⟩ hij hdel_eq

private lemma deleteTwo_map {α β : Type*} (f : α → β) (w : List α) (i j : ℕ) :
    deleteTwo (w.map f) i j =
      (deleteTwo w i j).map f := by
  simp [deleteTwo, List.zipIdx_map, List.filter_map, Function.comp_def]

private lemma wordProd_O_conjugate {n : ℕ} {B₁ B₂ : Matrix (Fin n) (Fin n) ℝ}
    (P : SignedPerm n) (hB : B₂ = P.toMatrixᵀ * B₁ * P.toMatrix) (w : List (Fin n)) :
    P.toMatrixᵀ * (w.map (reflectionMatrix B₁ ∘ P.perm)).prod * P.toMatrix =
      (w.map (reflectionMatrix B₂)).prod := by
  induction w with
  | nil =>
    simp [P.toMatrix_transpose_mul_self]
  | cons a t ih =>
    simp only [List.map_cons, List.prod_cons, Function.comp_apply]
    have ha : P.toMatrixᵀ * reflectionMatrix B₁ (P.perm a) * P.toMatrix = reflectionMatrix B₂ a :=
      conjugate_reflections_of_form B₁ B₂ P hB a
    have hPP : P.toMatrix * P.toMatrixᵀ = 1 := by
      ext r c
      simp only [Matrix.mul_apply, Matrix.transpose_apply, SignedPerm.toMatrix_apply, Matrix.one_apply]
      have hterm : ∀ k : Fin n,
          (if r = P.perm k then P.signReal k else 0) *
            (if c = P.perm k then P.signReal k else 0) =
          if k = P.perm.symm r then (if r = c then 1 else 0) else 0 := by
        intro k
        by_cases hk : k = P.perm.symm r
        · subst hk
          have hpk : P.perm (P.perm.symm r) = r := P.perm.apply_symm_apply r
          by_cases hrc : r = c
          · subst hrc; simp [hpk, P.signReal_mul_self]
          · simp [hpk, hrc, Ne.symm hrc]
        · have hne : r ≠ P.perm k := fun h => hk (P.perm.eq_symm_apply.mpr h.symm)
          simp [hk, hne]
      rw [Finset.sum_congr rfl fun k _ => hterm k]
      simp
    calc P.toMatrixᵀ * (reflectionMatrix B₁ (P.perm a) *
          (t.map (reflectionMatrix B₁ ∘ P.perm)).prod) * P.toMatrix
        = (P.toMatrixᵀ * reflectionMatrix B₁ (P.perm a) * P.toMatrix) *
            (P.toMatrixᵀ * (t.map (reflectionMatrix B₁ ∘ P.perm)).prod * P.toMatrix) := by
          calc P.toMatrixᵀ * (reflectionMatrix B₁ (P.perm a) *
                (t.map (reflectionMatrix B₁ ∘ P.perm)).prod) * P.toMatrix
              = P.toMatrixᵀ * reflectionMatrix B₁ (P.perm a) * 1 *
                  (t.map (reflectionMatrix B₁ ∘ P.perm)).prod * P.toMatrix := by
                simp only [mul_one, mul_assoc]
            _ = P.toMatrixᵀ * reflectionMatrix B₁ (P.perm a) * (P.toMatrix * P.toMatrixᵀ) *
                  (t.map (reflectionMatrix B₁ ∘ P.perm)).prod * P.toMatrix := by rw [hPP]
            _ = (P.toMatrixᵀ * reflectionMatrix B₁ (P.perm a) * P.toMatrix) *
                  (P.toMatrixᵀ * (t.map (reflectionMatrix B₁ ∘ P.perm)).prod * P.toMatrix) := by
                simp only [mul_assoc]
      _ = reflectionMatrix B₂ a * (t.map (reflectionMatrix B₂)).prod := by rw [ha, ih]

/-- The Deletion Property is invariant under `𝒪`-conjugacy (`SignedPerm`). -/
theorem deletion_invariant_of_O_conjugate {n : ℕ} (S₁ S₂ : ReflectionSystem n)
    (P : SignedPerm n) (hB : S₂.B = P.toMatrixᵀ * S₁.B * P.toMatrix)
    (h1 : SatisfiesDeletionProperty S₁) :
    SatisfiesDeletionProperty S₂ := by
  intro w ⟨u, hu, heq⟩
  have hconj : ∀ v : List (Fin n),
      P.toMatrixᵀ * S₁.wordProd (v.map P.perm) * P.toMatrix = S₂.wordProd v := by
    intro v
    simpa [wordProd, List.map_map] using wordProd_O_conjugate P hB v
  have hS1eq : S₁.wordProd (w.map P.perm) = S₁.wordProd (u.map P.perm) := by
    have hw := hconj w
    have hu_conj := hconj u
    rw [heq, ← hu_conj] at hw
    have h1' := congr_arg (fun M => P.toMatrix * M * P.toMatrixᵀ) hw
    have hPP : P.toMatrix * P.toMatrixᵀ = 1 := by
      ext r c
      simp only [Matrix.mul_apply, Matrix.transpose_apply, SignedPerm.toMatrix_apply, Matrix.one_apply]
      have hterm : ∀ k : Fin n,
          (if r = P.perm k then P.signReal k else 0) *
            (if c = P.perm k then P.signReal k else 0) =
          if k = P.perm.symm r then (if r = c then 1 else 0) else 0 := by
        intro k
        by_cases hk : k = P.perm.symm r
        · subst hk
          have hpk : P.perm (P.perm.symm r) = r := P.perm.apply_symm_apply r
          by_cases hrc : r = c
          · subst hrc; simp [hpk, P.signReal_mul_self]
          · simp [hpk, hrc, Ne.symm hrc]
        · have hne : r ≠ P.perm k := fun h => hk (P.perm.eq_symm_apply.mpr h.symm)
          simp [hk, hne]
      rw [Finset.sum_congr rfl fun k _ => hterm k]
      simp
    have h1'' : (P.toMatrix * P.toMatrixᵀ) * S₁.wordProd (w.map P.perm) *
        (P.toMatrix * P.toMatrixᵀ) =
        (P.toMatrix * P.toMatrixᵀ) * S₁.wordProd (u.map P.perm) *
          (P.toMatrix * P.toMatrixᵀ) := by
      simpa only [mul_assoc] using h1'
    simpa [hPP] using h1''
  obtain ⟨i, j, hij, hj, hdel⟩ := h1 (w.map P.perm) ⟨u.map P.perm, by simpa using hu, hS1eq⟩
  refine ⟨i, j, hij, by simpa using hj, ?_⟩
  rw [← hconj (deleteTwo w i j), ← hconj w,
    ← deleteTwo_map P.perm w i j, hdel]

/-- **Corollary 1.3**: For every `k : ℕ`, `(tildeAminus2Extended k).toReflectionSystem`
is not `𝒪`-conjugate to any reflection system `S₁` satisfying the Deletion Property
(and hence, by Theorem 3.9, not conjugate to any classical Coxeter system). -/
theorem corollary_1_3_not_conjugate_to_deletion (k : ℕ)
    (S₁ : ReflectionSystem (3 + k)) (hdel : SatisfiesDeletionProperty S₁) :
    ¬ ∃ P : SignedPerm (3 + k),
      (tildeAminus2Extended k).toBilinearForm =
        P.toMatrixᵀ * S₁.B * P.toMatrix := by
  rintro ⟨P, hB⟩
  have h2 := deletion_invariant_of_O_conjugate S₁
    (tildeAminus2Extended k).toReflectionSystem P hB hdel
  exact tildeAminus2Extended_not_deletion k h2

/-! ### Proposition 3.8 & Theorem 3.9: Exchange Property from Deletion -/

/-- A word `w` is **reduced** in `S` if it is not equal in `W(S)` to any strictly shorter word. -/
def IsReducedWord {n : ℕ} (S : ReflectionSystem n) (w : List (Fin n)) : Prop :=
  ∀ u : List (Fin n), u.length < w.length → S.wordProd w ≠ S.wordProd u

/-- A `ReflectionSystem n` satisfies the **Exchange Property** (Proposition 3.8 / Theorem 3.9)
if whenever `w` is reduced and `s :: w` equals a strictly shorter word in `W(S)`, there exists
`k < w.length` such that `S.wordProd (s :: w) = S.wordProd (w.eraseIdx k)`. -/
def SatisfiesExchangeProperty {n : ℕ} (S : ReflectionSystem n) : Prop :=
  ∀ (s : Fin n) (w : List (Fin n)), IsReducedWord S w →
    (∃ u : List (Fin n), u.length < (s :: w).length ∧ S.wordProd (s :: w) = S.wordProd u) →
    ∃ k : ℕ, k < w.length ∧ S.wordProd (s :: w) = S.wordProd (w.eraseIdx k)

private lemma filter_zipIdx_offset {α : Type*} (w : List α) (k m : ℕ) :
    ((List.zipIdx w (k + 1)).filter (fun p => p.2 ≠ k + 1 + m)).map Prod.fst =
      w.eraseIdx m := by
  induction w generalizing k m with
  | nil => simp
  | cons a t ih =>
    cases m with
    | zero =>
      have hsub : ∀ p ∈ List.zipIdx t (k + 2), p.2 ≠ k + 1 := by
        intro p hp
        have := List.mem_zipIdx hp
        omega
      simp [List.zipIdx_cons]
      rw [List.filter_eq_self.mpr]
      · simp
      · intro p hp
        simp [hsub p hp]
    | succ m' =>
      have hne : k + 1 ≠ k + 1 + (m' + 1) := by omega
      simp only [List.zipIdx_cons, List.filter_cons, decide_eq_true_eq, List.eraseIdx_cons_succ]
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ih (k + 1) m'

private lemma deleteTwo_cons_zero {α : Type*} (s : α) (w : List α) (j : ℕ) (hj : 0 < j) :
    deleteTwo (s :: w) 0 j = w.eraseIdx (j - 1) := by
  cases j with
  | zero => exact absurd hj (Nat.lt_irrefl 0)
  | succ m =>
    unfold deleteTwo
    simp only [List.zipIdx_cons, List.filter_cons, ne_eq, not_true_eq_false, false_and,
      decide_false, Bool.false_eq_true, ↓reduceIte]
    have hfilt : (List.zipIdx w 1).filter (fun p => p.2 ≠ 0 ∧ p.2 ≠ m + 1) =
        (List.zipIdx w 1).filter (fun p => p.2 ≠ m + 1) := by
      refine List.filter_congr ?_
      intro p hp
      have hge : 1 ≤ p.2 := (List.mem_zipIdx hp).1
      have hne : p.2 ≠ 0 := by omega
      simp [hne]
    rw [hfilt]
    simpa [Nat.add_comm] using filter_zipIdx_offset w 0 m

private lemma deleteTwo_cons_succ {α : Type*} (s : α) (w : List α) (i j : ℕ) :
    deleteTwo (s :: w) (i + 1) (j + 1) = s :: deleteTwo w i j := by
  unfold deleteTwo
  simp only [List.zipIdx_cons, List.filter_cons, ne_eq, Nat.zero_ne_add_one, not_false_eq_true,
    and_self, decide_true, ↓reduceIte, List.map_cons]
  have hshift : ∀ (l : List α) (k : ℕ),
      ((List.zipIdx l (k + 1)).filter (fun p => p.2 ≠ i + 1 ∧ p.2 ≠ j + 1)).map Prod.fst =
        ((List.zipIdx l k).filter (fun p => p.2 ≠ i ∧ p.2 ≠ j)).map Prod.fst := by
    intro l
    induction l with
    | nil => intro k; simp
    | cons a t ih =>
      intro k
      simp only [List.zipIdx_cons, List.filter_cons]
      have hk1 : (k + 1 ≠ i + 1 ∧ k + 1 ≠ j + 1) ↔ (k ≠ i ∧ k ≠ j) := by omega
      by_cases h : (k ≠ i ∧ k ≠ j)
      · have h' : (k + 1 ≠ i + 1 ∧ k + 1 ≠ j + 1) := hk1.mpr h
        have hc1 : decide (k + 1 ≠ i + 1 ∧ k + 1 ≠ j + 1) = true := decide_eq_true h'
        have hc2 : decide (k ≠ i ∧ k ≠ j) = true := decide_eq_true h
        rw [hc1, hc2]
        simp only [↓reduceIte, List.map_cons]
        exact congrArg (a :: ·) (ih (k + 1))
      · have h' : ¬(k + 1 ≠ i + 1 ∧ k + 1 ≠ j + 1) := mt hk1.mp h
        have hc1 : decide (k + 1 ≠ i + 1 ∧ k + 1 ≠ j + 1) = false := decide_eq_false h'
        have hc2 : decide (k ≠ i ∧ k ≠ j) = false := decide_eq_false h
        rw [hc1, hc2]
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact ih (k + 1)
  congr 1
  exact hshift w 0

private lemma deleteTwo_length_lt {α : Type*} (w : List α) (i j : ℕ)
    (hi : i < w.length) : (deleteTwo w i j).length < w.length := by
  unfold deleteTwo
  rw [List.length_map]
  have hgen : ∀ (l : List α) (k : ℕ), k ≤ i → i < k + l.length →
      ((List.zipIdx l k).filter (fun p => p.2 ≠ i ∧ p.2 ≠ j)).length < l.length := by
    intro l
    induction l with
    | nil => intro k hk1 hk2; simp at hk2; omega
    | cons a t ih =>
      intro k hk1 hk2
      simp only [List.zipIdx_cons, List.filter_cons, List.length_cons]
      by_cases hki : k = i
      · subst hki
        simp only [ne_eq, not_true_eq_false, false_and, decide_false, Bool.false_eq_true, ↓reduceIte]
        exact Nat.lt_succ_of_le ((List.length_filter_le _ _).trans (by simp))
      · have hlt : k + 1 ≤ i := by omega
        have hlt2 : i < (k + 1) + t.length := by simp at hk2; omega
        have iht := ih (k + 1) hlt hlt2
        split_ifs
        · simp only [List.length_cons]; omega
        · omega
  exact hgen w 0 (Nat.zero_le i) (by omega)

/-- **Proposition 3.8 / Theorem 3.9** (Deletion implies Exchange): Any `ReflectionSystem n`
satisfying the Deletion Property also satisfies the Exchange Property. -/
theorem exchange_of_deletion {n : ℕ} (S : ReflectionSystem n)
    (hdel : SatisfiesDeletionProperty S) :
    SatisfiesExchangeProperty S := by
  intro s w hwred hshort
  obtain ⟨i, j, hij, hj, heq⟩ := hdel (s :: w) hshort
  cases i with
  | zero =>
    refine ⟨j - 1, ?_, ?_⟩
    · simp only [List.length_cons] at hj; omega
    · rw [← heq, deleteTwo_cons_zero s w j hij]
  | succ i' =>
    cases j with
    | zero => exact absurd hij (Nat.not_lt_zero _)
    | succ j' =>
      exfalso
      have hj' : j' < w.length := by simp only [List.length_cons] at hj; omega
      have hi' : i' < w.length := lt_trans (by omega : i' < j') hj'
      have hlen : (deleteTwo w i' j').length < w.length :=
        deleteTwo_length_lt w i' j' hi'
      rw [deleteTwo_cons_succ] at heq
      have hprod : S.wordProd (deleteTwo w i' j') = S.wordProd w := by
        have h1 : reflectionMatrix S.B s * S.wordProd (deleteTwo w i' j') =
            reflectionMatrix S.B s * S.wordProd w := by
          simpa [wordProd] using heq
        have h2 := congr_arg (fun M => reflectionMatrix S.B s * M) h1
        simpa only [← mul_assoc, reflectionMatrix_mul_self, one_mul] using h2
      exact hwred (deleteTwo w i' j') hlen hprod.symm

/-- **Theorem 3.9** (Exchange implies Deletion): Any `ReflectionSystem n` satisfying
the Exchange Property also satisfies the Deletion Property. -/
theorem deletion_of_exchange {n : ℕ} (S : ReflectionSystem n)
    (hex : SatisfiesExchangeProperty S) :
    SatisfiesDeletionProperty S := by
  intro w
  induction w with
  | nil =>
    rintro ⟨u, hu, _⟩
    simp at hu
  | cons s t ih =>
    intro hshort
    by_cases ht : IsReducedWord S t
    · obtain ⟨k, hk, heq⟩ := hex s t ht hshort
      refine ⟨0, k + 1, Nat.zero_lt_succ k, by simp only [List.length_cons]; omega, ?_⟩
      rw [deleteTwo_cons_zero s t (k + 1) (Nat.zero_lt_succ k)]
      simpa using heq.symm
    · unfold IsReducedWord at ht
      push Not at ht
      obtain ⟨u, hu, heq⟩ := ht
      obtain ⟨i, j, hij, hj, hdel⟩ := ih ⟨u, hu, heq⟩
      refine ⟨i + 1, j + 1, Nat.succ_lt_succ hij, by simp only [List.length_cons]; omega, ?_⟩
      rw [deleteTwo_cons_succ]
      simp only [wordProd, List.map_cons, List.prod_cons]
      exact congrArg (reflectionMatrix S.B s * ·) hdel

/-- **Theorem 3.9 (Deletion ↔ Exchange)**: For any `ReflectionSystem n`, the Deletion
Property and the Exchange Property are logically equivalent. -/
theorem deletion_iff_exchange {n : ℕ} (S : ReflectionSystem n) :
    SatisfiesDeletionProperty S ↔ SatisfiesExchangeProperty S :=
  ⟨exchange_of_deletion S, deletion_of_exchange S⟩

/-- **Theorem 3.9 (Coxeter presentation lift)**: Whenever the pairwise products of
reflections in `S` satisfy the Coxeter relations of `M : CoxeterMatrix (Fin n)`,
`W(S)` is a quotient of the classical Coxeter group `M.Group`. -/
theorem reflectionSystem_isLiftable_of_orders {n : ℕ} (S : ReflectionSystem n)
    (M : CoxeterMatrix (Fin n))
    (hord : ∀ i j : Fin n, (reflectionMatrix S.B i * reflectionMatrix S.B j) ^ (M.M i j) = 1) :
    M.IsLiftable (reflectionMatrix S.B) :=
  hord

end MixedSignCoxeter
