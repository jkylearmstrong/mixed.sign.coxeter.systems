/-
Copyright (c) 2026 Johnathon Kyle Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Nat.Fib.Basic
import MixedSignCoxeter.MixedSign

/-!
# Rank-2 Mixed-Sign Coxeter Systems (Chapter 3, Section 3.1)

Formalization of Section 3.1 of:
Johnathon Kyle Armstrong, *Principal Elements of Mixed-Sign Coxeter Systems* (FSU, 2012).

## Main definitions
* `rank2Graph s₀ s₁ m`: The 2-node mixed-sign Coxeter graph with signs `s₀, s₁` and edge weight `m`.
* `s0PM c`, `s1PM c`: The generating reflections for `A_2(+, -)` with off-diagonal entry `c`.
* `s0A2PM`, `s1A2PM`: The generating reflections for `A_2(+, -)[3]` (Example 3.16).

## Main results
* `det_rank2_pm` (Lemma 3.17): `det B(A_2(+, -)[m]) = -(4 + c^2) < 0` (indefinite / hyperbolic).
* `rank2_pm_comm_of_m2` (Lemma 3.14, `m = 2`): When `c = 0`, `(s₀ s₁)^2 = 1`.
* `rank2_pm_infinite_order` (Lemma 3.14, `m ≥ 3` or `∞`): When `c ≠ 0`, `(s₀ s₁)^k ≠ 1` for all `k ≥ 1`.
* `a2_pm_3_fibonacci_powers` (Example 3.16): For `k ≥ 1`,
  `(s₀ s₁)^k = (-1)^k • !![F_{2k+1}, F_{2k}; F_{2k}, F_{2k-1}]`.
-/

open Matrix

namespace MixedSignCoxeter

section RankTwo

/-- Construct a rank-2 mixed-sign Coxeter graph with node signs `s₀, s₁` and edge weight `m`
(`none` denotes `∞`). -/
def rank2Graph (s₀ s₁ : Sign) (m : Option ℕ) (hm : ∀ k, m = some k → 2 ≤ k) :
    MixedSignCoxeterGraph 2 where
  sign i := if i = 0 then s₀ else s₁
  weight i j := if i = j then none else m
  weight_symm i j := by
    fin_cases i <;> fin_cases j <;> simp
  weight_ge_two i j k h := by
    by_cases hij : i = j
    · simp [hij] at h
    · simp [hij] at h
      exact hm k h

/-- Reflection `s₀` for `B = !![2, c; c, -2]`. -/
def s0PM (c : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![-1, -c;
      0,  1]

/-- Reflection `s₁` for `B = !![2, c; c, -2]`. -/
def s1PM (c : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1,  0;
     c, -1]

/-- The reflection matrices of `rank2Graph Sign.pos Sign.neg m` match `s0PM (edgeEntry m)` and
`s1PM (edgeEntry m)`. -/
lemma rank2_pm_generators (m : Option ℕ) (hm : ∀ k, m = some k → 2 ≤ k) :
    let Γ := rank2Graph Sign.pos Sign.neg m hm
    ReflectionSystem.reflectionMatrix Γ.toBilinearForm 0 = s0PM (edgeEntry m) ∧
    ReflectionSystem.reflectionMatrix Γ.toBilinearForm 1 = s1PM (edgeEntry m) := by
  intro Γ
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Γ, rank2Graph, MixedSignCoxeterGraph.toBilinearForm,
        ReflectionSystem.reflectionMatrix_apply, Sign.toReal, s0PM] <;>
      ring
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Γ, rank2Graph, MixedSignCoxeterGraph.toBilinearForm,
        ReflectionSystem.reflectionMatrix_apply, Sign.toReal, s1PM] <;>
      ring

/-- **Lemma 3.17**: The bilinear form `B = !![2, c; c, -2]` of `A_2(+, -)[m]` has determinant
`-(4 + c^2) < 0`, so it is always indefinite of signature `(1, 1, 0)`. -/
theorem det_rank2_pm (c : ℝ) :
    Matrix.det !![(2 : ℝ), c; c, -2] = -(4 + c ^ 2) := by
  simp [Matrix.det_fin_two]
  ring

theorem det_rank2_pm_neg (c : ℝ) :
    Matrix.det !![(2 : ℝ), c; c, -2] < 0 := by
  rw [det_rank2_pm]
  nlinarith [sq_nonneg c]

/-- **Lemma 3.14 (`m = 2`)**: When `c = 0`, `s₀ s₁ = -1` and `(s₀ s₁)^2 = 1`. -/
theorem rank2_pm_order_two_of_zero :
    (s0PM 0 * s1PM 0) ^ 2 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [s0PM, s1PM, Matrix.mul_apply, sq, Fin.sum_univ_two]

/-- Helper matrix `P(c) = -(s0PM c * s1PM c) = !![1 + c^2, -c; -c, 1]`. -/
private def negProdPM (c : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1 + c ^ 2, -c;
     -c,         1]

private lemma s0PM_mul_s1PM (c : ℝ) :
    s0PM c * s1PM c = (-1 : ℝ) • negProdPM c := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [s0PM, s1PM, negProdPM, Matrix.mul_apply, Fin.sum_univ_two] <;>
    ring

private lemma negProdPM_pow_form (c : ℝ) (hc : c ≠ 0) :
    ∀ k : ℕ, 1 ≤ k →
      ∃ a b d : ℝ,
        1 < a ∧ 0 < b ∧ 1 ≤ d ∧ a - d = c ^ 2 * b ∧
        (negProdPM c) ^ k = !![a, -c * b; -c * b, d] := by
  intro k hk
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases hk0 : k = 0
    · subst hk0
      refine ⟨1 + c ^ 2, 1, 1, ?_, by norm_num, by norm_num, by ring, ?_⟩
      · have hc2 : 0 < c ^ 2 := sq_pos_of_ne_zero hc
        linarith
      · ext i j
        fin_cases i <;> fin_cases j <;> simp [negProdPM]
    · have hk1 : 1 ≤ k := Nat.pos_of_ne_zero hk0
      obtain ⟨a, b, d, ha, hb, hd, hsym, hpow⟩ := ih hk1
      have hc2 : 0 < c ^ 2 := sq_pos_of_ne_zero hc
      refine ⟨a * (1 + c ^ 2) + c ^ 2 * b, a + b, c ^ 2 * b + d, ?_, ?_, ?_, ?_, ?_⟩
      · nlinarith
      · linarith
      · nlinarith
      · linear_combination hsym
      · rw [pow_succ, hpow]
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [negProdPM, Matrix.mul_apply, Fin.sum_univ_two]
        · ring
        · ring
        · linear_combination c * hsym
        · ring

/-- **Lemma 3.14 (`m ≥ 3` or `m = ∞`)**: Whenever `c ≠ 0`, the principal element `s₀ s₁` of
`A_2(+, -)[m]` has infinite order: `(s₀ s₁)^k ≠ 1` for every `k ≥ 1`. -/
theorem rank2_pm_infinite_order (c : ℝ) (hc : c ≠ 0) (k : ℕ) (hk : 1 ≤ k) :
    (s0PM c * s1PM c) ^ k ≠ 1 := by
  rw [s0PM_mul_s1PM, smul_pow]
  obtain ⟨a, _, _, ha, _, _, _, hpow⟩ := negProdPM_pow_form c hc k hk
  rw [hpow]
  intro heq
  have h00 := congr_arg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) heq
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.one_apply_eq] at h00
  rcases neg_one_pow_eq_or ℝ k with h1 | h1
  · rw [h1, one_mul] at h00
    linarith
  · rw [h1, neg_one_mul] at h00
    linarith

/-- For `m ≥ 3`, `edgeEntry (some m) = -2 * cos(π / m) ≠ 0`. -/
lemma edgeEntry_ne_zero_of_three_le {m : ℕ} (hm : 3 ≤ m) :
    edgeEntry (some m) ≠ 0 := by
  simp only [edgeEntry]
  have hm_pos : (0 : ℝ) < (m : ℝ) := by positivity
  have hpi_div_lt : Real.pi / (m : ℝ) < Real.pi / 2 := by
    apply div_lt_div_of_pos_left Real.pi_pos (by norm_num)
    exact_mod_cast (by omega : 2 < m)
  have hpi_div_pos : 0 < Real.pi / (m : ℝ) := div_pos Real.pi_pos hm_pos
  have hcos : 0 < Real.cos (Real.pi / (m : ℝ)) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, hpi_div_lt⟩
  linarith

lemma edgeEntry_none_ne_zero : edgeEntry none ≠ 0 := by
  simp [edgeEntry]

/-! ### Example 3.16: `A_2(+, -)[3]` and Fibonacci Matrix Powers -/

/-- Generating reflection `s₀` for `A_2(+, -)[3]` (Example 3.16). -/
def s0A2PM : Matrix (Fin 2) (Fin 2) ℝ := s0PM (-1)

/-- Generating reflection `s₁` for `A_2(+, -)[3]` (Example 3.16). -/
def s1A2PM : Matrix (Fin 2) (Fin 2) ℝ := s1PM (-1)

lemma edgeEntry_three : edgeEntry (some 3) = -1 := by
  simp [edgeEntry, Real.cos_pi_div_three]

/-- **Example 3.16 (Fibonacci powers)**: For every `k ≥ 1`,
`(s₀ s₁)^k = (-1)^k • !![F_{2k+1}, F_{2k}; F_{2k}, F_{2k-1}]`. -/
theorem a2_pm_3_fibonacci_powers (k : ℕ) (hk : 1 ≤ k) :
    (s0A2PM * s1A2PM) ^ k =
      ((-1 : ℝ) ^ k) •
        !![(Nat.fib (2 * k + 1) : ℝ), (Nat.fib (2 * k) : ℝ);
           (Nat.fib (2 * k) : ℝ),     (Nat.fib (2 * k - 1) : ℝ)] := by
  rw [s0A2PM, s1A2PM, s0PM_mul_s1PM, smul_pow]
  congr 1
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases hk0 : k = 0
    · subst hk0
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [negProdPM, Nat.fib_add_two, Nat.fib_one, Nat.fib_zero] <;>
        norm_num
    · have hk1 : 1 ≤ k := Nat.pos_of_ne_zero hk0
      rw [pow_succ, ih hk1]
      have hsub1 : 2 * k - 1 + 1 = 2 * k := by omega
      have hfib1 : Nat.fib (2 * k + 1) = Nat.fib (2 * k) + Nat.fib (2 * k - 1) := by
        conv_lhs => rw [show 2 * k + 1 = (2 * k - 1) + 2 by omega]
        rw [Nat.fib_add_two, hsub1]
        ring
      have hfib2 : Nat.fib (2 * (k + 1)) = Nat.fib (2 * k + 1) + Nat.fib (2 * k) := by
        rw [show 2 * (k + 1) = 2 * k + 2 by ring, Nat.fib_add_two]
        ring
      have hfib3 : Nat.fib (2 * (k + 1) + 1) =
          Nat.fib (2 * (k + 1)) + Nat.fib (2 * k + 1) := by
        rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by ring, Nat.fib_add_two,
          show 2 * k + 1 + 1 = 2 * (k + 1) by ring]
        ring
      have hfib0 : Nat.fib (2 * (k + 1) - 1) = Nat.fib (2 * k + 1) := rfl
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp only [negProdPM, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
          Matrix.cons_val_zero, Matrix.cons_val_one] <;>
        push_cast [hfib0, hfib1, hfib2, hfib3] <;>
        ring

/-- **Corollary 3.18**: If a mixed-sign Coxeter graph `Γ` contains an adjacent pair
`(i, j)` with `Γ.signs i = .pos`, `Γ.signs j = .neg`, and `Γ.toBilinearForm i j ≠ 0`,
then `s_i * s_j` has infinite order in `W(Γ)`. -/
theorem adjacent_pm_infinite_order {n : ℕ} (Γ : MixedSignCoxeterGraph n) (i j : Fin n)
    (hne : i ≠ j) (hi : Γ.sign i = Sign.pos) (hj : Γ.sign j = Sign.neg)
    (hc : Γ.toBilinearForm i j ≠ 0) (k : ℕ) (hk : 1 ≤ k) :
    (ReflectionSystem.reflectionMatrix Γ.toBilinearForm i *
      ReflectionSystem.reflectionMatrix Γ.toBilinearForm j) ^ k ≠ 1 := by
  let c : ℝ := Γ.toBilinearForm i j
  let embed : (Fin 2 → ℝ) → (Fin n → ℝ) :=
    fun u r => if r = i then u 0 else if r = j then u 1 else 0
  have hembed_inj : ∀ u₁ u₂ : Fin 2 → ℝ, embed u₁ = embed u₂ → u₁ = u₂ := by
    intro u₁ u₂ h
    ext a
    fin_cases a
    · simpa [embed] using congr_fun h i
    · simpa [embed, Ne.symm hne] using congr_fun h j
  have hBii : Γ.toBilinearForm i i = 2 := by
    simp [MixedSignCoxeterGraph.toBilinearForm, hi, Sign.toReal]
  have hBjj : Γ.toBilinearForm j j = -2 := by
    simp [MixedSignCoxeterGraph.toBilinearForm, hj, Sign.toReal]
  have hBji : Γ.toBilinearForm j i = c :=
    (Γ.toBilinearForm_symm.apply j i).symm
  have hs_i : ∀ u : Fin 2 → ℝ,
      (ReflectionSystem.reflectionMatrix Γ.toBilinearForm i).mulVec (embed u) =
        embed ((s0PM c).mulVec u) := by
    intro u
    ext r
    simp only [Matrix.mulVec, dotProduct, ReflectionSystem.reflectionMatrix_apply, embed]
    have hc_def : Γ.toBilinearForm i j = c := rfl
    have hsplit : ∀ x : Fin n,
        ((if r = x then (1 : ℝ) else 0) -
          if r = i then 2 * Γ.toBilinearForm i x / Γ.toBilinearForm i i else 0) *
          (if x = i then u 0 else if x = j then u 1 else 0) =
        (if r = x then (if x = i then u 0 else if x = j then u 1 else 0) else 0) -
          (if r = i then (if x = i then 2 * u 0 else 0) + (if x = j then c * u 1 else 0) else 0) := by
      intro x
      by_cases hxi : x = i
      · rw [hxi]
        by_cases hri : r = i <;> simp [hri, hne, hBii] <;> ring
      · by_cases hxj : x = j
        · rw [hxj]
          by_cases hrj : r = j <;> by_cases hri : r = i <;>
            simp [hrj, hri, hxi, hne, Ne.symm hne, hBii, hc_def] <;> ring
        · by_cases hrx : r = x <;> by_cases hri : r = i <;>
            simp [hrx, hri, hxi, hxj]
    rw [Finset.sum_congr rfl fun x _ => hsplit x, Finset.sum_sub_distrib]
    have hsum1 : (∑ x : Fin n,
        if r = x then (if x = i then u 0 else if x = j then u 1 else 0) else 0) =
        if r = i then u 0 else if r = j then u 1 else 0 := by
      have : (∑ x : Fin n,
          if r = x then (if x = i then u 0 else if x = j then u 1 else 0) else 0) =
          ∑ x : Fin n, if x = r then (if x = i then u 0 else if x = j then u 1 else 0) else 0 := by
        refine Finset.sum_congr rfl fun x _ => by simp only [eq_comm]
      rw [this, Finset.sum_ite_eq']
      simp
    have hsum2 : (∑ x : Fin n,
        if r = i then (if x = i then 2 * u 0 else 0) + (if x = j then c * u 1 else 0) else 0) =
        if r = i then 2 * u 0 + c * u 1 else 0 := by
      by_cases hri : r = i
      · subst hri; simp [Finset.sum_add_distrib]
      · simp [hri]
    rw [hsum1, hsum2]
    by_cases hri : r = i
    · subst hri
      simp [s0PM, Fin.sum_univ_two, hne]
      ring
    · by_cases hrj : r = j
      · subst hrj
        simp [s0PM, Fin.sum_univ_two, hri]
      · simp [hri, hrj]
  have hs_j : ∀ u : Fin 2 → ℝ,
      (ReflectionSystem.reflectionMatrix Γ.toBilinearForm j).mulVec (embed u) =
        embed ((s1PM c).mulVec u) := by
    intro u
    ext r
    simp only [Matrix.mulVec, dotProduct, ReflectionSystem.reflectionMatrix_apply, embed]
    have hsplit : ∀ x : Fin n,
        ((if r = x then (1 : ℝ) else 0) -
          if r = j then 2 * Γ.toBilinearForm j x / Γ.toBilinearForm j j else 0) *
          (if x = i then u 0 else if x = j then u 1 else 0) =
        (if r = x then (if x = i then u 0 else if x = j then u 1 else 0) else 0) -
          (if r = j then (if x = i then -(c * u 0) else 0) + (if x = j then 2 * u 1 else 0) else 0) := by
      intro x
      by_cases hxi : x = i
      · rw [hxi]
        by_cases hri : r = i <;> by_cases hrj : r = j <;>
          simp [hri, hrj, hne, Ne.symm hne, hBjj, hBji] <;> ring
      · by_cases hxj : x = j
        · rw [hxj]
          by_cases hrj : r = j <;> simp [hrj, Ne.symm hne, hBjj] <;> ring
        · by_cases hrx : r = x <;> by_cases hrj : r = j <;>
            simp [hrx, hrj, hxi, hxj]
    rw [Finset.sum_congr rfl fun x _ => hsplit x, Finset.sum_sub_distrib]
    have hsum1 : (∑ x : Fin n,
        if r = x then (if x = i then u 0 else if x = j then u 1 else 0) else 0) =
        if r = i then u 0 else if r = j then u 1 else 0 := by
      have : (∑ x : Fin n,
          if r = x then (if x = i then u 0 else if x = j then u 1 else 0) else 0) =
          ∑ x : Fin n, if x = r then (if x = i then u 0 else if x = j then u 1 else 0) else 0 := by
        refine Finset.sum_congr rfl fun x _ => by simp only [eq_comm]
      rw [this, Finset.sum_ite_eq']
      simp
    have hsum2 : (∑ x : Fin n,
        if r = j then (if x = i then -(c * u 0) else 0) + (if x = j then 2 * u 1 else 0) else 0) =
        if r = j then -(c * u 0) + 2 * u 1 else 0 := by
      by_cases hrj : r = j
      · subst hrj; simp [Finset.sum_add_distrib]
      · simp [hrj]
    rw [hsum1, hsum2]
    by_cases hri : r = i
    · subst hri
      simp [s1PM, Fin.sum_univ_two, hne]
    · by_cases hrj : r = j
      · subst hrj
        simp [s1PM, Fin.sum_univ_two, Ne.symm hne]
        ring
      · simp [hri, hrj]
  have hmulN : ∀ (A B : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ),
      (A * B).mulVec x = A.mulVec (B.mulVec x) := fun A B x => (Matrix.mulVec_mulVec x A B).symm
  have hmul2 : ∀ (A B : Matrix (Fin 2) (Fin 2) ℝ) (x : Fin 2 → ℝ),
      (A * B).mulVec x = A.mulVec (B.mulVec x) := fun A B x => (Matrix.mulVec_mulVec x A B).symm
  have hpow : ∀ (m : ℕ) (u : Fin 2 → ℝ),
      ((ReflectionSystem.reflectionMatrix Γ.toBilinearForm i *
        ReflectionSystem.reflectionMatrix Γ.toBilinearForm j) ^ m).mulVec (embed u) =
        embed (((s0PM c * s1PM c) ^ m).mulVec u) := by
    intro m u
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ', pow_succ', hmulN, hmul2, ih, hmulN, hmul2, hs_j, hs_i]
  intro hpow1
  have hmat1 : (s0PM c * s1PM c) ^ k = 1 := by
    ext r col
    have hcol := hembed_inj (((s0PM c * s1PM c) ^ k).mulVec (Pi.single col 1)) (Pi.single col 1) (by
      rw [← hpow k (Pi.single col 1), hpow1, Matrix.one_mulVec])
    have hr := congr_fun hcol r
    fin_cases col <;>
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.one_apply,
        Pi.single_apply] at hr ⊢ <;>
      simp at hr ⊢ <;>
      exact hr
  exact rank2_pm_infinite_order c hc k hk hmat1

/-! ### Proposition 3.12 & Example 3.13 -/

/-- **Proposition 3.12**: In `A₂(-, +)` (Example 3.16), the first coordinate of
`w^k * e₀` is `(-1)^k * F_{2k+1}`, so consecutive powers strictly alternate sign. -/
theorem prop_3_12_root_oscillation (k : ℕ) :
    (Matrix.mulVec ((s0A2PM * s1A2PM) ^ k) ![1, 0]) (0 : Fin 2) =
      (-1 : ℝ) ^ k * (Nat.fib (2 * k + 1) : ℝ) ∧
    (Matrix.mulVec ((s0A2PM * s1A2PM) ^ k) ![1, 0]) (0 : Fin 2) *
      (Matrix.mulVec ((s0A2PM * s1A2PM) ^ (k + 1)) ![1, 0]) (0 : Fin 2) < 0 := by
  have h1 : ∀ m : ℕ, (Matrix.mulVec ((s0A2PM * s1A2PM) ^ m) ![1, 0]) (0 : Fin 2) =
      (-1 : ℝ) ^ m * (Nat.fib (2 * m + 1) : ℝ) := by
    intro m
    cases m with
    | zero => simp
    | succ m' =>
      rw [a2_pm_3_fibonacci_powers (m' + 1) (by omega)]
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  refine ⟨h1 k, ?_⟩
  rw [h1 k, h1 (k + 1)]
  have hf1 : (0 : ℝ) < (Nat.fib (2 * k + 1) : ℝ) := by
    exact_mod_cast Nat.fib_pos.mpr (by omega)
  have hf2 : (0 : ℝ) < (Nat.fib (2 * (k + 1) + 1) : ℝ) := by
    exact_mod_cast Nat.fib_pos.mpr (by omega)
  have hsq : (-1 : ℝ) ^ k * (-1 : ℝ) ^ (k + 1) = -1 := by
    rw [pow_succ']
    have : (-1 : ℝ) ^ k * (-1 : ℝ) ^ k = 1 := by
      rw [← mul_pow]
      norm_num
    nlinarith
  have hprod : (-1 : ℝ) ^ k * (Nat.fib (2 * k + 1) : ℝ) *
      ((-1 : ℝ) ^ (k + 1) * (Nat.fib (2 * (k + 1) + 1) : ℝ)) =
      ((-1 : ℝ) ^ k * (-1 : ℝ) ^ (k + 1)) *
      ((Nat.fib (2 * k + 1) : ℝ) * (Nat.fib (2 * (k + 1) + 1) : ℝ)) := by ring
  rw [hprod, hsq]
  nlinarith

/-- **Example 3.13** ($A_2[3] = I_2[3]$): In the classical rank-2 spherical system
with `m = 3`, `(s₀ s₁)³ = I`, giving the dihedral group `D₆` of order `6`. -/
theorem example_3_13_A2_3_order_three :
    let s0 : Matrix (Fin 2) (Fin 2) ℤ := !![-1, 1; 0, 1]
    let s1 : Matrix (Fin 2) (Fin 2) ℤ := !![1, 0; 1, -1]
    (s0 * s1) ^ 3 = 1 := by
  decide

/-- **Example 3.13 & Proposition 3.10–3.11** ($A_2[\infty] = I_2[\infty]$):
In the classical rank-2 affine system with `m = ∞`,
`(s₀ s₁)^k = !![2k + 1, -2k; 2k, 1 - 2k]`, so `(s₀ s₁)^k ≠ 1` for `k ≥ 1`
and `((s₀ s₁)^k * e₀)₀ = 2k + 1 > 0`. -/
theorem example_3_13_A2_inf_powers (k : ℕ) :
    let s0 : Matrix (Fin 2) (Fin 2) ℤ := !![-1, 2; 0, 1]
    let s1 : Matrix (Fin 2) (Fin 2) ℤ := !![1, 0; 2, -1]
    (s0 * s1) ^ k =
      !![(2 * (k : ℤ) + 1), -(2 * (k : ℤ)); (2 * (k : ℤ)), 1 - 2 * (k : ℤ)] := by
  intro s0 s1
  induction k with
  | zero =>
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  | succ m ih =>
    rw [pow_succ, ih]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [s0, s1, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem example_3_13_A2_inf_infinite_order (k : ℕ) (hk : 1 ≤ k) :
    let s0 : Matrix (Fin 2) (Fin 2) ℤ := !![-1, 2; 0, 1]
    let s1 : Matrix (Fin 2) (Fin 2) ℤ := !![1, 0; 2, -1]
    (s0 * s1) ^ k ≠ 1 := by
  intro s0 s1 h1
  have h := congr_fun (congr_fun h1 0) 0
  rw [example_3_13_A2_inf_powers k] at h
  simp at h
  omega

end RankTwo

end MixedSignCoxeter

