import Mathlib
import PEqualNP.Defs
import PEqualNP.Defs.NestedCoverCircuit
import PEqualNP.Defs.NotBracket

namespace PEqualNP.Outside.L_meta_50191

def L_meta_50191_mev (g : PEqualNP.CircuitLowerBounds.Gate) (ms : List ℕ) : ℕ :=
  match g.op with
  | PEqualNP.CircuitLowerBounds.GateOp.and =>
      (g.inputs.map fun i => ms.getD i 0).foldr (fun a b => a &&& b) 63
  | PEqualNP.CircuitLowerBounds.GateOp.or =>
      (g.inputs.map fun i => ms.getD i 0).foldr (fun a b => a ||| b) 0
  | PEqualNP.CircuitLowerBounds.GateOp.not => ((g.inputs.map fun i => ms.getD i 0).headD 0) ^^^ 63
  | _ => 0

def L_meta_50191_mw (gs : List PEqualNP.CircuitLowerBounds.Gate) (ms : List ℕ) : List ℕ :=
  gs.foldl (fun ms g => ms ++ [L_meta_50191_mev g ms]) ms

theorem L_meta_50191_gapp {α : Type} (l : List α) (b d : α) (i : ℕ) :
    (l ++ [b]).getD i d = if i < l.length then l.getD i d else if i = l.length then b else d := by
  rcases lt_trichotomy i l.length with h | h | h
  · rw [if_pos h, List.getD_append _ _ _ _ h]
  · subst h; simp
  · rw [if_neg (by omega), if_neg (by omega), List.getD_eq_default _ _ (by simp; omega)]

theorem L_meta_50191_ev (t : ℕ) (ht : t < 6) (w : List Bool) (ms : List ℕ)
    (h : ∀ i, w.getD i false = (ms.getD i 0).testBit t) (g : PEqualNP.CircuitLowerBounds.Gate)
    (hg : g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨
      g.op = PEqualNP.CircuitLowerBounds.GateOp.not) :
    g.op.eval (g.inputs.map fun i => w.getD i false) = (L_meta_50191_mev g ms).testBit t := by
  have h63 : (63 : ℕ).testBit t = true := by interval_cases t <;> decide
  obtain ⟨op, ins⟩ := g
  rcases hg with hg | hg | hg <;> simp only at hg <;> subst hg
  · simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, L_meta_50191_mev]
    induction ins with
    | nil => simp [h63]
    | cons a l ih =>
      simp only [List.map_cons, List.all_cons, List.foldr_cons, Nat.testBit_and]
      rw [← ih, h a]; rfl
  · simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, L_meta_50191_mev]
    induction ins with
    | nil => simp
    | cons a l ih =>
      simp only [List.map_cons, List.any_cons, List.foldr_cons, Nat.testBit_or]
      rw [← ih, h a]; rfl
  · cases ins with
    | nil => simp [PEqualNP.CircuitLowerBounds.GateOp.eval, L_meta_50191_mev, h63]
    | cons a l =>
      simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, L_meta_50191_mev, List.map_cons,
        List.headD_cons, Nat.testBit_xor, h63, h a, Bool.xor_true]

theorem L_meta_50191_wires_mask (t : ℕ) (ht : t < 6) :
    ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) (ms : List ℕ),
    (∀ g ∈ gs, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) →
    w.length = ms.length → (∀ i, w.getD i false = (ms.getD i 0).testBit t) →
    ∀ i, (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD i false
      = ((L_meta_50191_mw gs ms).getD i 0).testBit t
  | [], w, ms, _, _, h => by simpa [L_meta_50191_mw] using h
  | g :: gs, w, ms, hg, hl, h => by
    have := L_meta_50191_wires_mask t ht gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (ms ++ [L_meta_50191_mev g ms]) (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg')) (by simp [hl])
      (by
        intro i
        rw [L_meta_50191_gapp, L_meta_50191_gapp, hl]
        split_ifs
        · exact h i
        · exact L_meta_50191_ev t ht w ms h g (hg g List.mem_cons_self)
        · simp)
    simpa [L_meta_50191_mw, List.foldl_cons] using this

theorem L_meta_50191_getD_lt (ms : List ℕ) (h : ∀ x ∈ ms, x < 64) (i : ℕ) : ms.getD i 0 < 64 := by
  induction ms generalizing i with
  | nil => simp
  | cons a l ih =>
    cases i with
    | zero => simpa using h a List.mem_cons_self
    | succ i => simpa using ih (fun x hx => h x (List.mem_cons_of_mem _ hx)) i

theorem L_meta_50191_mev_lt (g : PEqualNP.CircuitLowerBounds.Gate) (ms : List ℕ)
    (h : ∀ x ∈ ms, x < 64) : L_meta_50191_mev g ms < 64 := by
  have hg := L_meta_50191_getD_lt ms h
  obtain ⟨op, ins⟩ := g
  cases op <;> simp only [L_meta_50191_mev]
  · induction ins with
    | nil => simp
    | cons a l ih => exact lt_of_le_of_lt Nat.and_le_right ih
  · induction ins with
    | nil => simp
    | cons a l ih =>
      simp only [List.map_cons, List.foldr_cons]
      exact Nat.or_lt_two_pow (n := 6) (hg a) ih
  · cases ins with
    | nil => simp
    | cons a l => exact Nat.xor_lt_two_pow (n := 6) (hg a) (by decide)
  all_goals decide

theorem L_meta_50191_mw_len : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (ms : List ℕ),
    (L_meta_50191_mw gs ms).length = ms.length + gs.length
  | [], ms => by simp [L_meta_50191_mw]
  | g :: gs, ms => by
    have := L_meta_50191_mw_len gs (ms ++ [L_meta_50191_mev g ms])
    simp only [L_meta_50191_mw, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem L_meta_50191_mw_lt : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (ms : List ℕ),
    (∀ x ∈ ms, x < 64) → ∀ x ∈ L_meta_50191_mw gs ms, x < 64
  | [], ms, h => by simpa [L_meta_50191_mw] using h
  | g :: gs, ms, h => by
    have := L_meta_50191_mw_lt gs (ms ++ [L_meta_50191_mev g ms]) (by
      intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · exact h x hx
      · simp at hx; subst hx; exact L_meta_50191_mev_lt g ms h)
    simpa [L_meta_50191_mw, List.foldl_cons] using this

def L_meta_50191_T : List ℕ := [6, 22, 52]

def L_meta_50191_miss (ms : List ℕ) : ℕ := L_meta_50191_T.countP (fun x => !ms.contains x)

def L_meta_50191_c0 (ms : List ℕ) : List ℕ :=
  [63, 0] ++ ms.flatMap (fun a => [a &&& 63, a ||| 0] ++ ms.flatMap fun b => [a &&& (b &&& 63), a ||| (b ||| 0)])

def L_meta_50191_c1 (ms : List ℕ) : List ℕ := (0 ^^^ 63) :: ms.map (fun a => a ^^^ 63)

def L_meta_50191_bits (l : List ℕ) : ℕ := l.foldl (fun B v => B ||| (1 <<< v)) 0

def L_meta_50191_srch : ℕ → List ℕ → ℕ → Bool
  | 0, ms, _ => L_meta_50191_T.all ms.contains
  | r + 1, ms, k => L_meta_50191_T.all ms.contains ||
      (decide (L_meta_50191_miss ms ≤ r + 1) &&
        (List.range 64).any fun v =>
          ((L_meta_50191_bits (L_meta_50191_c0 ms)).testBit v && L_meta_50191_srch r (ms ++ [v]) k) ||
          ((decide (k < 2) && (L_meta_50191_bits (L_meta_50191_c1 ms)).testBit v) &&
            L_meta_50191_srch r (ms ++ [v]) (k + 1)))

theorem L_meta_50191_bits_mem (l : List ℕ) (v : ℕ) (hv : v ∈ l) :
    (L_meta_50191_bits l).testBit v = true := by
  have key : ∀ (l : List ℕ) (B : ℕ), (B.testBit v = true ∨ v ∈ l) →
      (l.foldl (fun B v => B ||| (1 <<< v)) B).testBit v = true := by
    intro l
    induction l with
    | nil => intro B h; simpa using h
    | cons a l ih =>
      intro B h
      apply ih
      rcases h with h | h
      · left; simp [Nat.testBit_or, h]
      · rcases List.mem_cons.1 h with h | h
        · left; subst h; simp [Nat.testBit_or, Nat.testBit_shiftLeft]
        · right; exact h
  exact key l 0 (Or.inr hv)

theorem L_meta_50191_miss_step (ms : List ℕ) (v : ℕ) :
    L_meta_50191_miss ms ≤ L_meta_50191_miss (ms ++ [v]) + 1 := by
  simp only [L_meta_50191_miss, L_meta_50191_T, List.countP_cons, List.countP_nil,
    List.contains_append, List.contains_cons, List.contains_nil]
  by_cases h6 : v = 6 <;> by_cases h22 : v = 22 <;> by_cases h52 : v = 52 <;> subst_vars <;>
    simp_all <;> split_ifs <;> simp_all <;> omega

theorem L_meta_50191_miss_mw : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (ms : List ℕ),
    L_meta_50191_miss ms ≤ L_meta_50191_miss (L_meta_50191_mw gs ms) + gs.length
  | [], ms => by simp [L_meta_50191_mw]
  | g :: gs, ms => by
    have h1 := L_meta_50191_miss_step ms (L_meta_50191_mev g ms)
    have h2 := L_meta_50191_miss_mw gs (ms ++ [L_meta_50191_mev g ms])
    simp only [L_meta_50191_mw, List.foldl_cons, List.length_cons] at h2 ⊢
    omega

theorem L_meta_50191_miss_zero (ms : List ℕ) (h : ∀ x ∈ L_meta_50191_T, x ∈ ms) :
    L_meta_50191_miss ms = 0 := by
  simp only [L_meta_50191_miss, List.countP_eq_zero]
  intro x hx
  simp [h x hx]

def L_meta_50191_V : List PEqualNP.CircuitLowerBounds.Gate → ℕ → Prop
  | [], _ => True
  | g :: gs, n => (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧
      g.inputs.length ≤ 2 ∧ (∀ i ∈ g.inputs, i < n) ∧ L_meta_50191_V gs (n + 1)

theorem L_meta_50191_getD_mem (ms : List ℕ) (i : ℕ) (hi : i < ms.length) : ms.getD i 0 ∈ ms := by
  rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi

theorem L_meta_50191_c0_mem (g : PEqualNP.CircuitLowerBounds.Gate) (ms : List ℕ)
    (hop : g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or)
    (hlen : g.inputs.length ≤ 2) (hin : ∀ i ∈ g.inputs, i < ms.length) :
    L_meta_50191_mev g ms ∈ L_meta_50191_c0 ms := by
  obtain ⟨op, ins⟩ := g
  simp only at hop hlen hin
  match ins, hlen, hin with
  | [], _, _ => rcases hop with h | h <;> subst h <;> simp [L_meta_50191_mev, L_meta_50191_c0]
  | [a], _, hin =>
    have ha := L_meta_50191_getD_mem ms a (hin a (by simp))
    rcases hop with h | h <;> subst h <;> simp only [L_meta_50191_mev, L_meta_50191_c0, List.map_cons,
      List.map_nil, List.foldr_cons, List.foldr_nil, List.mem_append, List.mem_flatMap] <;>
      exact Or.inr ⟨ms.getD a 0, ha, by simp⟩
  | [a, b], _, hin =>
    have ha := L_meta_50191_getD_mem ms a (hin a (by simp))
    have hb := L_meta_50191_getD_mem ms b (hin b (by simp))
    rcases hop with h | h <;> subst h <;> simp only [L_meta_50191_mev, L_meta_50191_c0, List.map_cons,
      List.map_nil, List.foldr_cons, List.foldr_nil, List.mem_append, List.mem_flatMap] <;>
      (right; refine ⟨ms.getD a 0, ha, ?_⟩; right; exact ⟨ms.getD b 0, hb, by simp⟩)
  | _ :: _ :: _ :: _, h, _ => simp at h

theorem L_meta_50191_c1_mem (g : PEqualNP.CircuitLowerBounds.Gate) (ms : List ℕ)
    (hop : g.op = PEqualNP.CircuitLowerBounds.GateOp.not) (hin : ∀ i ∈ g.inputs, i < ms.length) :
    L_meta_50191_mev g ms ∈ L_meta_50191_c1 ms := by
  obtain ⟨op, ins⟩ := g
  simp only at hop hin
  subst hop
  cases ins with
  | nil => simp [L_meta_50191_mev, L_meta_50191_c1]
  | cons a l =>
    have ha := L_meta_50191_getD_mem ms a (hin a (by simp))
    simp only [L_meta_50191_mev, L_meta_50191_c1, List.map_cons, List.headD_cons, List.mem_cons,
      List.mem_map]
    exact Or.inr ⟨_, ha, rfl⟩

theorem L_meta_50191_srch_all (r k : ℕ) (ms : List ℕ) (hs : L_meta_50191_srch r ms k = false) :
    L_meta_50191_T.all ms.contains = false := by
  cases r with
  | zero => simpa [L_meta_50191_srch] using hs
  | succ r =>
    simp only [L_meta_50191_srch, Bool.or_eq_false_iff] at hs
    exact hs.1

theorem L_meta_50191_sound : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (r k : ℕ) (ms : List ℕ),
    L_meta_50191_srch r ms k = false → gs.length ≤ r → (∀ x ∈ ms, x < 64) →
    L_meta_50191_V gs ms.length →
    k + PEqualNP.NotBracket.notCount ⟨gs, 0⟩ ≤ 2 →
    ¬ (∀ x ∈ L_meta_50191_T, x ∈ L_meta_50191_mw gs ms)
  | [], r, k, ms, hs, _, _, _, _ => by
    intro hall
    have := L_meta_50191_srch_all r k ms hs
    rw [List.all_eq_false] at this
    obtain ⟨x, hx, hc⟩ := this
    simp [L_meta_50191_mw] at hall
    simp [hall x hx] at hc
  | g :: gs, r, k, ms, hs, hlen, hlt, hV, hk => by
    intro hall
    cases r with
    | zero => simp at hlen
    | succ r =>
      obtain ⟨hop, hl2, hin, hV'⟩ := hV
      simp only [L_meta_50191_srch, Bool.or_eq_false_iff, Bool.and_eq_false_iff,
        decide_eq_false_iff_not] at hs
      rcases hs.2 with hm | hany
      · have h1 := L_meta_50191_miss_mw (g :: gs) ms
        rw [L_meta_50191_miss_zero _ hall] at h1
        simp at h1 hlen
        omega
      · rw [List.any_eq_false] at hany
        have hv := L_meta_50191_mev_lt g ms hlt
        have hrange : L_meta_50191_mev g ms ∈ List.range 64 := List.mem_range.2 hv
        have hb := hany _ hrange
        have hlt' : ∀ x ∈ ms ++ [L_meta_50191_mev g ms], x < 64 := by
          intro x hx
          rcases List.mem_append.1 hx with hx | hx
          · exact hlt x hx
          · simp at hx; subst hx; exact hv
        have hV'' : L_meta_50191_V gs (ms ++ [L_meta_50191_mev g ms]).length := by simpa using hV'
        have hall' : ∀ x ∈ L_meta_50191_T, x ∈ L_meta_50191_mw gs (ms ++ [L_meta_50191_mev g ms]) := by
          simpa [L_meta_50191_mw, List.foldl_cons] using hall
        by_cases hn : g.op = PEqualNP.CircuitLowerBounds.GateOp.not
        · have hk2 : k < 2 := by simp [PEqualNP.NotBracket.notCount, List.filter_cons, hn] at hk; omega
          have hbit := L_meta_50191_bits_mem _ _ (L_meta_50191_c1_mem g ms hn hin)
          have hs' : L_meta_50191_srch r (ms ++ [L_meta_50191_mev g ms]) (k + 1) = false := by
            simp [hbit, hk2] at hb
            exact hb.2
          exact L_meta_50191_sound gs r (k + 1) _ hs' (by simp at hlen; omega) hlt' hV''
            (by simp [PEqualNP.NotBracket.notCount, List.filter_cons, hn] at hk ⊢; omega) hall'
        · have hop' : g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
              g.op = PEqualNP.CircuitLowerBounds.GateOp.or := by tauto
          have hbit := L_meta_50191_bits_mem _ _ (L_meta_50191_c0_mem g ms hop' hl2 hin)
          have hs' : L_meta_50191_srch r (ms ++ [L_meta_50191_mev g ms]) k = false := by
            simp [hbit] at hb
            exact hb.1
          exact L_meta_50191_sound gs r k _ hs' (by simp at hlen; omega) hlt' hV''
            (by simp [PEqualNP.NotBracket.notCount, List.filter_cons, hn] at hk ⊢; omega) hall'

theorem L_meta_50191_V_of : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (n : ℕ),
    (∀ g ∈ gs, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧
      g.inputs.length ≤ 2) →
    (∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).inputs, i < n + j) →
    L_meta_50191_V gs n
  | [], _, _, _ => trivial
  | g :: gs, n, h1, h2 => by
    refine ⟨(h1 g List.mem_cons_self).1, (h1 g List.mem_cons_self).2, ?_, ?_⟩
    · intro i hi; simpa using h2 0 (by simp) i (by simpa using hi)
    · apply L_meta_50191_V_of gs (n + 1) (fun g' hg' => h1 g' (List.mem_cons_of_mem _ hg'))
      intro j hj i hi
      have := h2 (j + 1) (by simp; omega) i (by simpa using hi)
      omega

theorem L_meta_50191_search : L_meta_50191_srch 5 [62, 60, 56, 48, 32, 0, 63] 0 = false := by
  decide +kernel

theorem L_meta_50191_base (t : Fin 6) (i : ℕ) :
    ((List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false, true]).getD i false =
      (([62, 60, 56, 48, 32, 0, 63] : List ℕ).getD i 0).testBit t.val := by
  by_cases hi : i < 7
  · have key : ∀ t : Fin 6, ∀ i : Fin 7,
        ((List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false, true]).getD i.val false =
          (([62, 60, 56, 48, 32, 0, 63] : List ℕ).getD i.val 0).testBit t.val := by decide
    exact key t ⟨i, hi⟩
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    simp

theorem L_meta_50191_pick (mw : List ℕ) (hlt : ∀ x ∈ mw, x < 64) (p c : ℕ) (hp : p < mw.length)
    (hc : c < 64) (h : ∀ t : Fin 6, (mw.getD p 0).testBit t.val = c.testBit t.val) : c ∈ mw := by
  have hx := L_meta_50191_getD_mem mw p hp
  have heq : mw.getD p 0 = c := by
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < 6
    · exact h ⟨i, hi⟩
    · have h64 : (64 : ℕ) ≤ 2 ^ i := by
        calc (64 : ℕ) = 2 ^ 6 := by norm_num
          _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (hlt _ hx) h64),
        Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hc h64)]
  rw [← heq]; exact hx

end PEqualNP.Outside.L_meta_50191

open PEqualNP.Outside.L_meta_50191

theorem PEqualNP.Outside.L_meta_50191 : (¬ (∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (7+D.size)),
  PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 7 D ∧
  PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ 5 ∧
  ∀ t : Fin 6,
    let xs := (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false,true]
    let w := D.wires xs
    w.getD p.val false = (6 : Nat).testBit t.val ∧
    w.getD q.val false = (22 : Nat).testBit t.val ∧
    w.getD r.val false = (52 : Nat).testBit t.val)) := by
  rintro ⟨D, p, q, r, hF, hR, hN, hS, hw⟩
  have hops : ∀ g ∈ D.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧
      g.inputs.length ≤ 2 := by
    intro g hg
    have := hF g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
    exact this
  have hV : L_meta_50191_V D.gates ([62, 60, 56, 48, 32, 0, 63] : List ℕ).length :=
    L_meta_50191_V_of D.gates 7 hops (fun j hj i hi => hR j hj i hi)
  set mw := L_meta_50191_mw D.gates [62, 60, 56, 48, 32, 0, 63] with hmw
  have hlt : ∀ x ∈ mw, x < 64 := L_meta_50191_mw_lt _ _ (by decide)
  have hlen : mw.length = 7 + D.size := by
    rw [hmw, L_meta_50191_mw_len]; rfl
  have hbit : ∀ t : Fin 6, ∀ i, (D.wires ((List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++
      [false, true])).getD i false = (mw.getD i 0).testBit t.val := by
    intro t i
    exact L_meta_50191_wires_mask t.val t.isLt D.gates _ _ (fun g hg => (hops g hg).1) (by simp)
      (L_meta_50191_base t) i
  have h6 : 6 ∈ mw := L_meta_50191_pick mw hlt p.val 6 (by omega) (by norm_num)
    (fun t => by rw [← hbit t]; exact (hw t).1)
  have h22 : 22 ∈ mw := L_meta_50191_pick mw hlt q.val 22 (by omega) (by norm_num)
    (fun t => by rw [← hbit t]; exact (hw t).2.1)
  have h52 : 52 ∈ mw := L_meta_50191_pick mw hlt r.val 52 (by omega) (by norm_num)
    (fun t => by rw [← hbit t]; exact (hw t).2.2)
  apply L_meta_50191_sound D.gates 5 0 _ L_meta_50191_search hS (by decide) hV
    (by rw [Nat.zero_add]; exact hN)
  intro x hx
  simp only [L_meta_50191_T, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl <;> assumption
