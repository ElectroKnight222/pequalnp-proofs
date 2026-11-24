import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 1600000 in
theorem PEqualNP.Outside.R_meta_4267_1
    (h1 : ¬ PEqualNP.MetaComplexity.HasCircuitSize 6
      (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 3) || (x 1 && x 4) ||
        (x 2 && x 4) || (x 3 && x 5) || (x 2 && x 5)) 7)
    (h2 :
      let f : (Fin 7 → Bool) → Bool := fun x =>
        ([1, 12, 4, 15, 26, 35, 46, 36] : List ℕ).any fun e =>
          x (Fin.ofNat 7 (e / 10)) && x (Fin.ofNat 7 (e % 10))
      let gat := PEqualNP.MetaComplexity.NestedCover.gateAt
      let eff (g : PEqualNP.CircuitLowerBounds.Gate) : List ℕ :=
        match g.op with
        | PEqualNP.CircuitLowerBounds.GateOp.not => g.inputs.take 1
        | _ => g.inputs
      ∀ (C D : PEqualNP.CircuitLowerBounds.Circuit) (a b : ℕ),
        PEqualNP.MetaComplexity.FanInTwo C → C.size = 11 →
        PEqualNP.MetaComplexity.circuitFun 7 C = f →
        List.Forall₂ (fun g h : PEqualNP.CircuitLowerBounds.Gate =>
          g.op = h.op ∧ List.Forall₂ (fun i j => j = i + 1 ∨ j = 0 ∧ (i = a ∨ i = b)) g.inputs h.inputs)
          C.gates D.gates →
        (∀ x : Fin 7 → Bool, (D.wires (true :: List.ofFn x)).getD (C.output + 1) false = (f x || x 2)) →
        (∀ x : Fin 7 → Bool, x 2 = false → f x = false →
          ¬ ∀ g ∈ C.gates, 2 ∈ g.inputs →
            g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
            ∃ j : Fin 7, j ≠ 2 ∧ j.val ∈ g.inputs ∧ x j = true) →
        (C.gates.filter (fun g => g.op.eval [true, false] && g.inputs.contains 2)).length = 2 →
        (C.gates.filter (fun g => (eff g).contains 2)).length = 2 →
        (∃ k < 11, 0 ∈ eff (gat D k) ∧
          (gat D k).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
          (gat D k).inputs.length = 2 ∧ (gat D k).inputs ≠ [0, 0] ∧ 3 ∉ (gat D k).inputs ∧
          ∀ j < 11, j ≠ k → 0 ∈ eff (gat D j) →
            (gat C j).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ 2 ∈ (gat C j).inputs) →
        False) :
    have x1 : (Fin (7 : ℕ) → Bool) → Bool := fun (x1 : Fin (7 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (4 : ℕ), (15 : ℕ), (26 : ℕ), (35 : ℕ), (46 : ℕ), (36 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (7 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (7 : ℕ) (x2 % (10 : ℕ))); ∀ (x2 x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : ℕ), PEqualNP.MetaComplexity.FanInTwo x2 → x2.size = (11 : ℕ) → PEqualNP.MetaComplexity.circuitFun (7 : ℕ) x2 = x1 → List.Forall₂ (fun (x9 x10 : PEqualNP.CircuitLowerBounds.Gate) => x9.op = x10.op ∧ List.Forall₂ (fun (x11 x12 : ℕ) => x12 = x11 + (1 : ℕ) ∨ x12 = (0 : ℕ) ∧ (x11 = x4 ∨ x11 = x5)) x9.inputs x10.inputs) x2.gates x3.gates → (∀ (x10 : Fin (7 : ℕ) → Bool), (x3.wires (Bool.true :: List.ofFn x10)).getD (x2.output + (1 : ℕ)) Bool.false = (x1 x10 || x10 (2 : Fin (7 : ℕ)))) → (∀ (x11 : Fin (7 : ℕ) → Bool), x11 (2 : Fin (7 : ℕ)) = Bool.false → x1 x11 = Bool.false → ¬∀ x14 ∈ x2.gates, (2 : ℕ) ∈ x14.inputs → x14.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∃ (x17 : Fin (7 : ℕ)), x17 ≠ (2 : Fin (7 : ℕ)) ∧ ↑x17 ∈ x14.inputs ∧ x11 x17 = Bool.true) → (List.filter (fun (x12 : PEqualNP.CircuitLowerBounds.Gate) => x12.op.eval [Bool.true, Bool.false] && x12.inputs.contains (2 : ℕ)) x2.gates).length < (2 : ℕ) := by
  classical
  intro f C D a b hfan hsize hfun hedits hD hunm
  by_contra hlt
  have hge2 : 2 ≤ (C.gates.filter (fun g => g.op.eval [true, false] && g.inputs.contains 2)).length := by
    omega
  let eff (g : PEqualNP.CircuitLowerBounds.Gate) : List ℕ :=
    match g.op with
    | PEqualNP.CircuitLowerBounds.GateOp.not => g.inputs.take 1
    | _ => g.inputs
  let c6 (y : Fin 6 → Bool) : Bool :=
    (y 0 && y 1) || (y 0 && y 3) || (y 1 && y 4) ||
      (y 2 && y 4) || (y 3 && y 5) || (y 2 && y 5)
  let stepW (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have hstep_len : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool),
      (gs.foldl stepW w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp
    | cons g gs ih =>
      intro w
      rw [List.foldl_cons, ih]
      simp [stepW]
      omega
  have hstep_lt : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) (i : ℕ),
      i < w.length → (gs.foldl stepW w).getD i false = w.getD i false := by
    intro gs
    induction gs with
    | nil => intro w i _; rfl
    | cons g gs ih =>
      intro w i hi
      rw [List.foldl_cons, ih (stepW w g) i (by simp [stepW]; omega)]
      simp only [stepW, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  have hstep_gate : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) (k : ℕ)
      (hk : k < gs.length),
      (gs.foldl stepW w).getD (w.length + k) false =
        gs[k].op.eval (gs[k].inputs.map fun i => ((gs.take k).foldl stepW w).getD i false) := by
    intro gs
    induction gs with
    | nil => intro w k hk; simp at hk
    | cons g gs ih =>
      intro w k hk
      cases k with
      | zero =>
        rw [List.foldl_cons, Nat.add_zero]
        have hlen : w.length < (stepW w g).length := by simp [stepW]
        rw [hstep_lt gs (stepW w g) w.length hlen]
        simp [stepW]
      | succ k =>
        rw [List.foldl_cons, List.take_succ_cons, List.foldl_cons]
        have hk' : k < gs.length := by simpa using hk
        have hlen : (stepW w g).length = w.length + 1 := by simp [stepW]
        have h := ih (stepW w g) k hk'
        rw [hlen] at h
        rw [show w.length + (k + 1) = w.length + 1 + k by omega]
        exact h
  have hfa_mem_left : ∀ {α β : Type} {R : α → β → Prop} {l1 : List α} {l2 : List β} {x : α},
      List.Forall₂ R l1 l2 → x ∈ l1 → ∃ y ∈ l2, R x y := by
    intro α β R l1 l2 x h hx
    induction h with
    | nil => cases hx
    | @cons x0 y0 xs ys hxy _ ih =>
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact ⟨y0, List.mem_cons_self, hxy⟩
      · obtain ⟨y, hy, hr⟩ := ih hx'
        exact ⟨y, List.mem_cons_of_mem _ hy, hr⟩
  have hcard_filter : ∀ {α : Type} (l : List α) (m : ℕ) (hm : l.length = m) (p : α → Bool),
      (Finset.univ.filter (fun k : Fin m => p (l[k.val]'(by omega)))).card = (l.filter p).length := by
    intro α l m hm p
    subst hm
    induction l with
    | nil => simp
    | cons x xs ih =>
      rw [Finset.card_filter]
      change (∑ k : Fin (xs.length + 1), if p ((x :: xs)[k.val]) = true then 1 else 0) =
        ((x :: xs).filter p).length
      rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, List.getElem_cons_zero, Fin.val_succ, List.getElem_cons_succ,
        List.filter_cons]
      rw [← Finset.card_filter, ih]
      by_cases hpx : p x = true <;> simp [hpx] <;> omega
  have hcount_eq_filter : ∀ (l : List Bool),
      l.count false = (l.filter (fun b => b == false)).length := by
    intro l
    induction l with
    | nil => simp
    | cons b l ih =>
      cases b <;> simp [List.count_cons, ih]
  have hlenC : C.gates.length = 11 := hsize
  have hlenD : D.gates.length = 11 := by
    have h := (List.forall₂_iff_get.mp hedits).1
    omega
  have hfan_mem : ∀ (k : ℕ) (hk : k < 11),
      (C.gates[k]'(by omega)).op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
        PEqualNP.CircuitLowerBounds.GateOp.or, PEqualNP.CircuitLowerBounds.GateOp.not} :
          Set PEqualNP.CircuitLowerBounds.GateOp) ∧
      (C.gates[k]'(by omega)).inputs.length ≤ 2 := by
    intro k hk
    exact hfan _ (List.getElem_mem (by omega))
  have hedits_get : ∀ (k : ℕ) (hk : k < 11),
      (C.gates[k]'(by omega)).op = (D.gates[k]'(by omega)).op ∧
      List.Forall₂ (fun i j => j = i + 1 ∨ j = 0 ∧ (i = a ∨ i = b))
        (C.gates[k]'(by omega)).inputs (D.gates[k]'(by omega)).inputs := by
    intro k hk
    exact (List.forall₂_iff_get.mp hedits).2 k (by omega) (by omega)
  have hfanD : PEqualNP.MetaComplexity.FanInTwo D := by
    intro h hh
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hh
    have hk11 : k < 11 := by omega
    obtain ⟨hop, hinp⟩ := hedits_get k hk11
    obtain ⟨hm1, hm2⟩ := hfan_mem k hk11
    refine ⟨hop ▸ hm1, ?_⟩
    rw [← (List.forall₂_iff_get.mp hinp).1]
    exact hm2
  have heval_eff : ∀ (g : PEqualNP.CircuitLowerBounds.Gate) (v : ℕ → Bool),
      g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
        PEqualNP.CircuitLowerBounds.GateOp.or, PEqualNP.CircuitLowerBounds.GateOp.not} :
          Set PEqualNP.CircuitLowerBounds.GateOp) →
      g.op.eval (g.inputs.map v) = g.op.eval ((eff g).map v) := by
    intro g v hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with h | h | h
    · simp [eff, h]
    · simp [eff, h]
    · simp only [eff, h]
      cases hgi : g.inputs with
      | nil => rfl
      | cons i rest =>
        simp [PEqualNP.CircuitLowerBounds.GateOp.eval]
  have heff_rel_of : ∀ (g h : PEqualNP.CircuitLowerBounds.Gate),
      g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
        PEqualNP.CircuitLowerBounds.GateOp.or, PEqualNP.CircuitLowerBounds.GateOp.not} :
          Set PEqualNP.CircuitLowerBounds.GateOp) →
      g.op = h.op →
      List.Forall₂ (fun i j => j = i + 1 ∨ j = 0 ∧ (i = a ∨ i = b)) g.inputs h.inputs →
      List.Forall₂ (fun i j => j = i + 1 ∨ j = 0 ∧ (i = a ∨ i = b)) (eff g) (eff h) := by
    intro g h hg hop hinp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with hg | hg | hg
    · have hhop : h.op = PEqualNP.CircuitLowerBounds.GateOp.and := hop.symm.trans hg
      simp only [eff, hg, hhop]; exact hinp
    · have hhop : h.op = PEqualNP.CircuitLowerBounds.GateOp.or := hop.symm.trans hg
      simp only [eff, hg, hhop]; exact hinp
    · have hhop : h.op = PEqualNP.CircuitLowerBounds.GateOp.not := hop.symm.trans hg
      simp only [eff, hg, hhop]
      cases hgi : g.inputs with
      | nil =>
        rw [hgi] at hinp
        cases hdi : h.inputs with
        | nil => simp
        | cons _ _ => rw [hdi] at hinp; cases hinp
      | cons i1 irest =>
        rw [hgi] at hinp
        cases hdi : h.inputs with
        | nil => rw [hdi] at hinp; cases hinp
        | cons j1 jrest =>
          rw [hdi] at hinp
          simp only [List.take_succ_cons, List.take_zero]
          exact List.Forall₂.cons (List.forall₂_cons.mp hinp).1 List.Forall₂.nil
  have hop_or_eval : ∀ (g : PEqualNP.CircuitLowerBounds.Gate),
      g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
        PEqualNP.CircuitLowerBounds.GateOp.or, PEqualNP.CircuitLowerBounds.GateOp.not} :
          Set PEqualNP.CircuitLowerBounds.GateOp) →
      (g.op.eval [true, false] = true ↔ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) := by
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with h | h | h
    · rw [h]; constructor <;> intro hc <;> simp [PEqualNP.CircuitLowerBounds.GateOp.eval] at hc
    · rw [h]; constructor <;> intro hc <;> simp [PEqualNP.CircuitLowerBounds.GateOp.eval]
    · rw [h]; constructor <;> intro hc <;> simp [PEqualNP.CircuitLowerBounds.GateOp.eval] at hc
  let evalVal (w : List Bool) (v : Bool ⊕ ℕ) : Bool :=
    match v with
    | Sum.inl b => b
    | Sum.inr u => w.getD u false
  let simGate (env : List (Bool ⊕ ℕ)) (nw : ℕ) (h : PEqualNP.CircuitLowerBounds.Gate) :
      (Bool ⊕ ℕ) × Option PEqualNP.CircuitLowerBounds.Gate :=
    let lk (j : ℕ) : Bool ⊕ ℕ := env.getD j (Sum.inl false)
    match h.op with
    | PEqualNP.CircuitLowerBounds.GateOp.and =>
      match h.inputs with
      | [] => (Sum.inl true, none)
      | [i] => (lk i, none)
      | [i, j] =>
        match lk i, lk j with
        | Sum.inl false, _ => (Sum.inl false, none)
        | _, Sum.inl false => (Sum.inl false, none)
        | Sum.inl true, v => (v, none)
        | v, Sum.inl true => (v, none)
        | Sum.inr u, Sum.inr v =>
          if u = v then (Sum.inr u, none)
          else (Sum.inr nw, some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [u, v]⟩)
      | _ => (Sum.inl false, none)
    | PEqualNP.CircuitLowerBounds.GateOp.or =>
      match h.inputs with
      | [] => (Sum.inl false, none)
      | [i] => (lk i, none)
      | [i, j] =>
        match lk i, lk j with
        | Sum.inl true, _ => (Sum.inl true, none)
        | _, Sum.inl true => (Sum.inl true, none)
        | Sum.inl false, v => (v, none)
        | v, Sum.inl false => (v, none)
        | Sum.inr u, Sum.inr v =>
          if u = v then (Sum.inr u, none)
          else (Sum.inr nw, some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [u, v]⟩)
      | _ => (Sum.inl false, none)
    | PEqualNP.CircuitLowerBounds.GateOp.not =>
      match h.inputs with
      | [] => (Sum.inl true, none)
      | i :: _ =>
        match lk i with
        | Sum.inl b => (Sum.inl (!b), none)
        | Sum.inr u => (Sum.inr nw, some ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [u]⟩)
    | _ => (Sum.inl false, none)
  let simStep (st : List (Bool ⊕ ℕ) × List PEqualNP.CircuitLowerBounds.Gate × List Bool)
      (h : PEqualNP.CircuitLowerBounds.Gate) :
      List (Bool ⊕ ℕ) × List PEqualNP.CircuitLowerBounds.Gate × List Bool :=
    let r := simGate st.1 (6 + st.2.1.length) h
    (st.1 ++ [r.1], st.2.1 ++ r.2.toList, st.2.2 ++ [r.2.isSome])
  have hsimGate_ok : ∀ (env : List (Bool ⊕ ℕ)) (nw : ℕ) (h : PEqualNP.CircuitLowerBounds.Gate),
      h.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
        PEqualNP.CircuitLowerBounds.GateOp.or, PEqualNP.CircuitLowerBounds.GateOp.not} :
          Set PEqualNP.CircuitLowerBounds.GateOp) →
      h.inputs.length ≤ 2 →
      (∀ g ∈ (simGate env nw h).2.toList,
        g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
          PEqualNP.CircuitLowerBounds.GateOp.or, PEqualNP.CircuitLowerBounds.GateOp.not} :
            Set PEqualNP.CircuitLowerBounds.GateOp) ∧ g.inputs.length ≤ 2) ∧
      ((∀ j u, env.getD j (Sum.inl false) = Sum.inr u → u < nw) →
        ∀ u, (simGate env nw h).1 = Sum.inr u →
          u < nw + (if (simGate env nw h).2.isSome then 1 else 0)) := by
    intro env nw h hop hlen
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with h_op | h_op | h_op
    · rcases hgi : h.inputs with _ | ⟨i, _ | ⟨j, _ | _⟩⟩
      · simp [simGate, h_op, hgi]
      · simp only [simGate, h_op, hgi, Option.toList_none, List.not_mem_nil, false_implies,
          implies_true, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, Nat.add_zero,
          true_and]
        intro hb u hu
        exact hb i u hu
      · simp only [simGate, h_op, hgi]
        cases hli : env.getD i (Sum.inl false) with
        | inl bi =>
          cases bi with
          | false => simp
          | true =>
            cases hlj : env.getD j (Sum.inl false) with
            | inl bj =>
              cases bj <;> simp
            | inr vj =>
              simp only [Option.toList_none, List.not_mem_nil, false_implies, implies_true,
                Option.isSome_none, Bool.false_eq_true, ↓reduceIte, Nat.add_zero, true_and]
              intro hb u hu
              cases hu
              exact hb j _ hlj
        | inr ui =>
          cases hlj : env.getD j (Sum.inl false) with
          | inl bj =>
            cases bj with
            | false => simp
            | true =>
              simp only [Option.toList_none, List.not_mem_nil, false_implies, implies_true,
                Option.isSome_none, Bool.false_eq_true, ↓reduceIte, Nat.add_zero, true_and]
              intro hb u hu
              cases hu
              exact hb i _ hli
          | inr vj =>
            by_cases heq : ui = vj
            · simp only [heq, ↓reduceIte, Option.toList_none, List.not_mem_nil, false_implies,
                implies_true, Option.isSome_none, Bool.false_eq_true, Nat.add_zero, true_and]
              intro hb u hu
              cases hu
              exact hb j _ hlj
            · simp only [heq, ↓reduceIte, Option.toList_some, List.mem_singleton, forall_eq,
                Set.mem_insert_iff, Set.mem_singleton_iff, true_or, List.length_cons,
                List.length_nil, Nat.reduceAdd, Nat.le_refl, and_self, Option.isSome_some,
                true_and]
              intro _ u hu
              cases hu
              omega
      · simp [hgi] at hlen
    · rcases hgi : h.inputs with _ | ⟨i, _ | ⟨j, _ | _⟩⟩
      · simp [simGate, h_op, hgi]
      · simp only [simGate, h_op, hgi, Option.toList_none, List.not_mem_nil, false_implies,
          implies_true, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, Nat.add_zero,
          true_and]
        intro hb u hu
        exact hb i u hu
      · simp only [simGate, h_op, hgi]
        cases hli : env.getD i (Sum.inl false) with
        | inl bi =>
          cases bi with
          | true => simp
          | false =>
            cases hlj : env.getD j (Sum.inl false) with
            | inl bj =>
              cases bj <;> simp
            | inr vj =>
              simp only [Option.toList_none, List.not_mem_nil, false_implies, implies_true,
                Option.isSome_none, Bool.false_eq_true, ↓reduceIte, Nat.add_zero, true_and]
              intro hb u hu
              cases hu
              exact hb j _ hlj
        | inr ui =>
          cases hlj : env.getD j (Sum.inl false) with
          | inl bj =>
            cases bj with
            | true => simp
            | false =>
              simp only [Option.toList_none, List.not_mem_nil, false_implies, implies_true,
                Option.isSome_none, Bool.false_eq_true, ↓reduceIte, Nat.add_zero, true_and]
              intro hb u hu
              cases hu
              exact hb i _ hli
          | inr vj =>
            by_cases heq : ui = vj
            · simp only [heq, ↓reduceIte, Option.toList_none, List.not_mem_nil, false_implies,
                implies_true, Option.isSome_none, Bool.false_eq_true, Nat.add_zero, true_and]
              intro hb u hu
              cases hu
              exact hb j _ hlj
            · simp only [heq, ↓reduceIte, Option.toList_some, List.mem_singleton, forall_eq,
                Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true, List.length_cons,
                List.length_nil, Nat.reduceAdd, Nat.le_refl, and_self, Option.isSome_some,
                true_and]
              intro _ u hu
              cases hu
              omega
      · simp [hgi] at hlen
    · rcases hgi : h.inputs with _ | ⟨i, rest⟩
      · simp [simGate, h_op, hgi]
      · simp only [simGate, h_op, hgi]
        cases hli : env.getD i (Sum.inl false) with
        | inl bi => simp [hli]
        | inr ui =>
          simp only [hli, Option.toList_some, List.mem_singleton, forall_eq, Set.mem_insert_iff,
            Set.mem_singleton_iff, or_true, List.length_cons, List.length_nil, Nat.reduceLeDiff,
            and_self, Option.isSome_some, ↓reduceIte, true_and]
          intro _ u hu
          cases hu
          omega
  have hsimGate_sem : ∀ (env : List (Bool ⊕ ℕ)) (h : PEqualNP.CircuitLowerBounds.Gate)
      (wD wE : List Bool),
      h.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
        PEqualNP.CircuitLowerBounds.GateOp.or, PEqualNP.CircuitLowerBounds.GateOp.not} :
          Set PEqualNP.CircuitLowerBounds.GateOp) →
      h.inputs.length ≤ 2 →
      (∀ j, wD.getD j false = evalVal wE (env.getD j (Sum.inl false))) →
      (∀ j u, env.getD j (Sum.inl false) = Sum.inr u → u < wE.length) →
      let r := simGate env wE.length h
      let wE' := r.2.toList.foldl stepW wE
      h.op.eval (h.inputs.map fun i => wD.getD i false) = evalVal wE' r.1 ∧
      ∀ j, wD.getD j false = evalVal wE' (env.getD j (Sum.inl false)) := by
    intro env h wD wE hop hlen hagree hbound
    dsimp only
    have hpres : ∀ j, wD.getD j false =
        evalVal ((simGate env wE.length h).2.toList.foldl stepW wE)
          (env.getD j (Sum.inl false)) := by
      intro j
      rw [hagree j]
      cases hej : env.getD j (Sum.inl false) with
      | inl b => rfl
      | inr u =>
        have hu : u < wE.length := hbound j u hej
        exact (hstep_lt (simGate env wE.length h).2.toList wE u hu).symm
    refine ⟨?_, hpres⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with h_op | h_op | h_op
    · rcases hgi : h.inputs with _ | ⟨i, _ | ⟨j, _ | _⟩⟩
      · simp [simGate, h_op, hgi, evalVal, PEqualNP.CircuitLowerBounds.GateOp.eval]
      · have hi := hagree i
        simp only [simGate, h_op, hgi, Option.toList_none, List.foldl_nil,
          PEqualNP.CircuitLowerBounds.GateOp.eval, List.map_cons, List.map_nil, List.all_cons,
          List.all_nil, id_eq, Bool.and_true]
        exact hi
      · have hi0 := hagree i
        have hj0 := hagree j
        simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.map_cons, List.map_nil,
          List.all_cons, List.all_nil, id_eq, Bool.and_true, h_op, hgi, simGate]
        cases hli : env.getD i (Sum.inl false) with
        | inl bi =>
          rw [hli] at hi0
          cases bi with
          | false => rw [hi0]; rfl
          | true =>
            cases hlj : env.getD j (Sum.inl false) with
            | inl bj =>
              rw [hlj] at hj0
              cases bj <;> rw [hi0, hj0] <;> rfl
            | inr vj =>
              rw [hlj] at hj0
              rw [hi0, hj0]; rfl
        | inr ui =>
          rw [hli] at hi0
          cases hlj : env.getD j (Sum.inl false) with
          | inl bj =>
            rw [hlj] at hj0
            cases bj <;> rw [hi0, hj0] <;> simp [evalVal]
          | inr vj =>
            rw [hlj] at hj0
            by_cases heq : ui = vj
            · subst heq
              rw [hi0, hj0]
              simp [evalVal]
            · simp only [heq, ↓reduceIte, Option.toList_some, List.foldl_cons, List.foldl_nil]
              rw [hi0, hj0]
              simp [stepW, evalVal, PEqualNP.CircuitLowerBounds.GateOp.eval]
      · simp [hgi] at hlen
    · rcases hgi : h.inputs with _ | ⟨i, _ | ⟨j, _ | _⟩⟩
      · simp [simGate, h_op, hgi, evalVal, PEqualNP.CircuitLowerBounds.GateOp.eval]
      · have hi := hagree i
        simp only [simGate, h_op, hgi, Option.toList_none, List.foldl_nil,
          PEqualNP.CircuitLowerBounds.GateOp.eval, List.map_cons, List.map_nil, List.any_cons,
          List.any_nil, id_eq, Bool.or_false]
        exact hi
      · have hi0 := hagree i
        have hj0 := hagree j
        simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.map_cons, List.map_nil,
          List.any_cons, List.any_nil, id_eq, Bool.or_false, h_op, hgi, simGate]
        cases hli : env.getD i (Sum.inl false) with
        | inl bi =>
          rw [hli] at hi0
          cases bi with
          | true => rw [hi0]; rfl
          | false =>
            cases hlj : env.getD j (Sum.inl false) with
            | inl bj =>
              rw [hlj] at hj0
              cases bj <;> rw [hi0, hj0] <;> rfl
            | inr vj =>
              rw [hlj] at hj0
              rw [hi0, hj0]; rfl
        | inr ui =>
          rw [hli] at hi0
          cases hlj : env.getD j (Sum.inl false) with
          | inl bj =>
            rw [hlj] at hj0
            cases bj <;> rw [hi0, hj0] <;> simp [evalVal]
          | inr vj =>
            rw [hlj] at hj0
            by_cases heq : ui = vj
            · subst heq
              rw [hi0, hj0]
              simp [evalVal]
            · simp only [heq, ↓reduceIte, Option.toList_some, List.foldl_cons, List.foldl_nil]
              rw [hi0, hj0]
              simp [stepW, evalVal, PEqualNP.CircuitLowerBounds.GateOp.eval]
      · simp [hgi] at hlen
    · rcases hgi : h.inputs with _ | ⟨i, rest⟩
      · simp [simGate, h_op, hgi, evalVal, PEqualNP.CircuitLowerBounds.GateOp.eval]
      · have hi0 := hagree i
        simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.map_cons, List.headD_cons, h_op,
          hgi, simGate]
        cases hli : env.getD i (Sum.inl false) with
        | inl bi =>
          rw [hli] at hi0
          rw [hi0]
        | inr ui =>
          rw [hli] at hi0
          simp only [Option.toList_some, List.foldl_cons, List.foldl_nil]
          rw [hi0]
          simp [stepW, evalVal, PEqualNP.CircuitLowerBounds.GateOp.eval]
  let env0 : List (Bool ⊕ ℕ) :=
    [Sum.inl true, Sum.inr 0, Sum.inr 1, Sum.inl false, Sum.inr 2, Sum.inr 3, Sum.inr 4, Sum.inr 5]
  let st0 : List (Bool ⊕ ℕ) × List PEqualNP.CircuitLowerBounds.Gate × List Bool := (env0, [], [])
  let stFin := D.gates.foldl simStep st0
  have hsim_fold : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate)
      (st : List (Bool ⊕ ℕ) × List PEqualNP.CircuitLowerBounds.Gate × List Bool),
      (∀ h ∈ gs, h.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
        PEqualNP.CircuitLowerBounds.GateOp.or, PEqualNP.CircuitLowerBounds.GateOp.not} :
          Set PEqualNP.CircuitLowerBounds.GateOp) ∧ h.inputs.length ≤ 2) →
      (∀ g ∈ st.2.1, g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
        PEqualNP.CircuitLowerBounds.GateOp.or, PEqualNP.CircuitLowerBounds.GateOp.not} :
          Set PEqualNP.CircuitLowerBounds.GateOp) ∧ g.inputs.length ≤ 2) →
      (∀ j u, st.1.getD j (Sum.inl false) = Sum.inr u → u < 6 + st.2.1.length) →
      let st' := gs.foldl simStep st
      st'.1.length = st.1.length + gs.length ∧
      st'.2.2.length = st.2.2.length + gs.length ∧
      st'.2.1.length + (st'.2.2.drop st.2.2.length).count false = st.2.1.length + gs.length ∧
      (∀ g ∈ st'.2.1, g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
        PEqualNP.CircuitLowerBounds.GateOp.or, PEqualNP.CircuitLowerBounds.GateOp.not} :
          Set PEqualNP.CircuitLowerBounds.GateOp) ∧ g.inputs.length ≤ 2) ∧
      (∀ j u, st'.1.getD j (Sum.inl false) = Sum.inr u → u < 6 + st'.2.1.length) ∧
      (∀ (y : Fin 6 → Bool) (wD : List Bool),
        wD.length = st.1.length →
        (∀ j, wD.getD j false = evalVal (st.2.1.foldl stepW (List.ofFn y))
          (st.1.getD j (Sum.inl false))) →
        ∀ j, (gs.foldl stepW wD).getD j false =
          evalVal (st'.2.1.foldl stepW (List.ofFn y)) (st'.1.getD j (Sum.inl false))) := by
    intro gs
    induction gs with
    | nil =>
      intro st _ hacc hb
      refine ⟨rfl, rfl, by simp, hacc, hb, ?_⟩
      intro y wD _ hwD j
      exact hwD j
    | cons h gs ih =>
      intro st hgs hacc hb
      have hh := hgs h (by simp)
      have hgo := hsimGate_ok st.1 (6 + st.2.1.length) h hh.1 hh.2
      let st1 := simStep st h
      have hlen1 : st1.1.length = st.1.length + 1 := by simp [st1, simStep]
      have hlen2 : st1.2.2.length = st.2.2.length + 1 := by simp [st1, simStep]
      have hacc1 : ∀ g ∈ st1.2.1,
          g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
            PEqualNP.CircuitLowerBounds.GateOp.or, PEqualNP.CircuitLowerBounds.GateOp.not} :
              Set PEqualNP.CircuitLowerBounds.GateOp) ∧ g.inputs.length ≤ 2 := by
        intro g hg
        simp only [st1, simStep, List.mem_append] at hg
        rcases hg with hg | hg
        · exact hacc g hg
        · exact hgo.1 g hg
      have hb1 : ∀ j u, st1.1.getD j (Sum.inl false) = Sum.inr u → u < 6 + st1.2.1.length := by
        intro j u hj
        simp only [st1, simStep] at hj ⊢
        by_cases hjlt : j < st.1.length
        · rw [List.getD_append _ _ _ _ hjlt] at hj
          have := hb j u hj
          simp only [List.length_append]
          omega
        · by_cases hjeq : j = st.1.length
          · subst hjeq
            simp only [List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self,
              List.getD_cons_zero] at hj
            have hu := hgo.2 hb u hj
            have hopt : (if (simGate st.1 (6 + st.2.1.length) h).2.isSome then 1 else 0) =
                (simGate st.1 (6 + st.2.1.length) h).2.toList.length := by
              cases (simGate st.1 (6 + st.2.1.length) h).2 <;> simp
            rw [List.length_append, ← hopt]
            omega
          · rw [List.getD_eq_default _ _ (by simp; omega)] at hj
            cases hj
      have hrec := ih st1 (fun h' hh' => hgs h' (List.mem_cons_of_mem _ hh')) hacc1 hb1
      obtain ⟨r1, r2, r3, r4, r5, r6⟩ := hrec
      refine ⟨?_, ?_, ?_, r4, r5, ?_⟩
      · rw [List.foldl_cons]; change (gs.foldl simStep st1).1.length = _; rw [r1, hlen1]; simp; omega
      · rw [List.foldl_cons]; change (gs.foldl simStep st1).2.2.length = _; rw [r2, hlen2]; simp; omega
      · rw [List.foldl_cons]
        change (gs.foldl simStep st1).2.1.length +
          ((gs.foldl simStep st1).2.2.drop st.2.2.length).count false = _
        have hdrop : (gs.foldl simStep st1).2.2.drop st.2.2.length =
            (simGate st.1 (6 + st.2.1.length) h).2.isSome ::
              ((gs.foldl simStep st1).2.2.drop st1.2.2.length) := by
          have hpref : ∀ (ks : List PEqualNP.CircuitLowerBounds.Gate)
              (s : List (Bool ⊕ ℕ) × List PEqualNP.CircuitLowerBounds.Gate × List Bool),
              ∃ ext, (ks.foldl simStep s).2.2 = s.2.2 ++ ext := by
            intro ks
            induction ks with
            | nil => intro s; exact ⟨[], by simp⟩
            | cons k ks ihk =>
              intro s
              rw [List.foldl_cons]
              obtain ⟨ext, hext⟩ := ihk (simStep s k)
              refine ⟨[(simGate s.1 (6 + s.2.1.length) k).2.isSome] ++ ext, ?_⟩
              rw [hext]; simp [simStep, List.append_assoc]
          obtain ⟨ext, hext⟩ := hpref gs st1
          rw [hext]
          rw [List.drop_append_of_le_length (le_refl _), List.drop_eq_nil_of_le (le_refl _),
            List.nil_append]
          simp only [st1, simStep, List.append_assoc]
          rw [List.drop_append_of_le_length (le_refl _), List.drop_eq_nil_of_le (le_refl _),
            List.nil_append]
          rfl
        rw [hdrop]
        have hc_split : ∀ (b : Bool) (l : List Bool),
            (b :: l).count false = (if b == false then 1 else 0) + l.count false := by
          intro b l
          cases b <;> simp <;> omega
        rw [hc_split]
        have h1len : st1.2.1.length = st.2.1.length +
            (if (simGate st.1 (6 + st.2.1.length) h).2.isSome then 1 else 0) := by
          simp only [st1, simStep, List.length_append]
          cases (simGate st.1 (6 + st.2.1.length) h).2 <;> simp
        cases hsome : (simGate st.1 (6 + st.2.1.length) h).2 <;>
          simp [hsome, hlen2] at r3 h1len ⊢ <;> omega
      · intro y wD hwDl hwD j
        rw [List.foldl_cons, List.foldl_cons]
        apply r6 y (stepW wD h) (by simp [stepW, hwDl, hlen1])
        intro k
        let wE := st.2.1.foldl stepW (List.ofFn y)
        have hwEl : wE.length = 6 + st.2.1.length := by
          simp [wE, hstep_len]
        have hsem := hsimGate_sem st.1 h wD wE hh.1 hh.2 hwD (by
          intro j' u hu; rw [hwEl]; exact hb j' u hu)
        rw [hwEl] at hsem
        have hwE1 : st1.2.1.foldl stepW (List.ofFn y) =
            (simGate st.1 (6 + st.2.1.length) h).2.toList.foldl stepW wE := by
          dsimp only [st1, simStep, wE]
          rw [List.foldl_append]
        rw [hwE1]
        by_cases hklt : k < wD.length
        · change (wD ++ [h.op.eval (h.inputs.map fun i => wD.getD i false)]).getD k false = _
          rw [List.getD_append _ _ _ _ hklt]
          have hst1k : st1.1.getD k (Sum.inl false) = st.1.getD k (Sum.inl false) := by
            simp only [st1, simStep]
            exact List.getD_append _ _ _ _ (by omega)
          rw [hst1k]
          exact hsem.2 k
        · by_cases hkeq : k = wD.length
          · subst hkeq
            have hst1k : st1.1.getD wD.length (Sum.inl false) =
                (simGate st.1 (6 + st.2.1.length) h).1 := by
              rw [hwDl]
              simp only [st1, simStep, List.getD_eq_getElem?_getD,
                List.getElem?_append_right (le_refl _), Nat.sub_self, List.getElem?_cons_zero,
                Option.getD_some]
            rw [hst1k]
            simpa [stepW] using hsem.1
          · change (wD ++ [h.op.eval (h.inputs.map fun i => wD.getD i false)]).getD k false = _
            rw [List.getD_eq_default _ _ (by simp; omega)]
            have hst1k : st1.1.getD k (Sum.inl false) = Sum.inl false := by
              apply List.getD_eq_default
              simp only [st1, simStep, List.length_append, List.length_singleton]
              omega
            rw [hst1k]
  have hstFin := hsim_fold D.gates st0 hfanD (by simp [st0]) (by
    intro j u hj
    rcases (by omega : j < 8 ∨ 8 ≤ j) with hjlt | hjge
    · interval_cases j <;> simp [st0, env0] at hj <;> omega
    · rw [List.getD_eq_default _ _ (by simp [st0, env0]; omega)] at hj
      cases hj)
  have hstFin_len1 : stFin.1.length = 19 := by simpa [st0, env0, hlenD] using hstFin.1
  have hstFin_len2 : stFin.2.2.length = 11 := by simpa [st0, hlenD] using hstFin.2.1
  have hstFin_cnt : stFin.2.1.length + stFin.2.2.count false = 11 := by
    simpa [st0, hlenD] using hstFin.2.2.1
  have hstFin_fan : PEqualNP.MetaComplexity.FanInTwo ⟨stFin.2.1, 0⟩ := hstFin.2.2.2.1
  have hstFin_sem : ∀ (y : Fin 6 → Bool) (j : ℕ),
      let row : Fin 7 → Bool := fun i => ([y 0, y 1, false, y 2, y 3, y 4, y 5]).getD i.val false
      (D.wires (true :: List.ofFn row)).getD j false =
        evalVal (stFin.2.1.foldl stepW (List.ofFn y)) (stFin.1.getD j (Sum.inl false)) := by
    intro y j row
    change (D.gates.foldl stepW (true :: List.ofFn row)).getD j false = _
    apply hstFin.2.2.2.2.2 y (true :: List.ofFn row) (by simp [st0, env0])
    intro k
    by_cases hk : k < 8
    · interval_cases k <;> simp [st0, env0, evalVal, row]
    · have hlen0 : st0.1.length = 8 := rfl
      rw [List.getD_eq_default _ _ (by simp; omega),
        List.getD_eq_default (st0.1) _ (by rw [hlen0]; omega)]
  have hrow_eq : ∀ (y : Fin 6 → Bool),
      let row : Fin 7 → Bool := fun i => ([y 0, y 1, false, y 2, y 3, y 4, y 5]).getD i.val false
      (f row || row 2) = c6 y := by
    intro y row
    change (([1, 12, 4, 15, 26, 35, 46, 36] : List ℕ).any (fun e =>
      row (Fin.ofNat 7 (e / 10)) && row (Fin.ofNat 7 (e % 10))) || row 2) = c6 y
    simp only [List.any_cons, List.any_nil, Bool.or_false]
    change (((row 0 && row 1) || ((row 1 && row 2) || ((row 0 && row 4) ||
      ((row 1 && row 5) || ((row 2 && row 6) || ((row 3 && row 5) ||
      ((row 4 && row 6) || (row 3 && row 6)))))))) || row 2) = c6 y
    have hr0 : row 0 = y 0 := rfl
    have hr1 : row 1 = y 1 := rfl
    have hr2 : row 2 = false := rfl
    have hr3 : row 3 = y 2 := rfl
    have hr4 : row 4 = y 3 := rfl
    have hr5 : row 5 = y 4 := rfl
    have hr6 : row 6 = y 5 := rfl
    rw [hr0, hr1, hr2, hr3, hr4, hr5, hr6]
    simp only [c6]
    cases y 0 <;> cases y 1 <;> cases y 2 <;> cases y 3 <;> cases y 4 <;> cases y 5 <;> rfl
  have houtE : ∃ outE : ℕ, stFin.1.getD (C.output + 1) (Sum.inl false) = Sum.inr outE := by
    cases ho : stFin.1.getD (C.output + 1) (Sum.inl false) with
    | inr u => exact ⟨u, rfl⟩
    | inl b =>
      cases b with
      | false =>
        let y : Fin 6 → Bool := fun i => decide (i = 0 ∨ i = 1)
        let row : Fin 7 → Bool := fun i => ([y 0, y 1, false, y 2, y 3, y 4, y 5]).getD i.val false
        have hy := hD row
        rw [hrow_eq y, hstFin_sem y (C.output + 1), ho] at hy
        have hc6 : c6 y = true := by decide
        rw [hc6] at hy
        cases hy
      | true =>
        let y : Fin 6 → Bool := fun _ => false
        let row : Fin 7 → Bool := fun i => ([y 0, y 1, false, y 2, y 3, y 4, y 5]).getD i.val false
        have hy := hD row
        rw [hrow_eq y, hstFin_sem y (C.output + 1), ho] at hy
        have hc6 : c6 y = false := by decide
        rw [hc6] at hy
        cases hy
  obtain ⟨outE, houtE_eq⟩ := houtE
  have h8le : 8 ≤ stFin.2.1.length := by
    by_contra hlt8
    apply h1
    refine ⟨⟨stFin.2.1, outE⟩, hstFin_fan, by change stFin.2.1.length ≤ 7; omega, ?_⟩
    intro y
    let row : Fin 7 → Bool := fun i => ([y 0, y 1, false, y 2, y 3, y 4, y 5]).getD i.val false
    have hy := hD row
    rw [hrow_eq y, hstFin_sem y (C.output + 1), houtE_eq] at hy
    exact hy
  have hdrop_le3 : stFin.2.2.count false ≤ 3 := by omega
  have hlocal : ∀ (k : ℕ) (hk : k < 11),
      let stk := (D.gates.take k).foldl simStep st0
      let hk_g := D.gates[k]'(by omega)
      stFin.1.getD (8 + k) (Sum.inl false) = (simGate stk.1 (6 + stk.2.1.length) hk_g).1 ∧
      stFin.2.2.getD k true = (simGate stk.1 (6 + stk.2.1.length) hk_g).2.isSome ∧
      stk.1.length = 8 + k ∧
      (∀ i < 8 + k, stk.1.getD i (Sum.inl false) = stFin.1.getD i (Sum.inl false)) := by
    intro k hk
    let pre := D.gates.take k
    let hk_g := D.gates[k]'(by omega)
    let post := D.gates.drop (k + 1)
    have hsplit : D.gates = pre ++ hk_g :: post := by
      have htk := List.take_append_drop k D.gates
      have hdrop : D.gates.drop k = hk_g :: post := by
        simpa [hk_g, post] using List.drop_eq_getElem_cons (by omega : k < D.gates.length)
      rw [← htk, hdrop]
    have hpref : ∀ (ks : List PEqualNP.CircuitLowerBounds.Gate)
        (s : List (Bool ⊕ ℕ) × List PEqualNP.CircuitLowerBounds.Gate × List Bool),
        ∃ e1 e2, (ks.foldl simStep s).1 = s.1 ++ e1 ∧ (ks.foldl simStep s).2.2 = s.2.2 ++ e2 := by
      intro ks
      induction ks with
      | nil => intro s; exact ⟨[], [], by simp, by simp⟩
      | cons g ks ihk =>
        intro s
        rw [List.foldl_cons]
        obtain ⟨e1, e2, h1', h2'⟩ := ihk (simStep s g)
        refine ⟨(simGate s.1 (6 + s.2.1.length) g).1 :: e1,
          (simGate s.1 (6 + s.2.1.length) g).2.isSome :: e2, ?_, ?_⟩
        · rw [h1']; simp [simStep, List.append_assoc]
        · rw [h2']; simp [simStep, List.append_assoc]
    have hstk := hsim_fold pre st0 (fun h hh => hfanD h (List.mem_of_mem_take hh))
      (by simp [st0]) (by
        intro j u hj
        rcases (by omega : j < 8 ∨ 8 ≤ j) with hjlt | hjge
        · interval_cases j <;> simp [st0, env0] at hj <;> omega
        · rw [List.getD_eq_default _ _ (by simp [st0, env0]; omega)] at hj
          cases hj)
    let stk := pre.foldl simStep st0
    have hpre_len : pre.length = k := by simp [pre, List.length_take, hlenD]; omega
    have hstk_len1 : stk.1.length = 8 + k := by simpa [st0, env0, hpre_len] using hstk.1
    have hstk_len2 : stk.2.2.length = k := by simpa [st0, hpre_len] using hstk.2.1
    obtain ⟨e1, e2, he1, he2⟩ := hpref post (simStep stk hk_g)
    have hfin_eq1 : stFin.1 = stk.1 ++ ((simGate stk.1 (6 + stk.2.1.length) hk_g).1 :: e1) := by
      change (D.gates.foldl simStep st0).1 = _
      rw [hsplit, List.foldl_append, List.foldl_cons, he1]
      simp [simStep, List.append_assoc]
    have hfin_eq2 : stFin.2.2 = stk.2.2 ++
        ((simGate stk.1 (6 + stk.2.1.length) hk_g).2.isSome :: e2) := by
      change (D.gates.foldl simStep st0).2.2 = _
      rw [hsplit, List.foldl_append, List.foldl_cons, he2]
      simp [simStep, List.append_assoc]
    refine ⟨?_, ?_, hstk_len1, ?_⟩
    · rw [hfin_eq1, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hstk_len1,
        Nat.sub_self]
      rfl
    · rw [hfin_eq2, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hstk_len2,
        Nat.sub_self]
      rfl
    · intro i hi
      rw [hfin_eq1, List.getD_append _ _ _ _ (by omega)]
  have hconst_drop : ∀ (k : ℕ) (hk : k < 11),
      (∃ j ∈ eff (D.gates[k]'(by omega)), ∃ b : Bool,
        ((D.gates.take k).foldl simStep st0).1.getD j (Sum.inl false) = Sum.inl b) →
      stFin.2.2.getD k true = false := by
    intro k hk ⟨j, hj, b, hjb⟩
    have hl := hlocal k hk
    rw [hl.2.1]
    set stk := (D.gates.take k).foldl simStep st0
    set hk_g := D.gates[k]'(by omega)
    have hfk := hfanD hk_g (List.getElem_mem (by omega))
    have hfk1 := hfk.1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hfk1
    rcases hfk1 with hop | hop | hop
    · have hj' : j ∈ hk_g.inputs := by simpa [eff, hop] using hj
      rcases hgi : hk_g.inputs with _ | ⟨i1, _ | ⟨i2, _ | _⟩⟩
      · simp [hgi] at hj'
      · simp [simGate, hop, hgi]
      · rw [hgi] at hj'
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hj'
        simp only [simGate, hop, hgi]
        rcases hj' with rfl | rfl
        · rw [hjb]
          cases stk.1.getD i2 (Sum.inl false) with
          | inl b2 => cases b <;> cases b2 <;> rfl
          | inr _ => cases b <;> rfl
        · rw [hjb]
          cases stk.1.getD i1 (Sum.inl false) with
          | inl b1 => cases b1 <;> cases b <;> rfl
          | inr _ => cases b <;> rfl
      · have := hfk.2; simp [hgi] at this
    · have hj' : j ∈ hk_g.inputs := by simpa [eff, hop] using hj
      rcases hgi : hk_g.inputs with _ | ⟨i1, _ | ⟨i2, _ | _⟩⟩
      · simp [hgi] at hj'
      · simp [simGate, hop, hgi]
      · rw [hgi] at hj'
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hj'
        simp only [simGate, hop, hgi]
        rcases hj' with rfl | rfl
        · rw [hjb]
          cases stk.1.getD i2 (Sum.inl false) with
          | inl b2 => cases b <;> cases b2 <;> rfl
          | inr _ => cases b <;> rfl
        · rw [hjb]
          cases stk.1.getD i1 (Sum.inl false) with
          | inl b1 => cases b1 <;> cases b <;> rfl
          | inr _ => cases b <;> rfl
      · have := hfk.2; simp [hgi] at this
    · have hj' : j ∈ hk_g.inputs.take 1 := by simpa [eff, hop] using hj
      rcases hgi : hk_g.inputs with _ | ⟨i1, rest⟩
      · simp [hgi] at hj'
      · simp only [hgi, List.take_succ_cons, List.take_zero, List.mem_singleton] at hj'
        simp only [simGate, hop, hgi, ← hj', hjb]
        rfl
  have hstk03 : ∀ (k : ℕ) (hk : k < 11),
      ((D.gates.take k).foldl simStep st0).1.getD 0 (Sum.inl false) = Sum.inl true ∧
      ((D.gates.take k).foldl simStep st0).1.getD 3 (Sum.inl false) = Sum.inl false := by
    intro k hk
    have hl := hlocal k hk
    have h0 := hl.2.2.2 0 (by omega)
    have h3 := hl.2.2.2 3 (by omega)
    have hpref : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate)
        (s : List (Bool ⊕ ℕ) × List PEqualNP.CircuitLowerBounds.Gate × List Bool),
        ∃ e1, (gs.foldl simStep s).1 = s.1 ++ e1 := by
      intro gs
      induction gs with
      | nil => intro s; exact ⟨[], by simp⟩
      | cons g gs ihg =>
        intro s
        rw [List.foldl_cons]
        obtain ⟨e1, he1⟩ := ihg (simStep s g)
        refine ⟨(simGate s.1 (6 + s.2.1.length) g).1 :: e1, ?_⟩
        rw [he1]; simp [simStep, List.append_assoc]
    obtain ⟨e1, he1⟩ := hpref D.gates st0
    have hf0 : stFin.1.getD 0 (Sum.inl false) = Sum.inl true := by
      change (D.gates.foldl simStep st0).1.getD 0 (Sum.inl false) = _
      rw [he1, List.getD_append _ _ _ _ (by simp [st0, env0])]
      rfl
    have hf3 : stFin.1.getD 3 (Sum.inl false) = Sum.inl false := by
      change (D.gates.foldl simStep st0).1.getD 3 (Sum.inl false) = _
      rw [he1, List.getD_append _ _ _ _ (by simp [st0, env0])]
      rfl
    exact ⟨h0.trans hf0, h3.trans hf3⟩
  let x2only : Fin 7 → Bool := fun i => decide (i = 2)
  let wC : List Bool := C.wires (List.ofFn x2only)
  let wD : List Bool := D.wires (true :: List.ofFn x2only)
  have hwC_eval : C.eval (List.ofFn x2only) = false := by
    change PEqualNP.MetaComplexity.circuitFun 7 C x2only = false
    rw [hfun]
    decide
  have hwD_eval : wD.getD (C.output + 1) false = true := by
    rw [show wD = D.wires (true :: List.ofFn x2only) from rfl, hD x2only]
    decide
  have hout_range : 7 ≤ C.output ∧ C.output < 18 := by
    constructor
    · by_contra hlt7
      have ho7 : C.output < 7 := by omega
      have hc1 : C.eval (List.ofFn x2only) = (List.ofFn x2only).getD C.output false :=
        hstep_lt C.gates (List.ofFn x2only) C.output (by simp [ho7])
      have hd1 : wD.getD (C.output + 1) false =
          (true :: List.ofFn x2only).getD (C.output + 1) false :=
        hstep_lt D.gates (true :: List.ofFn x2only) (C.output + 1) (by simp; omega)
      have heq : (true :: List.ofFn x2only).getD (C.output + 1) false =
          (List.ofFn x2only).getD C.output false := by simp
      rw [heq, ← hc1, hwC_eval] at hd1
      rw [hd1] at hwD_eval
      cases hwD_eval
    · by_contra hge18
      have hd1 : wD.getD (C.output + 1) false = false := by
        apply List.getD_eq_default
        change (D.gates.foldl stepW (true :: List.ofFn x2only)).length ≤ C.output + 1
        rw [hstep_len]
        simp [hlenD]
        omega
      rw [hd1] at hwD_eval
      cases hwD_eval
  let diff (k : ℕ) : Prop :=
    k < 11 ∧ wC.getD (7 + k) false ≠ wD.getD (8 + k) false
  have hex_diff : ∃ k, diff k := by
    refine ⟨C.output - 7, by omega, ?_⟩
    rw [show 7 + (C.output - 7) = C.output by omega,
      show 8 + (C.output - 7) = C.output + 1 by omega]
    change C.eval (List.ofFn x2only) ≠ wD.getD (C.output + 1) false
    rw [hwC_eval, hwD_eval]
    decide
  let kstar := Nat.find hex_diff
  have hkstar_spec : diff kstar := Nat.find_spec hex_diff
  have hkstar_lt : kstar < 11 := hkstar_spec.1
  have hkstar_min : ∀ m < kstar, ¬ diff m := fun m hm => Nat.find_min hex_diff hm
  have hpre_agree_at : ∀ (k : ℕ) (hk : k < 11) (bad : ℕ)
      (hagree : ∀ i < 7 + k, i ≠ bad → wC.getD i false = wD.getD (i + 1) false)
      (hno0 : 0 ∉ eff (D.gates[k]'(by omega)))
      (hnobad : bad < 7 + k → bad + 1 ∉ eff (D.gates[k]'(by omega))),
      wC.getD (7 + k) false = wD.getD (8 + k) false := by
    intro k hk bad hagree hno0 hnobad
    let gk := C.gates[k]'(by omega)
    let hk_g := D.gates[k]'(by omega)
    have hfk := hfan_mem k hk
    obtain ⟨hop, hinp⟩ := hedits_get k hk
    have hfkD : hk_g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
        PEqualNP.CircuitLowerBounds.GateOp.or, PEqualNP.CircuitLowerBounds.GateOp.not} :
          Set PEqualNP.CircuitLowerBounds.GateOp) := hop ▸ hfk.1
    let wC_pre := (C.gates.take k).foldl stepW (List.ofFn x2only)
    let wD_pre := (D.gates.take k).foldl stepW (true :: List.ofFn x2only)
    have hc_val : wC.getD (7 + k) false =
        gk.op.eval ((eff gk).map fun i => wC_pre.getD i false) := by
      have h1' := hstep_gate C.gates (List.ofFn x2only) k (by omega)
      change (C.gates.foldl stepW (List.ofFn x2only)).getD (7 + k) false = _
      rw [show 7 + k = (List.ofFn x2only).length + k by simp, h1']
      exact heval_eff gk _ hfk.1
    have hd_val : wD.getD (8 + k) false =
        hk_g.op.eval ((eff hk_g).map fun j => wD_pre.getD j false) := by
      have h1' := hstep_gate D.gates (true :: List.ofFn x2only) k (by omega)
      change (D.gates.foldl stepW (true :: List.ofFn x2only)).getD (8 + k) false = _
      rw [show 8 + k = (true :: List.ofFn x2only).length + k by simp, h1']
      exact heval_eff hk_g _ hfkD
    have heff_rel := heff_rel_of gk hk_g hfk.1 hop hinp
    have hmap_aux : ∀ (l1 l2 : List ℕ),
        List.Forall₂ (fun i j => j = i + 1 ∨ j = 0 ∧ (i = a ∨ i = b)) l1 l2 →
        0 ∉ l2 → (bad < 7 + k → bad + 1 ∉ l2) →
        l1.map (fun i => wC_pre.getD i false) = l2.map (fun j => wD_pre.getD j false) := by
      intro l1 l2 hrel hl0 hlbad
      induction hrel with
      | nil => rfl
      | @cons i j is js hij _ ih =>
        have hj0 : j ≠ 0 := fun h0 => hl0 (h0 ▸ List.mem_cons_self)
        have hji : j = i + 1 := by
          rcases hij with rfl | ⟨h0, _⟩
          · rfl
          · exact (hj0 h0).elim
        have hpt : wC_pre.getD i false = wD_pre.getD j false := by
          rw [hji]
          by_cases hilt : i < 7 + k
          · have hibad : i ≠ bad := by
              intro h0
              have hjbad : j = bad + 1 := by omega
              exact hlbad (by omega) (hjbad ▸ List.mem_cons_self)
            have hpreC : wC_pre.getD i false = wC.getD i false := by
              have hlen_pre : (C.gates.take k).length = k := by
                simp [List.length_take, hlenC]; omega
              have hlt' := hstep_lt (C.gates.drop k) wC_pre i (by
                rw [hstep_len]; simp [hlen_pre, hilt])
              have hwC_eq : wC = (C.gates.drop k).foldl stepW wC_pre := by
                conv_lhs =>
                  rw [show wC = C.gates.foldl stepW (List.ofFn x2only) from rfl,
                    ← List.take_append_drop k C.gates, List.foldl_append]
              rw [hwC_eq, hlt']
            have hpreD : wD_pre.getD (i + 1) false = wD.getD (i + 1) false := by
              have hlen_pre : (D.gates.take k).length = k := by
                simp [List.length_take, hlenD]; omega
              have hlt' := hstep_lt (D.gates.drop k) wD_pre (i + 1) (by
                rw [hstep_len]; simp [hlen_pre]; omega)
              have hwD_eq : wD = (D.gates.drop k).foldl stepW wD_pre := by
                conv_lhs =>
                  rw [show wD = D.gates.foldl stepW (true :: List.ofFn x2only) from rfl,
                    ← List.take_append_drop k D.gates, List.foldl_append]
              rw [hwD_eq, hlt']
            rw [hpreC, hpreD]
            exact hagree i hilt hibad
          · have hc_def : wC_pre.getD i false = false := by
              apply List.getD_eq_default
              rw [hstep_len, List.length_take]
              simp [hlenC]
              omega
            have hd_def : wD_pre.getD (i + 1) false = false := by
              apply List.getD_eq_default
              rw [hstep_len, List.length_take]
              simp [hlenD]
              omega
            rw [hc_def, hd_def]
        have htail := ih (fun hm => hl0 (List.mem_cons_of_mem _ hm))
          (fun hlt hm => hlbad hlt (List.mem_cons_of_mem _ hm))
        simp only [List.map_cons, hpt, htail]
    rw [hc_val, hd_val, hop, hmap_aux (eff gk) (eff hk_g) heff_rel hno0 hnobad]
  have hagree_lt_kstar : ∀ i < 7 + kstar, i ≠ 7 + kstar →
      wC.getD i false = wD.getD (i + 1) false := by
    intro i hi _
    rcases (by omega : i < 7 ∨ 7 ≤ i) with hi7 | hi7
    · have hc1 : wC.getD i false = (List.ofFn x2only).getD i false :=
        hstep_lt C.gates (List.ofFn x2only) i (by simp [hi7])
      have hd1 : wD.getD (i + 1) false = (true :: List.ofFn x2only).getD (i + 1) false :=
        hstep_lt D.gates (true :: List.ofFn x2only) (i + 1) (by simp; omega)
      rw [hc1, hd1]
      simp
    · have hnd : ¬ diff (i - 7) := hkstar_min (i - 7) (by omega)
      have hd_eq : wC.getD (7 + (i - 7)) false = wD.getD (8 + (i - 7)) false := by
        by_contra hne
        exact hnd ⟨by omega, hne⟩
      rw [show 7 + (i - 7) = i by omega, show 8 + (i - 7) = i + 1 by omega] at hd_eq
      exact hd_eq
  have hzero_eff_kstar : 0 ∈ eff (D.gates[kstar]'(by omega)) := by
    by_contra hno0
    exact hkstar_spec.2
      (hpre_agree_at kstar hkstar_lt (7 + kstar) hagree_lt_kstar hno0 (fun hlt => by omega))
  have hor2_not_diff : ∀ (k : ℕ) (hk : k < 11),
      (C.gates[k]'(by omega)).op = PEqualNP.CircuitLowerBounds.GateOp.or →
      2 ∈ (C.gates[k]'(by omega)).inputs → ¬ diff k := by
    intro k hk hor h2in hdk
    obtain ⟨hop, hinp⟩ := hedits_get k hk
    obtain ⟨j, hjmem, hjrel⟩ := hfa_mem_left hinp h2in
    have hwC_true : wC.getD (7 + k) false = true := by
      have h1' := hstep_gate C.gates (List.ofFn x2only) k (by omega)
      change (C.gates.foldl stepW (List.ofFn x2only)).getD (7 + k) false = true
      rw [show 7 + k = (List.ofFn x2only).length + k by simp, h1']
      simp only [hor, PEqualNP.CircuitLowerBounds.GateOp.eval, List.any_map, List.any_eq_true,
        Function.comp_apply, id_eq]
      refine ⟨2, h2in, ?_⟩
      rw [hstep_lt (C.gates.take k) (List.ofFn x2only) 2 (by simp)]
      rfl
    have hwD_true : wD.getD (8 + k) false = true := by
      have h1' := hstep_gate D.gates (true :: List.ofFn x2only) k (by omega)
      change (D.gates.foldl stepW (true :: List.ofFn x2only)).getD (8 + k) false = true
      rw [show 8 + k = (true :: List.ofFn x2only).length + k by simp, h1']
      simp only [← hop, hor, PEqualNP.CircuitLowerBounds.GateOp.eval, List.any_map,
        List.any_eq_true, Function.comp_apply, id_eq]
      refine ⟨j, hjmem, ?_⟩
      rcases hjrel with rfl | ⟨rfl, _⟩
      · rw [hstep_lt (D.gates.take k) (true :: List.ofFn x2only) 3 (by simp)]
        rfl
      · rw [hstep_lt (D.gates.take k) (true :: List.ofFn x2only) 0 (by simp)]
        rfl
    exact hdk.2 (hwC_true.trans hwD_true.symm)
  let O2 : Finset (Fin 11) := Finset.univ.filter fun k =>
    (C.gates[k.val]'(by omega)).op.eval [true, false] &&
      (C.gates[k.val]'(by omega)).inputs.contains 2
  let E2 : Finset (Fin 11) := Finset.univ.filter fun k =>
    (eff (C.gates[k.val]'(by omega))).contains 2
  let Z0 : Finset (Fin 11) := Finset.univ.filter fun k =>
    (eff (D.gates[k.val]'(by omega))).contains 0
  let Dropped : Finset (Fin 11) := Finset.univ.filter fun k =>
    stFin.2.2.getD k.val true == false
  have hO2_card_eq : O2.card =
      (C.gates.filter (fun g => g.op.eval [true, false] && g.inputs.contains 2)).length := by
    exact hcard_filter C.gates 11 hlenC (fun g => g.op.eval [true, false] && g.inputs.contains 2)
  have hE2_card_eq : E2.card = (C.gates.filter (fun g => (eff g).contains 2)).length := by
    exact hcard_filter C.gates 11 hlenC (fun g => (eff g).contains 2)
  have hDrop_card_le : Dropped.card ≤ 3 := by
    have hcnt : Dropped.card = stFin.2.2.count false := by
      rw [hcount_eq_filter]
      have hcf := hcard_filter stFin.2.2 11 hstFin_len2 (fun b => b == false)
      convert hcf using 2
      ext k
      simp only [Dropped, Finset.mem_filter, Finset.mem_univ, true_and,
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : k.val < stFin.2.2.length)]
      rfl
    omega
  have hO2_sub_E2 : O2 ⊆ E2 := by
    intro k hk
    simp only [O2, E2, Finset.mem_filter, Finset.mem_univ, true_and, Bool.and_eq_true,
      List.contains_eq_mem, decide_eq_true_eq] at hk ⊢
    have hfk := hfan_mem k.val k.isLt
    have hor := (hop_or_eval _ hfk.1).mp hk.1
    simpa [eff, hor] using hk.2
  have hE2_sub_Drop : E2 ⊆ Dropped := by
    intro k hk
    simp only [E2, Dropped, Finset.mem_filter, Finset.mem_univ, true_and,
      List.contains_eq_mem, decide_eq_true_eq, beq_iff_eq] at hk ⊢
    apply hconst_drop k.val k.isLt
    have hfk := hfan_mem k.val k.isLt
    obtain ⟨hop, hinp⟩ := hedits_get k.val k.isLt
    have heff_rel := heff_rel_of _ _ hfk.1 hop hinp
    obtain ⟨j, hjmem, hjrel⟩ := hfa_mem_left heff_rel hk
    have h03 := hstk03 k.val k.isLt
    rcases hjrel with rfl | ⟨rfl, _⟩
    · exact ⟨3, hjmem, false, h03.2⟩
    · exact ⟨0, hjmem, true, h03.1⟩
  have hZ0_sub_Drop : Z0 ⊆ Dropped := by
    intro k hk
    simp only [Z0, Dropped, Finset.mem_filter, Finset.mem_univ, true_and,
      List.contains_eq_mem, decide_eq_true_eq, beq_iff_eq] at hk ⊢
    exact hconst_drop k.val k.isLt ⟨0, hk, true, (hstk03 k.val k.isLt).1⟩
  let kf : Fin 11 := ⟨kstar, hkstar_lt⟩
  have hkf_in_Z0 : kf ∈ Z0 := by
    simp only [Z0, Finset.mem_filter, Finset.mem_univ, true_and, List.contains_eq_mem,
      decide_eq_true_eq]
    exact hzero_eff_kstar
  have hkf_in_Drop : kf ∈ Dropped := hZ0_sub_Drop hkf_in_Z0
  have hkf_notin_O2 : kf ∉ O2 := by
    intro hmem
    simp only [O2, Finset.mem_filter, Finset.mem_univ, true_and, Bool.and_eq_true,
      List.contains_eq_mem, decide_eq_true_eq] at hmem
    have hfk := hfan_mem kstar hkstar_lt
    have hor := (hop_or_eval _ hfk.1).mp hmem.1
    exact hor2_not_diff kstar hkstar_lt hor hmem.2 hkstar_spec
  have hO2_sub_Drop : O2 ⊆ Dropped := Finset.Subset.trans hO2_sub_E2 hE2_sub_Drop
  have hIns_sub_Drop : insert kf O2 ⊆ Dropped := by
    intro k hk
    rcases Finset.mem_insert.mp hk with rfl | hk
    · exact hkf_in_Drop
    · exact hO2_sub_Drop hk
  have hO2_card2 : O2.card = 2 := by
    have h1' : 2 ≤ O2.card := by omega
    have h2' : (insert kf O2).card ≤ Dropped.card := Finset.card_le_card hIns_sub_Drop
    rw [Finset.card_insert_of_notMem hkf_notin_O2] at h2'
    omega
  have hDrop_eq : Dropped = insert kf O2 := by
    refine (Finset.eq_of_subset_of_card_le hIns_sub_Drop ?_).symm
    rw [Finset.card_insert_of_notMem hkf_notin_O2, hO2_card2]
    exact hDrop_card_le
  have hkstar_not_const : ∀ b : Bool, stFin.1.getD (8 + kstar) (Sum.inl false) ≠ Sum.inl b := by
    intro b hkb
    have hnot_out : C.output ≠ 7 + kstar := by
      intro hout_eq
      cases b with
      | false =>
        let y : Fin 6 → Bool := fun i => decide (i = 0 ∨ i = 1)
        let row : Fin 7 → Bool := fun i => ([y 0, y 1, false, y 2, y 3, y 4, y 5]).getD i.val false
        have hy := hD row
        rw [hrow_eq y, hstFin_sem y (C.output + 1), hout_eq,
          show 7 + kstar + 1 = 8 + kstar by omega, hkb] at hy
        have hc6 : c6 y = true := by decide
        rw [hc6] at hy
        cases hy
      | true =>
        let y : Fin 6 → Bool := fun _ => false
        let row : Fin 7 → Bool := fun i => ([y 0, y 1, false, y 2, y 3, y 4, y 5]).getD i.val false
        have hy := hD row
        rw [hrow_eq y, hstFin_sem y (C.output + 1), hout_eq,
          show 7 + kstar + 1 = 8 + kstar by omega, hkb] at hy
        have hc6 : c6 y = false := by decide
        rw [hc6] at hy
        cases hy
    have hex_m : ∃ m, diff m ∧ m ≠ kstar := by
      refine ⟨C.output - 7, ⟨by omega, ?_⟩, by omega⟩
      rw [show 7 + (C.output - 7) = C.output by omega,
        show 8 + (C.output - 7) = C.output + 1 by omega]
      change C.eval (List.ofFn x2only) ≠ wD.getD (C.output + 1) false
      rw [hwC_eval, hwD_eval]
      decide
    let mstar := Nat.find hex_m
    have hmstar_spec := Nat.find_spec hex_m
    have hmstar_diff : diff mstar := hmstar_spec.1
    have hmstar_ne : mstar ≠ kstar := hmstar_spec.2
    have hmstar_lt : mstar < 11 := hmstar_diff.1
    let mf : Fin 11 := ⟨mstar, hmstar_lt⟩
    have hmf_notin_O2 : mf ∉ O2 := by
      intro hmem
      simp only [O2, Finset.mem_filter, Finset.mem_univ, true_and, Bool.and_eq_true,
        List.contains_eq_mem, decide_eq_true_eq] at hmem
      have hfm := hfan_mem mstar hmstar_lt
      have hor := (hop_or_eval _ hfm.1).mp hmem.1
      exact hor2_not_diff mstar hmstar_lt hor hmem.2 hmstar_diff
    have hmf_notin_Drop : mf ∉ Dropped := by
      rw [hDrop_eq]
      intro hmem
      rcases Finset.mem_insert.mp hmem with h1' | h2'
      · exact hmstar_ne (congrArg Fin.val h1')
      · exact hmf_notin_O2 h2'
    have hmf_not0 : 0 ∉ eff (D.gates[mstar]'(by omega)) := by
      intro h0m
      have hmem : mf ∈ Z0 := by
        simp only [Z0, Finset.mem_filter, Finset.mem_univ, true_and, List.contains_eq_mem,
          decide_eq_true_eq]
        exact h0m
      exact hmf_notin_Drop (hZ0_sub_Drop hmem)
    have hagree_ne_kstar : ∀ i < 7 + mstar, i ≠ 7 + kstar →
        wC.getD i false = wD.getD (i + 1) false := by
      intro i hi hine
      rcases (by omega : i < 7 ∨ 7 ≤ i) with hi7 | hi7
      · have hc1 : wC.getD i false = (List.ofFn x2only).getD i false :=
          hstep_lt C.gates (List.ofFn x2only) i (by simp [hi7])
        have hd1 : wD.getD (i + 1) false = (true :: List.ofFn x2only).getD (i + 1) false :=
          hstep_lt D.gates (true :: List.ofFn x2only) (i + 1) (by simp; omega)
        rw [hc1, hd1]
        simp
      · have hne_k : i - 7 ≠ kstar := by omega
        have hlt_m : i - 7 < mstar := by omega
        have hnd : ¬ (diff (i - 7) ∧ i - 7 ≠ kstar) := Nat.find_min hex_m hlt_m
        have hd_eq : wC.getD (7 + (i - 7)) false = wD.getD (8 + (i - 7)) false := by
          by_contra hne
          exact hnd ⟨⟨by omega, hne⟩, hne_k⟩
        rw [show 7 + (i - 7) = i by omega, show 8 + (i - 7) = i + 1 by omega] at hd_eq
        exact hd_eq
    have hk_in_m : 8 + kstar ∈ eff (D.gates[mstar]'(by omega)) := by
      by_contra hnok
      exact hmstar_diff.2
        (hpre_agree_at mstar hmstar_lt (7 + kstar) hagree_ne_kstar hmf_not0
          (fun _ => by rw [show 7 + kstar + 1 = 8 + kstar by omega]; exact hnok))
    have hlt_m_k : kstar < mstar := by
      by_contra hge
      have hm_lt_k : mstar < kstar := by omega
      exact hkstar_min mstar hm_lt_k hmstar_diff
    have hm_dropped : stFin.2.2.getD mstar true = false := by
      apply hconst_drop mstar hmstar_lt
      refine ⟨8 + kstar, hk_in_m, b, ?_⟩
      have hl := hlocal mstar hmstar_lt
      rw [hl.2.2.2 (8 + kstar) (by omega)]
      exact hkb
    apply hmf_notin_Drop
    simp only [Dropped, Finset.mem_filter, Finset.mem_univ, true_and, beq_iff_eq]
    exact hm_dropped
  have hstar_shape :
      (PEqualNP.MetaComplexity.NestedCover.gateAt D kstar).op =
        PEqualNP.CircuitLowerBounds.GateOp.and ∧
      (PEqualNP.MetaComplexity.NestedCover.gateAt D kstar).inputs.length = 2 ∧
      (PEqualNP.MetaComplexity.NestedCover.gateAt D kstar).inputs ≠ [0, 0] ∧
      3 ∉ (PEqualNP.MetaComplexity.NestedCover.gateAt D kstar).inputs := by
    have hgatD : PEqualNP.MetaComplexity.NestedCover.gateAt D kstar =
        D.gates[kstar]'(by omega) := by
      simp [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by omega : kstar < D.gates.length)]
    rw [hgatD]
    set hk := D.gates[kstar]'(by omega)
    have hl := hlocal kstar hkstar_lt
    set stk := (D.gates.take kstar).foldl simStep st0
    have hfk := hfanD hk (List.getElem_mem (by omega))
    have h0in : 0 ∈ eff hk := hzero_eff_kstar
    obtain ⟨h0, h3⟩ := hstk03 kstar hkstar_lt
    change stk.1.getD 0 (Sum.inl false) = Sum.inl true at h0
    change stk.1.getD 3 (Sum.inl false) = Sum.inl false at h3
    have hnc : ∀ b : Bool, (simGate stk.1 (6 + stk.2.1.length) hk).1 ≠ Sum.inl b := by
      intro b heq
      exact hkstar_not_const b (hl.1.trans heq)
    have hfk1 := hfk.1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hfk1
    rcases hfk1 with hop | hop | hop
    · have h0in' : 0 ∈ hk.inputs := by
        change 0 ∈ eff hk at h0in
        simpa [eff, hop] using h0in
      rcases hgi : hk.inputs with _ | ⟨i1, _ | ⟨i2, _ | _⟩⟩
      · simp [hgi] at h0in'
      · simp only [hgi, List.mem_singleton] at h0in'
        exfalso
        apply hnc true
        dsimp only [simGate]
        rw [hop, hgi, ← h0in']
        dsimp only
        rw [h0]
      · refine ⟨hop, rfl, ?_, ?_⟩
        · intro heq00
          apply hnc true
          dsimp only [simGate]
          rw [hop, hgi, heq00]
          dsimp only
          rw [h0]
        · intro h3in
          simp only [List.mem_cons, List.not_mem_nil, or_false] at h3in
          rcases h3in with rfl | rfl
          · apply hnc false
            dsimp only [simGate]
            rw [hop, hgi]
            dsimp only
            rw [h3]
          · apply hnc false
            dsimp only [simGate]
            rw [hop, hgi]
            dsimp only
            rw [h3]
            cases stk.1.getD i1 (Sum.inl false) with
            | inl b1 => cases b1 <;> rfl
            | inr _ => rfl
      · have := hfk.2; simp [hgi] at this
    · have h0in' : 0 ∈ hk.inputs := by
        change 0 ∈ eff hk at h0in
        simpa [eff, hop] using h0in
      rcases hgi : hk.inputs with _ | ⟨i1, _ | ⟨i2, _ | _⟩⟩
      · simp [hgi] at h0in'
      · simp only [hgi, List.mem_singleton] at h0in'
        exfalso
        apply hnc true
        dsimp only [simGate]
        rw [hop, hgi, ← h0in']
        dsimp only
        rw [h0]
      · simp only [hgi, List.mem_cons, List.not_mem_nil, or_false] at h0in'
        exfalso
        rcases h0in' with rfl | rfl
        · apply hnc true
          dsimp only [simGate]
          rw [hop, hgi]
          dsimp only
          rw [h0]
        · apply hnc true
          dsimp only [simGate]
          rw [hop, hgi]
          dsimp only
          rw [h0]
          cases stk.1.getD i1 (Sum.inl false) with
          | inl b1 => cases b1 <;> rfl
          | inr _ => rfl
      · have := hfk.2; simp [hgi] at this
    · have h0in' : 0 ∈ hk.inputs.take 1 := by
        change 0 ∈ eff hk at h0in
        simpa [eff, hop] using h0in
      rcases hgi : hk.inputs with _ | ⟨i1, rest⟩
      · simp [hgi] at h0in'
      · simp only [hgi, List.take_succ_cons, List.take_zero, List.mem_singleton] at h0in'
        exfalso
        apply hnc false
        dsimp only [simGate]
        rw [hop, hgi, ← h0in']
        dsimp only
        rw [h0]
        rfl
  have hkf_notin_E2 : kf ∉ E2 := by
    intro hmem
    simp only [E2, Finset.mem_filter, Finset.mem_univ, true_and, List.contains_eq_mem,
      decide_eq_true_eq] at hmem
    set gk := C.gates[kstar]'(by omega)
    set hk := D.gates[kstar]'(by omega)
    have hgatD : PEqualNP.MetaComplexity.NestedCover.gateAt D kstar = hk := by
      simp [PEqualNP.MetaComplexity.NestedCover.gateAt, hk, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by omega : kstar < D.gates.length)]
    rw [hgatD] at hstar_shape
    obtain ⟨hopD, hlen2D, hne00, hno3⟩ := hstar_shape
    obtain ⟨hop, hinp⟩ := hedits_get kstar hkstar_lt
    have hopC : gk.op = PEqualNP.CircuitLowerBounds.GateOp.and := hop.trans hopD
    have hmem_gk : 2 ∈ gk.inputs := by
      have hmem' : 2 ∈ eff gk := hmem
      simp only [eff, hopC] at hmem'
      exact hmem'
    have hlen2C : gk.inputs.length = 2 := by
      rw [(List.forall₂_iff_get.mp hinp).1]
      exact hlen2D
    rcases hgi : gk.inputs with _ | ⟨i1, _ | ⟨i2, _ | _⟩⟩
    · simp [hgi] at hlen2C
    · simp [hgi] at hlen2C
    · rw [hgi] at hinp
      rcases hdi : hk.inputs with _ | ⟨j1, _ | ⟨j2, _ | _⟩⟩
      · simp [hdi] at hlen2D
      · simp [hdi] at hlen2D
      · rw [hdi] at hinp
        have hj1_rel := (List.forall₂_cons.mp hinp).1
        have hj2_rel := (List.forall₂_cons.mp (List.forall₂_cons.mp hinp).2).1
        have hj1_ne3 : j1 ≠ 3 := fun h3 => hno3 (by simp [hdi, h3])
        have hj2_ne3 : j2 ≠ 3 := fun h3 => hno3 (by simp [hdi, h3])
        have hj1_0 : i1 = 2 → j1 = 0 := by
          intro hi1
          subst hi1
          rcases hj1_rel with rfl | ⟨rfl, _⟩
          · exact (hj1_ne3 rfl).elim
          · rfl
        have hj2_0 : i2 = 2 → j2 = 0 := by
          intro hi2
          subst hi2
          rcases hj2_rel with rfl | ⟨rfl, _⟩
          · exact (hj2_ne3 rfl).elim
          · rfl
        have hnot_both0 : ¬ (j1 = 0 ∧ j2 = 0) := by
          rintro ⟨rfl, rfl⟩
          exact hne00 hdi
        have hi_cases : i1 = 2 ∨ i2 = 2 := by
          rw [hgi] at hmem_gk
          rcases List.mem_cons.mp hmem_gk with h1' | h2'
          · exact Or.inl h1'.symm
          · exact Or.inr (List.mem_singleton.mp h2').symm
        have heq_other : ∀ (i j : ℕ),
            (j = i + 1 ∨ j = 0 ∧ (i = a ∨ i = b)) → j ≠ 0 →
            ((C.gates.take kstar).foldl stepW (List.ofFn x2only)).getD i false =
              ((D.gates.take kstar).foldl stepW (true :: List.ofFn x2only)).getD j false := by
          intro i j hij hj0
          have hji : j = i + 1 := by
            rcases hij with rfl | ⟨rfl, _⟩
            · rfl
            · exact (hj0 rfl).elim
          rw [hji]
          by_cases hilt : i < 7 + kstar
          · have hpreC : ((C.gates.take kstar).foldl stepW (List.ofFn x2only)).getD i false =
                wC.getD i false := by
              have hlen_pre : (C.gates.take kstar).length = kstar := by
                simp [List.length_take, hlenC]; omega
              have hlt' := hstep_lt (C.gates.drop kstar)
                ((C.gates.take kstar).foldl stepW (List.ofFn x2only)) i
                (by rw [hstep_len]; simp [hlen_pre, hilt])
              have hwC_eq : wC = (C.gates.drop kstar).foldl stepW
                  ((C.gates.take kstar).foldl stepW (List.ofFn x2only)) := by
                conv_lhs =>
                  rw [show wC = C.gates.foldl stepW (List.ofFn x2only) from rfl,
                    ← List.take_append_drop kstar C.gates, List.foldl_append]
              rw [hwC_eq, hlt']
            have hpreD : ((D.gates.take kstar).foldl stepW
                (true :: List.ofFn x2only)).getD (i + 1) false = wD.getD (i + 1) false := by
              have hlen_pre : (D.gates.take kstar).length = kstar := by
                simp [List.length_take, hlenD]; omega
              have hlt' := hstep_lt (D.gates.drop kstar)
                ((D.gates.take kstar).foldl stepW (true :: List.ofFn x2only)) (i + 1)
                (by rw [hstep_len]; simp [hlen_pre]; omega)
              have hwD_eq : wD = (D.gates.drop kstar).foldl stepW
                  ((D.gates.take kstar).foldl stepW (true :: List.ofFn x2only)) := by
                conv_lhs =>
                  rw [show wD = D.gates.foldl stepW (true :: List.ofFn x2only) from rfl,
                    ← List.take_append_drop kstar D.gates, List.foldl_append]
              rw [hwD_eq, hlt']
            rw [hpreC, hpreD]
            exact hagree_lt_kstar i hilt (by omega)
          · have hc_def : ((C.gates.take kstar).foldl stepW (List.ofFn x2only)).getD i false =
                false := by
              apply List.getD_eq_default
              rw [hstep_len, List.length_take]
              simp [hlenC]
              omega
            have hd_def : ((D.gates.take kstar).foldl stepW
                (true :: List.ofFn x2only)).getD (i + 1) false = false := by
              apply List.getD_eq_default
              rw [hstep_len, List.length_take]
              simp [hlenD]
              omega
            rw [hc_def, hd_def]
        have hsame_in : ((C.gates.take kstar).foldl stepW (List.ofFn x2only)).getD i1 false =
            ((D.gates.take kstar).foldl stepW (true :: List.ofFn x2only)).getD j1 false ∧
            ((C.gates.take kstar).foldl stepW (List.ofFn x2only)).getD i2 false =
            ((D.gates.take kstar).foldl stepW (true :: List.ofFn x2only)).getD j2 false := by
          have hC2 : ((C.gates.take kstar).foldl stepW (List.ofFn x2only)).getD 2 false = true := by
            rw [hstep_lt (C.gates.take kstar) (List.ofFn x2only) 2 (by simp)]
            rfl
          have hD0 : ((D.gates.take kstar).foldl stepW
              (true :: List.ofFn x2only)).getD 0 false = true := by
            rw [hstep_lt (D.gates.take kstar) (true :: List.ofFn x2only) 0 (by simp)]
            rfl
          rcases hi_cases with rfl | rfl
          · have hj1 : j1 = 0 := hj1_0 rfl
            have hj2 : j2 ≠ 0 := fun h0 => hnot_both0 ⟨hj1, h0⟩
            refine ⟨?_, heq_other i2 j2 hj2_rel hj2⟩
            rw [hj1, hC2, hD0]
          · have hj2 : j2 = 0 := hj2_0 rfl
            have hj1 : j1 ≠ 0 := fun h0 => hnot_both0 ⟨h0, hj2⟩
            refine ⟨heq_other i1 j1 hj1_rel hj1, ?_⟩
            rw [hj2, hC2, hD0]
        apply hkstar_spec.2
        have hc1 := hstep_gate C.gates (List.ofFn x2only) kstar (by omega)
        have hd1 := hstep_gate D.gates (true :: List.ofFn x2only) kstar (by omega)
        change (C.gates.foldl stepW (List.ofFn x2only)).getD (7 + kstar) false =
          (D.gates.foldl stepW (true :: List.ofFn x2only)).getD (8 + kstar) false
        rw [show 7 + kstar = (List.ofFn x2only).length + kstar by simp, hc1,
          show 8 + kstar = (true :: List.ofFn x2only).length + kstar by simp, hd1]
        change gk.op.eval (gk.inputs.map _) = hk.op.eval (hk.inputs.map _)
        rw [hgi, hdi, ← hop, List.map_cons, List.map_cons, List.map_nil,
          List.map_cons, List.map_cons, List.map_nil, hsame_in.1, hsame_in.2]
      · simp [hdi] at hlen2D
    · simp [hgi] at hlen2C
  have hE2_eq_O2 : E2 = O2 := by
    apply Finset.Subset.antisymm _ hO2_sub_E2
    intro k hk
    have hkd : k ∈ Dropped := hE2_sub_Drop hk
    rw [hDrop_eq] at hkd
    rcases Finset.mem_insert.mp hkd with rfl | hko
    · exact (hkf_notin_E2 hk).elim
    · exact hko
  have hE2_card2 : E2.card = 2 := by rw [hE2_eq_O2, hO2_card2]
  apply h2 C D a b hfan hsize hfun hedits hD hunm
  · rw [← hO2_card_eq, hO2_card2]
  · rw [← hE2_card_eq, hE2_card2]
  · refine ⟨kstar, hkstar_lt, ?_, hstar_shape.1, hstar_shape.2.1, hstar_shape.2.2.1,
      hstar_shape.2.2.2, ?_⟩
    · simp only [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by omega : kstar < D.gates.length)]
      exact hzero_eff_kstar
    · intro j hj11 hjk h0j
      let jf : Fin 11 := ⟨j, hj11⟩
      have hj_Z0 : jf ∈ Z0 := by
        simp only [Z0, Finset.mem_filter, Finset.mem_univ, true_and, List.contains_eq_mem,
          decide_eq_true_eq]
        simpa [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem (by omega : j < D.gates.length)] using h0j
      have hj_Drop : jf ∈ Dropped := hZ0_sub_Drop hj_Z0
      rw [hDrop_eq] at hj_Drop
      rcases Finset.mem_insert.mp hj_Drop with hjeq | hjO2
      · exact (hjk (congrArg Fin.val hjeq)).elim
      · simp only [O2, Finset.mem_filter, Finset.mem_univ, true_and, Bool.and_eq_true,
          List.contains_eq_mem, decide_eq_true_eq] at hjO2
        have hfj := hfan_mem j hj11
        have hor := (hop_or_eval _ hfj.1).mp hjO2.1
        simp only [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem (by omega : j < C.gates.length)]
        exact ⟨hor, hjO2.2⟩
