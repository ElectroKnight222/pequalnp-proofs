import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.R_meta_2583_1

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership
open PEqualNP.TopForm
open PEqualNP.ReadK
open PEqualNP.Core

theorem foldl_snoc_prefix {α β : Type} (F : List α → β → α) (gs : List β) (init : List α) :
    init <+: gs.foldl (fun R g => R ++ [F R g]) init := by
  induction gs generalizing init with
  | nil => exact List.prefix_refl _
  | cons g gs ih => exact (List.prefix_append init [F init g]).trans (ih _)

theorem foldl_snoc_length {α β : Type} (F : List α → β → α) (gs : List β) (init : List α) :
    (gs.foldl (fun R g => R ++ [F R g]) init).length = init.length + gs.length := by
  induction gs generalizing init with
  | nil => simp
  | cons g gs ih => simp [ih]; omega

theorem getD_of_prefix {α : Type} {P L : List α} (h : P <+: L) {i : ℕ} (hi : i < P.length)
    (d : α) : L.getD i d = P.getD i d := by
  obtain ⟨t, rfl⟩ := h
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem foldl_snoc_init {α : Type} (G : List α → Gate → α) (d : α) (init : List α)
    (gs : List Gate) (i : ℕ) (hi : i < init.length) :
    (gs.foldl (fun R g => R ++ [G (g.inputs.map fun k => R.getD k d) g]) init).getD i d
      = init.getD i d :=
  getD_of_prefix (foldl_snoc_prefix (fun R g => G (g.inputs.map fun k => R.getD k d) g) _ _) hi d

theorem foldl_snoc_beyond {α : Type} (G : List α → Gate → α) (d : α) (init : List α)
    (gs : List Gate) (i : ℕ) (hi : init.length + gs.length ≤ i) :
    (gs.foldl (fun R g => R ++ [G (g.inputs.map fun k => R.getD k d) g]) init).getD i d = d := by
  apply List.getD_eq_default
  rw [foldl_snoc_length (fun R g => G (g.inputs.map fun k => R.getD k d) g)]
  exact hi

theorem foldl_snoc_gate {α : Type} (G : List α → Gate → α) (d : α) (init : List α)
    (gs : List Gate) (j : ℕ) (hj : j < gs.length)
    (hrb : ∀ i ∈ gs[j].inputs, i < init.length + j) :
    (gs.foldl (fun R g => R ++ [G (g.inputs.map fun k => R.getD k d) g]) init).getD
        (init.length + j) d
      = G (gs[j].inputs.map fun i =>
          (gs.foldl (fun R g => R ++ [G (g.inputs.map fun k => R.getD k d) g]) init).getD i d)
          gs[j] := by
  have hsplit : gs = gs.take j ++ gs[j] :: gs.drop (j + 1) := by simp
  set P := (gs.take j).foldl (fun R g => R ++ [G (g.inputs.map fun k => R.getD k d) g]) init
    with hP
  have hPl : P.length = init.length + j := by
    rw [hP, foldl_snoc_length (fun R g => G (g.inputs.map fun k => R.getD k d) g)]
    simp; omega
  have hpre : (P ++ [G (gs[j].inputs.map fun k => P.getD k d) gs[j]]) <+:
      gs.foldl (fun R g => R ++ [G (g.inputs.map fun k => R.getD k d) g]) init := by
    conv_rhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
    exact foldl_snoc_prefix (fun R g => G (g.inputs.map fun k => R.getD k d) g) _ _
  have hpre2 := (List.prefix_append P _).trans hpre
  rw [getD_of_prefix hpre (by simp; omega)]
  have e1 : (P ++ [G (gs[j].inputs.map fun k => P.getD k d) gs[j]]).getD (init.length + j) d
      = G (gs[j].inputs.map fun k => P.getD k d) gs[j] := by
    rw [← hPl]; simp
  rw [e1]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [getD_of_prefix hpre2 (by rw [hPl]; exact hrb i hi)]

def wireG (ins : List Bool) (g : Gate) : Bool := g.op.eval ins

theorem wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl
      (fun R g => R ++ [wireG (g.inputs.map fun i => R.getD i false) g]) x := rfl

theorem wires_getD_lt {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    (C.wires (List.ofFn x)).getD i false = x ⟨i, hi⟩ := by
  rw [wires_eq_foldl, foldl_snoc_init wireG false (List.ofFn x) C.gates i (by simpa using hi)]
  simp [List.getD_eq_getElem?_getD, hi]

theorem wires_getD_beyond {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ)
    (hi : n + C.gates.length ≤ i) :
    (C.wires (List.ofFn x)).getD i false = false := by
  rw [wires_eq_foldl]
  exact foldl_snoc_beyond wireG false (List.ofFn x) C.gates i (by simpa using hi)

theorem gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

theorem ao2_inputs_eq {n : ℕ} (C : Circuit) (hC : IsAO2 n C) (j : ℕ) (hj : j < C.gates.length) :
    (gateAt C j).inputs = [opnd C j 0, opnd C j 1] := by
  have hg : C.gates[j]? = some (gateAt C j) := by
    simp [gateAt, List.getD_eq_getElem?_getD, hj]
  have hlen : (gateAt C j).inputs.length = 2 := hC.2.2 _ (List.mem_of_getElem? hg)
  obtain ⟨a, b, hab⟩ := List.length_eq_two.1 hlen
  simp [opnd, hab]

theorem ao2_opnd_lt {n : ℕ} (C : Circuit) (hC : IsAO2 n C) (j : ℕ) (hj : j < C.gates.length)
    (d : Fin 2) : opnd C j d < n + j := by
  apply hC.2.1 j hj
  rw [ao2_inputs_eq C hC j hj]
  fin_cases d <;> simp

theorem gateVal_or_iff {n : ℕ} (C : Circuit) (hC : IsAO2 n C) (j : ℕ) (hj : j < C.gates.length)
    (ho : (gateAt C j).op = GateOp.or) (x : Fin n → Bool) :
    gateVal n C j x = true ↔
      (C.wires (List.ofFn x)).getD (opnd C j 0) false = true ∨
      (C.wires (List.ofFn x)).getD (opnd C j 1) false = true := by
  unfold gateVal
  rw [wires_eq_foldl]
  have hrb : ∀ i ∈ C.gates[j].inputs, i < (List.ofFn x).length + j := by
    intro i hi
    rw [List.length_ofFn]
    exact hC.2.1 j hj i (by rw [gateAt_eq hj]; exact hi)
  have hfg := foldl_snoc_gate wireG false (List.ofFn x) C.gates j hj hrb
  rw [List.length_ofFn] at hfg
  rw [hfg, wireG, ← gateAt_eq hj, ho, ao2_inputs_eq C hC j hj]
  simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, Bool.or_false,
    id_eq, Bool.or_eq_true]

theorem mem_insertNew_of_mem (A : List (List ℕ)) (v u : List ℕ) (hu : u ∈ A) :
    u ∈ insertNew A v := by
  unfold insertNew
  split_ifs
  · exact hu
  · simp [hu]

theorem mem_insertNew_self (A : List (List ℕ)) (v : List ℕ) :
    v ∈ insertNew A v := by
  unfold insertNew
  split_ifs with h
  · exact h
  · simp

theorem mem_foldl_insertNew_left (A B : List (List ℕ)) (u : List ℕ) (hu : u ∈ B) :
    u ∈ A.foldl insertNew B := by
  induction A generalizing B with
  | nil => exact hu
  | cons v A ih => exact ih _ (mem_insertNew_of_mem B v u hu)

theorem mem_foldl_insertNew_right (A B : List (List ℕ)) (u : List ℕ) (hu : u ∈ A) :
    u ∈ A.foldl insertNew B := by
  induction A generalizing B with
  | nil => simp at hu
  | cons v A ih =>
    rcases List.mem_cons.1 hu with rfl | hu'
    · exact mem_foldl_insertNew_left A _ u (mem_insertNew_self B u)
    · exact ih _ hu'

def rvG (S : List ℕ) (k : ℕ) (ins : List (List (List ℕ))) (g : Gate) : List (List ℕ) :=
  match g.op with
  | GateOp.or => ins.foldl (fun acc A => A.foldl insertNew acc) []
  | GateOp.and => ins.foldl (andStep k) [S.map fun _ => 0]
  | _ => []

theorem readVectors_eq_foldl (C : Circuit) (n : ℕ) (S : List ℕ) (k : ℕ) :
    readVectors C n S k = C.gates.foldl
      (fun R g => R ++ [rvG S k (g.inputs.map fun i => R.getD i []) g])
      ((List.range n).map (leafVectors S k)) := rfl

theorem readVectors_or_mem {n : ℕ} (C : Circuit) (hC : IsAO2 n C) (S : List ℕ) (k j : ℕ)
    (hj : j < C.gates.length) (ho : (gateAt C j).op = GateOp.or) (d : Fin 2) (v : List ℕ)
    (hv : v ∈ (readVectors C n S k).getD (opnd C j d) []) :
    v ∈ (readVectors C n S k).getD (n + j) [] := by
  have hrb : ∀ i ∈ C.gates[j].inputs, i < ((List.range n).map (leafVectors S k)).length + j := by
    intro i hi
    rw [List.length_map, List.length_range]
    exact hC.2.1 j hj i (by rw [gateAt_eq hj]; exact hi)
  have hfg := foldl_snoc_gate (rvG S k) [] ((List.range n).map (leafVectors S k)) C.gates j hj hrb
  rw [List.length_map, List.length_range] at hfg
  rw [readVectors_eq_foldl, hfg, ← gateAt_eq hj, rvG, ho, ao2_inputs_eq C hC j hj]
  simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, ← readVectors_eq_foldl]
  fin_cases d
  · exact mem_foldl_insertNew_left _ _ v (mem_foldl_insertNew_right _ _ v hv)
  · exact mem_foldl_insertNew_right _ _ v hv

theorem readsAtMost_or_mono {n : ℕ} (C : Circuit) (hC : IsAO2 n C) (S : List ℕ) (k j i : ℕ)
    (hj : j < C.gates.length) (ho : (gateAt C j).op = GateOp.or) (d : Fin 2)
    (hd : opnd C j d = n + i)
    (hi : readsAtMost (atGate n C i) n S k = true) :
    readsAtMost (atGate n C j) n S k = true := by
  unfold readsAtMost atGate at hi ⊢
  simp only [List.any_eq_true] at hi ⊢
  obtain ⟨v, hv1, hv2⟩ := hi
  refine ⟨v, ?_, hv2⟩
  have heq : readVectors { C with output := n + j } n S k = readVectors C n S k := rfl
  have heq' : readVectors { C with output := n + i } n S k = readVectors C n S k := rfl
  rw [heq]
  rw [heq', ← hd] at hv1
  exact readVectors_or_mem C hC S k j hj ho d v hv1

def incGraph {N : ℕ} (I : Fin N → Fin N → Prop) : SimpleGraph (Fin (N + N)) where
  Adj a b :=
    (∃ p l : Fin N, a = Fin.castAdd N p ∧ b = Fin.natAdd N l ∧ I p l) ∨
    (∃ p l : Fin N, b = Fin.castAdd N p ∧ a = Fin.natAdd N l ∧ I p l)
  symm := ⟨fun _ _ h => h.elim Or.inr Or.inl⟩
  loopless := by
    refine ⟨fun a h => ?_⟩
    rcases h with ⟨p, l, h1, h2, _⟩ | ⟨p, l, h1, h2, _⟩
    · have := congrArg Fin.val (h1.symm.trans h2)
      simp only [Fin.val_castAdd, Fin.val_natAdd] at this
      have hp := p.2
      omega
    · have := congrArg Fin.val (h1.symm.trans h2)
      simp only [Fin.val_castAdd, Fin.val_natAdd] at this
      have hp := p.2
      omega

theorem incGraph_bipartite {N : ℕ} (I : Fin N → Fin N → Prop) :
    ∀ u v : Fin (N + N), (incGraph I).Adj u v →
      decide (u.val < N) ≠ decide (v.val < N) := by
  intro u v huv
  rcases huv with ⟨p, l, rfl, rfl, _⟩ | ⟨p, l, rfl, rfl, _⟩
  · simp
  · simp

theorem incGraph_nonempty_edge {q N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hl : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) :
    ∃ u v : Fin (N + N), (incGraph I).Adj u v := by
  have hpos : 0 < N := by omega
  let l0 : Fin N := ⟨0, hpos⟩
  have hc : 0 < (Finset.univ.filter (fun p => I p l0)).card := by rw [hl l0]; omega
  obtain ⟨p, hp⟩ := Finset.card_pos.1 hc
  have hI : I p l0 := (Finset.mem_filter.1 hp).2
  exact ⟨Fin.castAdd N p, Fin.natAdd N l0, Or.inl ⟨p, l0, rfl, rfl, hI⟩⟩

theorem incGraph_noFourCycle {N : ℕ} (I : Fin N → Fin N → Prop)
    [DecidableRel (incGraph I).Adj]
    (hpp : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) :
    NoFourCycle (incGraph I) := by
  classical
  have cast_ne_nat : ∀ (p l : Fin N), Fin.castAdd N p ≠ Fin.natAdd N l := by
    intro p l h
    have hv := congrArg Fin.val h
    simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
    have hp := p.2
    omega
  have cast_inj : ∀ {p1 p2 : Fin N}, Fin.castAdd N p1 = Fin.castAdd N p2 → p1 = p2 := by
    intro p1 p2 h
    apply Fin.ext
    simpa only [Fin.val_castAdd] using congrArg Fin.val h
  have nat_inj : ∀ {l1 l2 : Fin N}, Fin.natAdd N l1 = Fin.natAdd N l2 → l1 = l2 := by
    intro l1 l2 h
    apply Fin.ext
    have hv := congrArg Fin.val h
    simp only [Fin.val_natAdd] at hv
    omega
  have adj_cast_left : ∀ {p : Fin N} {b : Fin (N + N)},
      (incGraph I).Adj (Fin.castAdd N p) b → ∃ l : Fin N, b = Fin.natAdd N l ∧ I p l := by
    intro p b h
    rcases h with ⟨p', l, h1, h2, hI⟩ | ⟨p', l, h1, h2, _⟩
    · cases cast_inj h1
      exact ⟨l, h2, hI⟩
    · exact absurd h2 (cast_ne_nat p l)
  have adj_nat_left : ∀ {l : Fin N} {b : Fin (N + N)},
      (incGraph I).Adj (Fin.natAdd N l) b → ∃ p : Fin N, b = Fin.castAdd N p ∧ I p l := by
    intro l b h
    rcases h with ⟨p, l', h1, h2, _⟩ | ⟨p, l', h1, h2, hI⟩
    · exact absurd h1 (cast_ne_nat p l).symm
    · cases nat_inj h2
      exact ⟨p, h1, hI⟩
  intro a b hab
  by_contra hgt
  have h2 : 2 ≤ (Finset.univ.filter fun w => (incGraph I).Adj a w ∧ (incGraph I).Adj b w).card := by
    omega
  obtain ⟨w1, hw1, w2, hw2, hw12⟩ := Finset.one_lt_card.1 h2
  rw [Finset.mem_filter] at hw1 hw2
  rcases hw1.2 with ⟨haw1, hbw1⟩
  rcases hw2.2 with ⟨haw2, hbw2⟩
  rcases haw1 with ⟨p1, l1, rfl, rfl, hI1⟩ | ⟨p1, l1, rfl, rfl, hI1⟩
  · obtain ⟨p2, rfl, hI2⟩ := adj_nat_left hbw1.symm
    have hp12 : p1 ≠ p2 := fun h => hab (by rw [h])
    obtain ⟨l2, rfl, hI1'⟩ := adj_cast_left haw2
    obtain ⟨l2', hweq, hI2'⟩ := adj_cast_left hbw2
    cases nat_inj hweq
    obtain ⟨l, _, huniq⟩ := hpp p1 p2 hp12
    have e1 := huniq l1 ⟨hI1, hI2⟩
    have e2 := huniq l2 ⟨hI1', hI2'⟩
    exact hw12 (by rw [e1, e2])
  · obtain ⟨l2, rfl, hI2⟩ := adj_cast_left hbw1.symm
    obtain ⟨p2, rfl, hI1'⟩ := adj_nat_left haw2
    obtain ⟨p2', hweq, hI2'⟩ := adj_nat_left hbw2
    cases cast_inj hweq
    have hp12 : p1 ≠ p2 := fun h => hw12 (by rw [h])
    obtain ⟨l, _, huniq⟩ := hpp p1 p2 hp12
    have e1 := huniq l1 ⟨hI1, hI1'⟩
    have e2 := huniq l2 ⟨hI2, hI2'⟩
    exact hab (by rw [e1, e2])

theorem incGraph_graphFun_eq {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    [DecidableRel (incGraph I).Adj] (z : Fin (N + N) → Bool) :
    graphFun (incGraph I) ∅ z =
      decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) := by
  apply Bool.eq_iff_iff.2
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or,
    decide_eq_true_eq]
  constructor
  · rintro ⟨u, v, huv, hu, hv⟩
    rcases huv with ⟨p, l, rfl, rfl, hI⟩ | ⟨p, l, rfl, rfl, hI⟩
    · exact ⟨p, l, hI, hu, hv⟩
    · exact ⟨p, l, hI, hv, hu⟩
  · rintro ⟨p, l, hI, hp, hl⟩
    exact ⟨Fin.castAdd N p, Fin.natAdd N l, Or.inl ⟨p, l, rfl, rfl, hI⟩, hp, hl⟩

theorem exists_leastAO {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : IsAO2 n C) (hF : circuitFun n C = graphFun G ∅) :
    ∃ C0 : Circuit, IsLeastAO G C0 ∧ C0.size ≤ C.size := by
  classical
  let P : ℕ → Prop := fun s => ∃ D : Circuit, IsAO2 n D ∧ circuitFun n D = graphFun G ∅ ∧ D.size = s
  have hex : ∃ s, P s := ⟨C.size, C, hC, hF, rfl⟩
  let s0 := Nat.find hex
  obtain ⟨C0, hC0AO, hC0F, hC0s⟩ := Nat.find_spec hex
  have hle : s0 ≤ C.size := Nat.find_min' hex ⟨C, hC, hF, rfl⟩
  refine ⟨C0, ⟨hC0AO, hC0F, fun D hD hDF => ?_⟩, ?_⟩
  · have := Nat.find_min' hex ⟨D, hD, hDF, rfl⟩
    omega
  · omega

def badEdges {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) :
    Finset (Fin n × Fin n) :=
  Finset.univ.filter fun e =>
    e.1 < e.2 ∧ G.Adj e.1 e.2 ∧ readsAtMost C n [e.1.val, e.2.val] 1 = false

theorem filter_pair_finRange {n : ℕ} (u v : Fin n) (huv : u < v) :
    (List.finRange n).filter (fun i => decide (i = u ∨ i = v)) = [u, v] := by
  have hpw : (List.finRange n).Pairwise (· < ·) := List.pairwise_lt_finRange n
  have hpf : ((List.finRange n).filter (fun i => decide (i = u ∨ i = v))).Pairwise (· < ·) :=
    hpw.filter _
  have hu : u ∈ (List.finRange n).filter (fun i => decide (i = u ∨ i = v)) :=
    List.mem_filter.2 ⟨List.mem_finRange u, by simp⟩
  have hv : v ∈ (List.finRange n).filter (fun i => decide (i = u ∨ i = v)) :=
    List.mem_filter.2 ⟨List.mem_finRange v, by simp⟩
  have hall : ∀ x ∈ (List.finRange n).filter (fun i => decide (i = u ∨ i = v)), x = u ∨ x = v :=
    fun x hx => by simpa [decide_eq_true_eq] using (List.mem_filter.1 hx).2
  generalize (List.finRange n).filter (fun i => decide (i = u ∨ i = v)) = l at hpf hu hv hall
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · simp at hu
  · simp only [List.mem_singleton] at hu hv
    exact absurd (hu.trans hv.symm) huv.ne
  · have hab : a < b := (List.pairwise_cons.1 hpf).1 b (by simp)
    have ha : a = u ∨ a = v := hall a (by simp)
    have hb : b = u ∨ b = v := hall b (by simp)
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact absurd hab (lt_irrefl _)
    · rfl
    · exact absurd (hab.trans huv) (lt_irrefl _)
    · exact absurd hab (lt_irrefl _)
  · have h1 := List.pairwise_cons.1 hpf
    have h2 := List.pairwise_cons.1 h1.2
    have hab : a < b := h1.1 b (by simp)
    have hbc : b < c := h2.1 c (by simp)
    have ha : a = u ∨ a = v := hall a (by simp)
    have hb : b = u ∨ b = v := hall b (by simp)
    have hc : c = u ∨ c = v := hall c (by simp)
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;> omega

theorem setList_pair {n : ℕ} (u v : Fin n) (huv : u < v) :
    setList ({u, v} : Finset (Fin n)) = [u.val, v.val] := by
  unfold setList
  have hfilter : ((List.finRange n).filter fun i => decide (i ∈ ({u, v} : Finset (Fin n)))) =
      (List.finRange n).filter fun i => decide (i = u ∨ i = v) := by
    apply List.filter_congr
    intro i _
    simp [Finset.mem_insert, Finset.mem_singleton]
  rw [hfilter, filter_pair_finRange u v huv]
  simp

theorem graphFun_empty_true {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → Bool) :
    graphFun G ∅ x = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true := by
  simp [graphFun]

theorem graphFun_empty_false {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → Bool) :
    graphFun G ∅ x = false ↔ ∀ u v : Fin n, G.Adj u v → x u = false ∨ x v = false := by
  rw [← Bool.not_eq_true, graphFun_empty_true]
  constructor
  · intro h u v huv
    by_cases hu : x u = true
    · right
      by_cases hv : x v = true
      · exact absurd ⟨u, v, huv, hu, hv⟩ h
      · exact Bool.eq_false_iff.2 hv
    · left
      exact Bool.eq_false_iff.2 hu
  · rintro h ⟨u, v, huv, hu, hv⟩
    rcases h u v huv with h1 | h1
    · rw [hu] at h1; exact Bool.false_ne_true h1.symm
    · rw [hv] at h1; exact Bool.false_ne_true h1.symm

theorem primeImplicant_iff_edge {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hF : circuitFun n C = graphFun G ∅) (S : Finset (Fin n))
    (hS : IsPrimeImplicant n C S) :
    ∃ u v : Fin n, u < v ∧ G.Adj u v ∧ S = {u, v} := by
  obtain ⟨h1, h2⟩ := hS
  rw [hF, graphFun_empty_true] at h1
  obtain ⟨a, b, hab, ha, hb⟩ := h1
  simp only [setInput, decide_eq_true_eq] at ha hb
  have hab_ne : a ≠ b := hab.ne
  have hsub : {a, b} ⊆ S := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact ha
    · exact hb
  have hSab : S = {a, b} := by
    by_contra hne
    have hss : {a, b} ∈ S.ssubsets := Finset.mem_ssubsets.2 (Finset.ssubset_iff_subset_ne.2 ⟨hsub, Ne.symm hne⟩)
    have hf := h2 {a, b} hss
    rw [hF, graphFun_empty_false] at hf
    rcases hf a b hab with ha' | hb'
    · simp [setInput] at ha'
    · simp [setInput] at hb'
  rcases lt_or_gt_of_ne hab_ne with hlt | hgt
  · exact ⟨a, b, hlt, hab, hSab⟩
  · refine ⟨b, a, hgt, hab.symm, ?_⟩
    rw [hSab, Finset.pair_comm]

theorem isRead1_of_badEdges_empty {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hF : circuitFun n C = graphFun G ∅) (hempty : badEdges G C = ∅) :
    IsReadK n C 1 := by
  intro S hS
  obtain ⟨u, v, huv, hadj, rfl⟩ := primeImplicant_iff_edge G C hF S hS
  rw [setList_pair u v huv]
  by_contra hf
  have hf' : readsAtMost C n [u.val, v.val] 1 = false := Bool.eq_false_iff.2 hf
  have hmem : (u, v) ∈ badEdges G C := by
    unfold badEdges
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, huv, hadj, hf'⟩
  rw [hempty] at hmem
  exact Finset.notMem_empty _ hmem

theorem output_gate_of_edge {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hF : circuitFun n C = graphFun G ∅) (u0 v0 : Fin n) (huv : G.Adj u0 v0) :
    ∃ o < C.gates.length, C.output = n + o := by
  by_cases hlt : C.output < n
  · exfalso
    let x : Fin n → Bool := fun i => decide (i.val = C.output)
    have hc : circuitFun n C x = true := by
      unfold circuitFun Circuit.eval
      rw [wires_getD_lt C x C.output hlt]
      simp [x]
    rw [hF, graphFun_empty_true] at hc
    obtain ⟨a, b, hab, ha, hb⟩ := hc
    simp only [x, decide_eq_true_eq] at ha hb
    exact hab.ne (Fin.ext (ha.trans hb.symm))
  · by_cases hge : n + C.gates.length ≤ C.output
    · exfalso
      have hc : circuitFun n C (pairInput u0 v0) = false := by
        unfold circuitFun Circuit.eval
        exact wires_getD_beyond C (pairInput u0 v0) C.output hge
      have ht : graphFun G ∅ (pairInput u0 v0) = true :=
        (graphFun_empty_true G _).2 ⟨u0, v0, huv, by simp [pairInput], by simp [pairInput]⟩
      rw [← hF, hc] at ht
      exact Bool.false_ne_true ht
    · exact ⟨C.output - n, by omega, by omega⟩

theorem impWire_belowF {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (w : ℕ) (hw : IsImpWire G C w) :
    ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD w false = true → graphFun G ∅ x = true :=
  hw.1

theorem find_core_of_bad_edge {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hF : circuitFun n C = graphFun G ∅)
    (handLow : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and → ∀ d : Fin 2,
      ¬ (∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD (opnd C k d) false = true →
        graphFun G ∅ x = true))
    (u0 v0 : Fin n) (huv : G.Adj u0 v0) (hbad : readsAtMost C n [u0.val, v0.val] 1 = false) :
    ∃ j0 : ℕ, IsCore G C j0 ∧ gateVal n C j0 (pairInput u0 v0) = true ∧
      ReadTwiceAt n C j0 u0 v0 := by
  have key : ∀ t : ℕ, ∀ j < C.gates.length, j = t → IsImpGate G C j →
      gateVal n C j (pairInput u0 v0) = true → ReadTwiceAt n C j u0 v0 →
      ∃ j0 : ℕ, IsCore G C j0 ∧ gateVal n C j0 (pairInput u0 v0) = true ∧
        ReadTwiceAt n C j0 u0 v0 := by
    intro t
    induction t using Nat.strong_induction_on with
    | _ t ih =>
      intro j hj ht himp hval hrt
      cases hop : (gateAt C j).op with
      | and =>
        have hnot : ¬ (IsImpOperand G C (opnd C j 0) ∧ IsImpOperand G C (opnd C j 1)) := by
          intro hpair
          obtain ⟨hn0, hbel0, _⟩ := hpair.1
          apply handLow j hj hop 0
          intro x hx
          apply hbel0 x
          unfold gateVal
          rwa [show n + (opnd C j 0 - n) = opnd C j 0 by omega]
        exact ⟨j, ⟨hj, himp, hnot, u0, v0, huv, hval, hrt⟩, hval, hrt⟩
      | or =>
        rcases (gateVal_or_iff C hAO j hj hop (pairInput u0 v0)).1 hval with hd0 | hd1
        · have hd : (C.wires (List.ofFn (pairInput u0 v0))).getD (opnd C j 0) false = true := hd0
          by_cases hlt : opnd C j 0 < n
          · exfalso
            rw [wires_getD_lt C (pairInput u0 v0) (opnd C j 0) hlt] at hd
            set y : Fin n := ⟨opnd C j 0, hlt⟩
            let uy : Fin n → Bool := fun i => decide (i = y)
            have hgy : gateVal n C j uy = true := by
              refine (gateVal_or_iff C hAO j hj hop uy).2 (Or.inl ?_)
              rw [wires_getD_lt C uy (opnd C j 0) hlt]
              simp [uy, y]
            have hFy := himp.1 uy hgy
            rw [graphFun_empty_true] at hFy
            obtain ⟨a, b, hab, ha, hb⟩ := hFy
            simp only [uy, decide_eq_true_eq] at ha hb
            exact hab.ne (ha.trans hb.symm)
          · have hltj := ao2_opnd_lt C hAO j hj 0
            set i := opnd C j 0 - n
            have hei : opnd C j 0 = n + i := by omega
            have hij : i < j := by omega
            have hil : i < C.gates.length := by omega
            have hvali : gateVal n C i (pairInput u0 v0) = true := by
              unfold gateVal
              rwa [← hei]
            have hbeli : BelowF G C i := by
              intro x hx
              apply himp.1 x
              refine (gateVal_or_iff C hAO j hj hop x).2 (Or.inl ?_)
              rw [hei]
              exact hx
            have himpi : IsImpGate G C i := ⟨hbeli, pairInput u0 v0, hvali⟩
            have hrti : ReadTwiceAt n C i u0 v0 := by
              by_contra hnf
              have htrue : readsAtMost (atGate n C i) n [u0.val, v0.val] 1 = true :=
                Bool.eq_true_of_not_eq_false hnf
              have := readsAtMost_or_mono C hAO [u0.val, v0.val] 1 j i hj hop 0 hei htrue
              unfold ReadTwiceAt at hrt
              rw [this] at hrt
              exact Bool.false_ne_true hrt.symm
            exact ih i (by omega) i hil rfl himpi hvali hrti
        · have hd : (C.wires (List.ofFn (pairInput u0 v0))).getD (opnd C j 1) false = true := hd1
          by_cases hlt : opnd C j 1 < n
          · exfalso
            rw [wires_getD_lt C (pairInput u0 v0) (opnd C j 1) hlt] at hd
            set y : Fin n := ⟨opnd C j 1, hlt⟩
            let uy : Fin n → Bool := fun i => decide (i = y)
            have hgy : gateVal n C j uy = true := by
              refine (gateVal_or_iff C hAO j hj hop uy).2 (Or.inr ?_)
              rw [wires_getD_lt C uy (opnd C j 1) hlt]
              simp [uy, y]
            have hFy := himp.1 uy hgy
            rw [graphFun_empty_true] at hFy
            obtain ⟨a, b, hab, ha, hb⟩ := hFy
            simp only [uy, decide_eq_true_eq] at ha hb
            exact hab.ne (ha.trans hb.symm)
          · have hltj := ao2_opnd_lt C hAO j hj 1
            set i := opnd C j 1 - n
            have hei : opnd C j 1 = n + i := by omega
            have hij : i < j := by omega
            have hil : i < C.gates.length := by omega
            have hvali : gateVal n C i (pairInput u0 v0) = true := by
              unfold gateVal
              rwa [← hei]
            have hbeli : BelowF G C i := by
              intro x hx
              apply himp.1 x
              refine (gateVal_or_iff C hAO j hj hop x).2 (Or.inr ?_)
              rw [hei]
              exact hx
            have himpi : IsImpGate G C i := ⟨hbeli, pairInput u0 v0, hvali⟩
            have hrti : ReadTwiceAt n C i u0 v0 := by
              by_contra hnf
              have htrue : readsAtMost (atGate n C i) n [u0.val, v0.val] 1 = true :=
                Bool.eq_true_of_not_eq_false hnf
              have := readsAtMost_or_mono C hAO [u0.val, v0.val] 1 j i hj hop 1 hei htrue
              unfold ReadTwiceAt at hrt
              rw [this] at hrt
              exact Bool.false_ne_true hrt.symm
            exact ih i (by omega) i hil rfl himpi hvali hrti
      | not => exact absurd (hAO.1 _ (gateAt_eq hj ▸ List.getElem_mem hj)) (by simp [hop])
      | mod m => exact absurd (hAO.1 _ (gateAt_eq hj ▸ List.getElem_mem hj)) (by simp [hop])
      | maj => exact absurd (hAO.1 _ (gateAt_eq hj ▸ List.getElem_mem hj)) (by simp [hop])
  obtain ⟨o, hol, hco⟩ := output_gate_of_edge G C hF u0 v0 huv
  have hvalo : gateVal n C o (pairInput u0 v0) = true := by
    have h1 : circuitFun n C (pairInput u0 v0) = true := by
      rw [hF, graphFun_empty_true]
      exact ⟨u0, v0, huv, by simp [pairInput], by simp [pairInput]⟩
    unfold gateVal
    rw [← hco]
    exact h1
  have hbelo : BelowF G C o := by
    intro x hx
    rw [← hF]
    unfold circuitFun Circuit.eval
    rw [hco]
    exact hx
  have hrto : ReadTwiceAt n C o u0 v0 := by
    unfold ReadTwiceAt atGate
    have hc : ({ C with output := n + o } : Circuit) = C := by
      cases C
      simp only [Circuit.mk.injEq, true_and]
      exact hco.symm
    rw [hc]
    exact hbad
  exact key o o hol rfl ⟨hbelo, pairInput u0 v0, hvalo⟩ hvalo hrto

theorem main
    (h_norm : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (s : Fin n → Bool) (C : Circuit),
      (∀ u v : Fin n, G.Adj u v → s u ≠ s v) → NoFourCycle G → (∃ u v : Fin n, G.Adj u v) →
      IsLeastAO G C →
      ∃ C' : Circuit, IsLeastAO G C' ∧
        (∀ k < C'.gates.length, (gateAt C' k).op = GateOp.and → ∀ d : Fin 2,
          ¬ (∀ x : Fin n → Bool, (C'.wires (List.ofFn x)).getD (opnd C' k d) false = true →
            graphFun G ∅ x = true)) ∧
        ((Finset.univ : Finset (Fin n × Fin n)).filter (fun e =>
          e.1 < e.2 ∧ G.Adj e.1 e.2 ∧ readsAtMost C' n [e.1.val, e.2.val] 1 = false)).card ≤
        ((Finset.univ : Finset (Fin n × Fin n)).filter (fun e =>
          e.1 < e.2 ∧ G.Adj e.1 e.2 ∧ readsAtMost C n [e.1.val, e.2.val] 1 = false)).card)
    (h_core_step : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (s : Fin n → Bool) (C : Circuit),
      (∀ u v : Fin n, G.Adj u v → s u ≠ s v) → NoFourCycle G → (∃ u v : Fin n, G.Adj u v) →
      IsLeastAO G C →
      (∃ j : ℕ, IsCore G C j) →
      ∃ D : Circuit, IsLeastAO G D ∧
        ((Finset.univ : Finset (Fin n × Fin n)).filter (fun e =>
          e.1 < e.2 ∧ G.Adj e.1 e.2 ∧ readsAtMost D n [e.1.val, e.2.val] 1 = false)).card <
        ((Finset.univ : Finset (Fin n × Fin n)).filter (fun e =>
          e.1 < e.2 ∧ G.Adj e.1 e.2 ∧ readsAtMost C n [e.1.val, e.2.val] 1 = false)).card) :
    ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit),
      2 ≤ q → N = q ^ 2 + q + 1 →
      (∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) →
      (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) →
      IsAO2 (N + N) C →
      (∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z =
        decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) →
      ∃ D : Circuit, IsAO2 (N + N) D ∧
        (∀ y : Fin (N + N) → Bool, circuitFun (N + N) D y =
          decide (∃ p l : Fin N, I p l ∧ y (Fin.castAdd N p) = true ∧ y (Fin.natAdd N l) = true)) ∧
        D.size ≤ C.size ∧ IsReadK (N + N) D 1 := by
  classical
  intro q N I _ C hq hN hl hpp hCAO hz
  let G : SimpleGraph (Fin (N + N)) := incGraph I
  let s : Fin (N + N) → Bool := fun a => decide (a.val < N)
  have hbip : ∀ u v : Fin (N + N), G.Adj u v → s u ≠ s v := incGraph_bipartite I
  have hC4 : NoFourCycle G := incGraph_noFourCycle I hpp
  have hne : ∃ u v : Fin (N + N), G.Adj u v := incGraph_nonempty_edge I hq hN hl
  have hCF : circuitFun (N + N) C = graphFun G ∅ := by
    funext z
    rw [hz z, incGraph_graphFun_eq I z]
  obtain ⟨C0, hC0least, hC0size⟩ := exists_leastAO G C hCAO hCF
  have ind : ∀ m : ℕ, ∀ C1 : Circuit, (badEdges G C1).card = m → IsLeastAO G C1 →
      ∃ D : Circuit, IsAO2 (N + N) D ∧ circuitFun (N + N) D = graphFun G ∅ ∧
        D.size ≤ C1.size ∧ IsReadK (N + N) D 1 := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro C1 hm hC1least
      obtain ⟨C', hC'least, handLow, hcard_le⟩ := h_norm (N + N) G s C1 hbip hC4 hne hC1least
      by_cases hempty : badEdges G C' = ∅
      · refine ⟨C', hC'least.1, hC'least.2.1, ?_, isRead1_of_badEdges_empty G C' hC'least.2.1 hempty⟩
        exact hC'least.2.2 C1 hC1least.1 hC1least.2.1
      · have hne_bad : (badEdges G C').Nonempty := Finset.nonempty_iff_ne_empty.2 hempty
        obtain ⟨⟨u0, v0⟩, hmem⟩ := hne_bad
        rw [badEdges, Finset.mem_filter] at hmem
        obtain ⟨_, huvlt, huvadj, hrt⟩ := hmem
        obtain ⟨j0, hcore, _, _⟩ :=
          find_core_of_bad_edge G C' hC'least.1 hC'least.2.1 handLow u0 v0 huvadj hrt
        obtain ⟨D1, hD1least, hD1lt⟩ :=
          h_core_step (N + N) G s C' hbip hC4 hne hC'least ⟨j0, hcore⟩
        have hlt_m : (badEdges G D1).card < m := by
          rw [← hm]
          exact lt_of_lt_of_le hD1lt hcard_le
        obtain ⟨D, hDAO, hDF, hDsize, hDread⟩ := ih (badEdges G D1).card hlt_m D1 rfl hD1least
        refine ⟨D, hDAO, hDF, ?_, hDread⟩
        have hs1 : D.size ≤ D1.size := hDsize
        have hs2 : D1.size ≤ C'.size := hD1least.2.2 C' hC'least.1 hC'least.2.1
        have hs3 : C'.size ≤ C1.size := hC'least.2.2 C1 hC1least.1 hC1least.2.1
        omega
  obtain ⟨D, hDAO, hDF, hDsize, hDread⟩ := ind (badEdges G C0).card C0 rfl hC0least
  refine ⟨D, hDAO, fun y => ?_, hDsize.trans hC0size, hDread⟩
  have := congrFun hDF y
  rw [incGraph_graphFun_eq I y] at this
  exact this

end PEqualNP.Outside.R_meta_2583_1

theorem PEqualNP.Outside.R_meta_2583_1
    (h_norm : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (s : Fin n → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ u v : Fin n, G.Adj u v → s u ≠ s v) → PEqualNP.TopForm.NoFourCycle G →
      (∃ u v : Fin n, G.Adj u v) → PEqualNP.TopForm.IsLeastAO G C →
      ∃ C' : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsLeastAO G C' ∧
        (∀ k < C'.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C' k).op =
          PEqualNP.CircuitLowerBounds.GateOp.and → ∀ d : Fin 2,
          ¬ (∀ x : Fin n → Bool, (C'.wires (List.ofFn x)).getD (PEqualNP.TopForm.opnd C' k d) false = true →
            PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = true)) ∧
        ((Finset.univ : Finset (Fin n × Fin n)).filter (fun e =>
          e.1 < e.2 ∧ G.Adj e.1 e.2 ∧ PEqualNP.ReadK.readsAtMost C' n [e.1.val, e.2.val] 1 = false)).card ≤
        ((Finset.univ : Finset (Fin n × Fin n)).filter (fun e =>
          e.1 < e.2 ∧ G.Adj e.1 e.2 ∧ PEqualNP.ReadK.readsAtMost C n [e.1.val, e.2.val] 1 = false)).card)
    (h_core_step : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (s : Fin n → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ u v : Fin n, G.Adj u v → s u ≠ s v) → PEqualNP.TopForm.NoFourCycle G →
      (∃ u v : Fin n, G.Adj u v) → PEqualNP.TopForm.IsLeastAO G C →
      (∃ j : ℕ, PEqualNP.Core.IsCore G C j) →
      ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsLeastAO G D ∧
        ((Finset.univ : Finset (Fin n × Fin n)).filter (fun e =>
          e.1 < e.2 ∧ G.Adj e.1 e.2 ∧ PEqualNP.ReadK.readsAtMost D n [e.1.val, e.2.val] 1 = false)).card <
        ((Finset.univ : Finset (Fin n × Fin n)).filter (fun e =>
          e.1 < e.2 ∧ G.Adj e.1 e.2 ∧ PEqualNP.ReadK.readsAtMost C n [e.1.val, e.2.val] 1 = false)).card) :
    ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ q → N = q ^ 2 + q + 1 → (∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) → (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) → PEqualNP.TopForm.IsAO2 (N + N) C → (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 (N + N) D ∧ (∀ y : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) D y = decide (∃ p l : Fin N, I p l ∧ y (Fin.castAdd N p) = true ∧ y (Fin.natAdd N l) = true)) ∧ D.size ≤ C.size ∧ PEqualNP.ReadK.IsReadK (N + N) D 1 := by
  exact PEqualNP.Outside.R_meta_2583_1.main h_norm h_core_step
