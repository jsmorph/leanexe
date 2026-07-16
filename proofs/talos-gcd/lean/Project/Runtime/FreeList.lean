import Project.Runtime.Tree

namespace Project.Runtime

open Wasm Project.Common

structure FreeNode where
  root : UInt64
  capacity : UInt64
  deriving Inhabited

def freeHead : List FreeNode → UInt64
  | [] => 0
  | node :: _ => node.root

def scanRemaining : List FreeNode → UInt64 → Nat
  | [], _ => 0
  | node :: rest, current =>
      if node.root = current then
        (node :: rest).length
      else
        scanRemaining rest current

def takeFirstFit (need : UInt64) : List FreeNode →
    Option (FreeNode × List FreeNode)
  | [] => none
  | node :: rest =>
      if need ≤ node.capacity then
        some (node, rest)
      else
        match takeFirstFit need rest with
        | none => none
        | some (chosen, rest') => some (chosen, node :: rest')

structure FreeChoice where
  previous : UInt64
  node : FreeNode
  next : UInt64
  remaining : List FreeNode

def previousRoot (initial : UInt64) : List FreeNode → UInt64
  | [] => initial
  | node :: rest => previousRoot node.root rest

theorem previousRoot_append_singleton (initial : UInt64)
    (nodes : List FreeNode) (node : FreeNode) :
    previousRoot initial (nodes ++ [node]) = node.root := by
  induction nodes generalizing initial with
  | nil => rfl
  | cons head rest ih => exact ih head.root

def takeFirstFitFrom (previous need : UInt64) : List FreeNode →
    Option FreeChoice
  | [] => none
  | node :: rest =>
      if need ≤ node.capacity then
        some { previous, node, next := freeHead rest, remaining := rest }
      else
        match takeFirstFitFrom node.root need rest with
        | none => none
        | some choice => some { choice with remaining := node :: choice.remaining }

theorem takeFirstFitFrom_project (previous need : UInt64)
    (nodes : List FreeNode) :
    (takeFirstFitFrom previous need nodes).map
        (fun choice => (choice.node, choice.remaining)) =
      takeFirstFit need nodes := by
  induction nodes generalizing previous with
  | nil => rfl
  | cons node rest ih =>
      simp only [takeFirstFitFrom, takeFirstFit]
      split
      · rfl
      · rw [← ih node.root]
        cases takeFirstFitFrom node.root need rest <;> rfl

theorem takeFirstFit_none_iff (need : UInt64) (nodes : List FreeNode) :
    takeFirstFit need nodes = none ↔
      ∀ node ∈ nodes, node.capacity < need := by
  induction nodes with
  | nil => simp [takeFirstFit]
  | cons node rest ih =>
      by_cases hfit : need ≤ node.capacity
      · rw [takeFirstFit, if_pos hfit]
        constructor
        · intro h
          simp at h
        · intro h
          have hlt := h node List.mem_cons_self
          rw [UInt64.le_iff_toNat_le] at hfit
          rw [UInt64.lt_iff_toNat_lt] at hlt
          omega
      · rw [takeFirstFit, if_neg hfit]
        have hnone :
            (match takeFirstFit need rest with
              | none => none
              | some (chosen, rest') => some (chosen, node :: rest')) = none ↔
            takeFirstFit need rest = none := by
          cases h : takeFirstFit need rest <;> simp
        rw [hnone, ih]
        constructor
        · intro h current hmem
          rcases List.mem_cons.mp hmem with rfl | htail
          · rw [UInt64.le_iff_toNat_le] at hfit
            rw [UInt64.lt_iff_toNat_lt]
            omega
          · exact h current htail
        · intro h current hmem
          exact h current (List.mem_cons_of_mem _ hmem)

theorem takeFirstFit_some_capacity {need : UInt64} {nodes rest : List FreeNode}
    {node : FreeNode} (h : takeFirstFit need nodes = some (node, rest)) :
    need ≤ node.capacity := by
  induction nodes generalizing node rest with
  | nil => simp [takeFirstFit] at h
  | cons current nodes ih =>
      simp only [takeFirstFit] at h
      split at h
      · have hpair : (current, nodes) = (node, rest) := Option.some.inj h
        have hnode : current = node := congrArg Prod.fst hpair
        simpa [hnode] using ‹need ≤ current.capacity›
      · split at h
        · contradiction
        · rename_i chosen tail htake
          have hpair : chosen = node ∧ current :: tail = rest := by
            simpa using h
          rw [← hpair.1]
          exact ih htake

theorem takeFirstFit_some_mem {need : UInt64} {nodes rest : List FreeNode}
    {node : FreeNode} (h : takeFirstFit need nodes = some (node, rest)) :
    node ∈ nodes := by
  induction nodes generalizing node rest with
  | nil => simp [takeFirstFit] at h
  | cons current nodes ih =>
      simp only [takeFirstFit] at h
      split at h
      · have hpair : (current, nodes) = (node, rest) := Option.some.inj h
        have hnode : current = node := congrArg Prod.fst hpair
        rw [← hnode]
        exact List.mem_cons_self
      · split at h
        · contradiction
        · rename_i chosen tail htake
          have hpair : chosen = node ∧ current :: tail = rest := by
            simpa using h
          rw [← hpair.1]
          exact List.mem_cons_of_mem _ (ih htake)

theorem takeFirstFit_some_length {need : UInt64} {nodes rest : List FreeNode}
    {node : FreeNode} (h : takeFirstFit need nodes = some (node, rest)) :
    rest.length + 1 = nodes.length := by
  induction nodes generalizing node rest with
  | nil => simp [takeFirstFit] at h
  | cons current nodes ih =>
      simp only [takeFirstFit] at h
      split at h
      · have hpair : (current, nodes) = (node, rest) := Option.some.inj h
        have hrest : nodes = rest := congrArg Prod.snd hpair
        rw [← hrest]
        simp
      · split at h
        · contradiction
        · rename_i chosen tail htake
          have hpair : chosen = node ∧ current :: tail = rest := by
            simpa using h
          rw [← hpair.2]
          have hlen := ih htake
          simp only [List.length_cons]
          omega

theorem takeFirstFitFrom_some_capacity {previous need : UInt64}
    {nodes : List FreeNode} {choice : FreeChoice}
    (h : takeFirstFitFrom previous need nodes = some choice) :
    need ≤ choice.node.capacity := by
  have hproject := congrArg
    (Option.map fun choice : FreeChoice => (choice.node, choice.remaining)) h
  rw [takeFirstFitFrom_project] at hproject
  exact takeFirstFit_some_capacity hproject

theorem takeFirstFitFrom_some_mem {previous need : UInt64}
    {nodes : List FreeNode} {choice : FreeChoice}
    (h : takeFirstFitFrom previous need nodes = some choice) :
    choice.node ∈ nodes := by
  have hproject := congrArg
    (Option.map fun choice : FreeChoice => (choice.node, choice.remaining)) h
  rw [takeFirstFitFrom_project] at hproject
  exact takeFirstFit_some_mem hproject

theorem takeFirstFitFrom_some_length {previous need : UInt64}
    {nodes : List FreeNode} {choice : FreeChoice}
    (h : takeFirstFitFrom previous need nodes = some choice) :
    choice.remaining.length + 1 = nodes.length := by
  have hproject := congrArg
    (Option.map fun choice : FreeChoice => (choice.node, choice.remaining)) h
  rw [takeFirstFitFrom_project] at hproject
  exact takeFirstFit_some_length hproject

theorem takeFirstFitFrom_some_decompose {previous need : UInt64}
    {nodes : List FreeNode} {choice : FreeChoice}
    (h : takeFirstFitFrom previous need nodes = some choice) :
    ∃ skipped tail : List FreeNode,
      nodes = skipped ++ (choice.node :: tail) ∧
      choice.previous = previousRoot previous skipped ∧
      choice.next = freeHead tail ∧
      choice.remaining = skipped ++ tail ∧
      ∀ node ∈ skipped, node.capacity < need := by
  induction nodes generalizing previous choice with
  | nil => simp [takeFirstFitFrom] at h
  | cons node rest ih =>
      simp only [takeFirstFitFrom] at h
      split at h
      · have hchoice :
            { previous := previous, node := node, next := freeHead rest,
              remaining := rest } = choice := Option.some.inj h
        subst choice
        exact ⟨[], rest, by simp [previousRoot]⟩
      · rename_i hnotFit
        cases hrest : takeFirstFitFrom node.root need rest with
        | none => simp [hrest] at h
        | some restChoice =>
            simp only [hrest] at h
            have hchoice :
                { restChoice with remaining := node :: restChoice.remaining } =
                  choice := Option.some.inj h
            subst choice
            obtain ⟨skipped, tail, hnodes, hprevious, hnext, hremaining,
              hsmall⟩ := ih hrest
            refine ⟨node :: skipped, tail, ?_, ?_, ?_, ?_, ?_⟩
            · simp [hnodes]
            · simpa [previousRoot] using hprevious
            · exact hnext
            · simp [hremaining]
            · intro other hmem
              rcases List.mem_cons.mp hmem with rfl | htail
              · rw [UInt64.lt_iff_toNat_lt]
                rw [UInt64.le_iff_toNat_le] at hnotFit
                omega
              · exact hsmall other htail

def FreeNode.region (node : FreeNode) : Nat × Nat :=
  (node.root.toNat - 48, 48 + node.capacity.toNat)

inductive FreeListAt : Mem → List FreeNode → Prop where
  | nil {mem : Mem} : FreeListAt mem []
  | cons {mem : Mem} {node : FreeNode} {rest : List FreeNode} :
      48 ≤ node.root.toNat →
      node.root.toNat + node.capacity.toNat < 4294967296 →
      node.root.toNat + node.capacity.toNat ≤ mem.pages * 65536 →
      mem.read64 ((node.root - 40).toUInt32) = 0 →
      mem.read64 ((node.root - 32).toUInt32) = node.capacity →
      mem.read64 ((node.root - 8).toUInt32) = freeHead rest →
      (∀ other ∈ rest,
        regionsDisjoint node.region other.region) →
      FreeListAt mem rest →
      FreeListAt mem (node :: rest)

theorem FreeListAt.head_ne_zero {mem : Mem} {node : FreeNode}
    {rest : List FreeNode} (h : FreeListAt mem (node :: rest)) :
    freeHead (node :: rest) ≠ 0 := by
  cases h with
  | cons hp =>
      simp only [freeHead]
      intro hzero
      have := congrArg UInt64.toNat hzero
      simp at this
      omega

theorem FreeListAt.mem_bounds {mem : Mem} {nodes : List FreeNode}
    (h : FreeListAt mem nodes) {node : FreeNode} (hmem : node ∈ nodes) :
    48 ≤ node.root.toNat ∧
    node.root.toNat + node.capacity.toNat < 4294967296 ∧
    node.root.toNat + node.capacity.toNat ≤ mem.pages * 65536 := by
  induction h with
  | nil => simp at hmem
  | cons hp h32 hfit _ _ _ _ _ ih =>
      rcases List.mem_cons.mp hmem with rfl | htail
      · exact ⟨hp, h32, hfit⟩
      · exact ih htail

theorem FreeNode.read64_write64_disjoint (mem : Mem)
    (writer reader : FreeNode) (writeOffset readOffset value : UInt64)
    (hWriter48 : 48 ≤ writer.root.toNat)
    (hWriter32 : writer.root.toNat + writer.capacity.toNat < 4294967296)
    (hReader48 : 48 ≤ reader.root.toNat)
    (hReader32 : reader.root.toNat + reader.capacity.toNat < 4294967296)
    (hWriteLow : 8 ≤ writeOffset.toNat)
    (hWriteHigh : writeOffset.toNat ≤ 48)
    (hReadLow : 8 ≤ readOffset.toNat)
    (hReadHigh : readOffset.toNat ≤ 48)
    (hsep : regionsDisjoint writer.region reader.region) :
    (mem.write64 ((writer.root - writeOffset).toUInt32) value).read64
        ((reader.root - readOffset).toUInt32) =
      mem.read64 ((reader.root - readOffset).toUInt32) := by
  apply read64_write64_ne
  rw [toUInt32_toNat, toUInt32_toNat,
    toNat_sub_le _ _ (by omega), toNat_sub_le _ _ (by omega),
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  unfold regionsDisjoint FreeNode.region at hsep
  omega

theorem FreeListAt.roots_ne_zero {mem : Mem} {nodes : List FreeNode}
    (h : FreeListAt mem nodes) :
    ∀ node ∈ nodes, node.root ≠ 0 := by
  intro node hmem
  have hbound := h.mem_bounds hmem
  intro hzero
  have := congrArg UInt64.toNat hzero
  simp at this
  omega

theorem FreeListAt.roots_nodup {mem : Mem} {nodes : List FreeNode}
    (h : FreeListAt mem nodes) :
    (nodes.map FreeNode.root).Nodup := by
  induction nodes with
  | nil => exact .nil
  | cons node rest ih =>
      cases h with
      | cons hp h32 hfit hrc hcapacity hnext hsep htail =>
          rw [List.map_cons]
          apply List.Nodup.cons
          · intro hmem
            obtain ⟨other, hother, hroot⟩ := List.mem_map.mp hmem
            have hdisjoint := hsep other hother
            unfold regionsDisjoint FreeNode.region at hdisjoint
            rw [← hroot] at hdisjoint
            omega
          · exact ih htail

private theorem scanRemaining_append (visited remaining : List FreeNode)
    (hNodup : ((visited ++ remaining).map FreeNode.root).Nodup)
    (hNonzero : ∀ node ∈ visited ++ remaining, node.root ≠ 0) :
    scanRemaining (visited ++ remaining) (freeHead remaining) =
      remaining.length := by
  induction visited with
  | nil => cases remaining <;> simp [scanRemaining, freeHead]
  | cons node visited ih =>
      have hNodupTail :
          ((visited ++ remaining).map FreeNode.root).Nodup := by
        simpa using hNodup.tail
      have hNonzeroTail :
          ∀ other ∈ visited ++ remaining, other.root ≠ 0 := by
        intro other hmem
        exact hNonzero other (List.mem_cons_of_mem _ hmem)
      have hne : node.root ≠ freeHead remaining := by
        cases remaining with
        | nil =>
            simpa [freeHead] using
              hNonzero node (List.mem_cons_self)
        | cons first rest =>
            intro heq
            have hrootMem :
                node.root ∈ (visited ++ first :: rest).map FreeNode.root := by
              rw [heq]
              exact List.mem_map.mpr ⟨first,
                List.mem_append_right visited List.mem_cons_self, rfl⟩
            have hNodupCons :
                (node.root :: (visited ++ first :: rest).map
                  FreeNode.root).Nodup := by
              simpa using hNodup
            cases hNodupCons with
            | cons hnotMem _ => exact (hnotMem node.root hrootMem) rfl
      simp only [List.cons_append, scanRemaining, hne, if_false]
      exact ih hNodupTail hNonzeroTail

theorem FreeListAt.scanRemaining_suffix {mem : Mem}
    {nodes visited remaining : List FreeNode} (h : FreeListAt mem nodes)
    (hsplit : nodes = visited ++ remaining) :
    scanRemaining nodes (freeHead remaining) = remaining.length := by
  subst nodes
  exact scanRemaining_append visited remaining h.roots_nodup h.roots_ne_zero

theorem FreeListAt.frame {mem mem' : Mem} {nodes : List FreeNode}
    (hpages : mem'.pages = mem.pages)
    (hread : ∀ node ∈ nodes, ∀ offset : UInt64,
      offset = 40 ∨ offset = 32 ∨ offset = 8 →
      mem'.read64 ((node.root - offset).toUInt32) =
        mem.read64 ((node.root - offset).toUInt32))
    (h : FreeListAt mem nodes) : FreeListAt mem' nodes := by
  induction nodes with
  | nil => exact .nil
  | cons node rest ih =>
      cases h with
      | cons hp h32 hfit hrc hcapacity hnext hsep htail =>
          refine .cons hp h32 ?_ ?_ ?_ ?_ hsep ?_
          · rw [hpages]
            exact hfit
          · rw [hread node (List.mem_cons_self) 40 (by simp)]
            exact hrc
          · rw [hread node (List.mem_cons_self) 32 (by simp)]
            exact hcapacity
          · rw [hread node (List.mem_cons_self) 8 (by simp)]
            exact hnext
          · apply ih
            · intro other hother offset hoffset
              exact hread other (List.mem_cons_of_mem _ hother) offset hoffset
            · exact htail

theorem FreeListAt.frame_write64_disjoint {mem : Mem}
    {nodes : List FreeNode} {writer : FreeNode} {writeOffset value : UInt64}
    (hWriter48 : 48 ≤ writer.root.toNat)
    (hWriter32 : writer.root.toNat + writer.capacity.toNat < 4294967296)
    (hWriteLow : 8 ≤ writeOffset.toNat)
    (hWriteHigh : writeOffset.toNat ≤ 48)
    (hsep : ∀ node ∈ nodes, regionsDisjoint writer.region node.region)
    (h : FreeListAt mem nodes) :
    FreeListAt (mem.write64 ((writer.root - writeOffset).toUInt32) value)
      nodes := by
  refine FreeListAt.frame (mem := mem)
    (mem' := mem.write64 ((writer.root - writeOffset).toUInt32) value)
    rfl ?_ h
  intro node hmem readOffset hRead
  obtain ⟨hReader48, hReader32, _⟩ := h.mem_bounds hmem
  rcases hRead with rfl | rfl | rfl
  all_goals
    apply writer.read64_write64_disjoint mem node <;>
      first | assumption | decide | exact hsep node hmem

theorem FreeListAt.selected_disjoint_after {mem : Mem}
    {skipped tail : List FreeNode} {selected : FreeNode}
    (h : FreeListAt mem (skipped ++ selected :: tail)) :
    ∀ node ∈ skipped ++ tail,
      regionsDisjoint selected.region node.region := by
  induction skipped with
  | nil =>
      simp only [List.nil_append] at h ⊢
      cases h with
      | cons _ _ _ _ _ _ hsep _ => exact hsep
  | cons head rest ih =>
      simp only [List.cons_append] at h ⊢
      cases h with
      | cons _ _ _ _ _ _ hsep htail =>
          intro node hmem
          rcases List.mem_cons.mp hmem with rfl | hrest
          · apply regionsDisjoint_symm
            exact hsep selected
              (List.mem_append_right rest List.mem_cons_self)
          · exact ih htail node hrest

private theorem FreeListAt.unlink_after {mem : Mem}
    {prior tail : List FreeNode} {previous selected : FreeNode}
    (h : FreeListAt mem (prior ++ previous :: selected :: tail)) :
    FreeListAt
      (mem.write64 ((previous.root - 8).toUInt32) (freeHead tail))
      (prior ++ previous :: tail) := by
  induction prior with
  | nil =>
      simp only [List.nil_append] at h ⊢
      cases h with
      | cons hp h32 hfit hrc hcapacity _ hsep hrest =>
          cases hrest with
          | cons _ _ _ _ _ _ _ htail =>
              have htail' :
                  FreeListAt
                    (mem.write64 ((previous.root - 8).toUInt32)
                      (freeHead tail)) tail :=
                htail.frame_write64_disjoint
                  (writer := previous) (writeOffset := 8)
                  (value := freeHead tail) hp h32
                  (by decide) (by decide)
                  (fun node hmem =>
                    hsep node (List.mem_cons_of_mem selected hmem))
              refine .cons hp h32 ?_ ?_ ?_ ?_ ?_ htail'
              · exact hfit
              · rw [read64_write64_ne]
                · exact hrc
                · rw [toUInt32_toNat, toUInt32_toNat,
                    toNat_sub_le _ _
                      (by norm_num [UInt64.toNat_ofNat]; omega),
                    toNat_sub_le _ _
                      (by norm_num [UInt64.toNat_ofNat]; omega),
                    Nat.mod_eq_of_lt (by omega),
                    Nat.mod_eq_of_lt (by omega)]
                  norm_num [UInt64.toNat_ofNat] at *
                  omega
              · rw [read64_write64_ne]
                · exact hcapacity
                · rw [toUInt32_toNat, toUInt32_toNat,
                    toNat_sub_le _ _
                      (by norm_num [UInt64.toNat_ofNat]; omega),
                    toNat_sub_le _ _
                      (by norm_num [UInt64.toNat_ofNat]; omega),
                    Nat.mod_eq_of_lt (by omega),
                    Nat.mod_eq_of_lt (by omega)]
                  norm_num [UInt64.toNat_ofNat] at *
                  omega
              · exact Mem.read64_write64_same mem
                  ((previous.root - 8).toUInt32) (freeHead tail)
              · intro node hmem
                exact hsep node (List.mem_cons_of_mem selected hmem)
  | cons head prior ih =>
      simp only [List.cons_append] at h ⊢
      cases h with
      | cons hp h32 hfit hrc hcapacity hnext hsep htail =>
          have hPreviousMem :
              previous ∈ prior ++ previous :: selected :: tail :=
            List.mem_append_right prior List.mem_cons_self
          obtain ⟨hPrevious48, hPrevious32, _⟩ :=
            htail.mem_bounds hPreviousMem
          have hPreviousHead :
              regionsDisjoint previous.region head.region :=
            regionsDisjoint_symm (hsep previous hPreviousMem)
          have hFreeHead :
              freeHead (prior ++ previous :: selected :: tail) =
                freeHead (prior ++ previous :: tail) := by
            cases prior <;> rfl
          have hread (offset : UInt64)
              (hLow : 8 ≤ offset.toNat) (hHigh : offset.toNat ≤ 48) :
              (mem.write64 ((previous.root - 8).toUInt32)
                  (freeHead tail)).read64
                    ((head.root - offset).toUInt32) =
                mem.read64 ((head.root - offset).toUInt32) :=
            previous.read64_write64_disjoint mem head 8 offset
              (freeHead tail) hPrevious48 hPrevious32 hp h32
              (by decide) (by decide) hLow hHigh hPreviousHead
          refine .cons hp h32 ?_ ?_ ?_ ?_ ?_ (ih htail)
          · exact hfit
          · rw [hread 40 (by decide) (by decide)]
            exact hrc
          · rw [hread 32 (by decide) (by decide)]
            exact hcapacity
          · rw [hread 8 (by decide) (by decide)]
            rw [← hFreeHead]
            exact hnext
          · intro node hmem
            apply hsep node
            rcases List.mem_append.mp hmem with hprefix | htailMem
            · exact List.mem_append_left _ hprefix
            · rcases List.mem_cons.mp htailMem with rfl | htailMem
              · exact List.mem_append_right prior List.mem_cons_self
              · exact List.mem_append_right prior
                  (List.mem_cons_of_mem previous
                    (List.mem_cons_of_mem selected htailMem))

def unlinkFreeChoice (mem : Mem) (choice : FreeChoice) : Mem :=
  if choice.previous = 0 then
    mem
  else
    mem.write64 ((choice.previous - 8).toUInt32) choice.next

theorem FreeListAt.unlink_takeFirstFitFrom {mem : Mem}
    {nodes : List FreeNode} {need : UInt64} {choice : FreeChoice}
    (hList : FreeListAt mem nodes)
    (hTake : takeFirstFitFrom 0 need nodes = some choice) :
    FreeListAt (unlinkFreeChoice mem choice) choice.remaining := by
  obtain ⟨skipped, tail, hnodes, hprevious, hnext, hremaining, _⟩ :=
    takeFirstFitFrom_some_decompose hTake
  subst nodes
  by_cases hSkipped : skipped = []
  · subst skipped
    simp only [previousRoot] at hprevious
    simp only [List.nil_append] at hList
    cases hList with
    | cons _ _ _ _ _ _ _ htail =>
        simpa [unlinkFreeChoice, hprevious, hremaining] using htail
  · let predecessor := skipped.getLast hSkipped
    have hsplit : skipped.dropLast ++ [predecessor] = skipped :=
      List.dropLast_append_getLast hSkipped
    have hPrevious : choice.previous = predecessor.root := by
      rw [hprevious, ← hsplit, previousRoot_append_singleton]
    have hPredecessorMem : predecessor ∈ skipped ++ choice.node :: tail := by
      rw [← hsplit]
      simp
    have hPreviousNonzero : choice.previous ≠ 0 := by
      rw [hPrevious]
      exact hList.roots_ne_zero predecessor hPredecessorMem
    have hList' :
        FreeListAt mem
          (skipped.dropLast ++ predecessor :: choice.node :: tail) := by
      rw [← hsplit] at hList
      simpa [List.append_assoc] using hList
    have hUnlinked := FreeListAt.unlink_after hList'
    have hRemaining' :
        choice.remaining = skipped.dropLast ++ predecessor :: tail := by
      calc
        choice.remaining = skipped ++ tail := hremaining
        _ = (skipped.dropLast ++ [predecessor]) ++ tail := by rw [hsplit]
        _ = skipped.dropLast ++ predecessor :: tail := by
          simp [List.append_assoc]
    rw [hRemaining', unlinkFreeChoice, if_neg hPreviousNonzero,
      hPrevious, hnext]
    exact hUnlinked

theorem FreeListAt.takeFirstFitFrom_node_disjoint {mem : Mem}
    {nodes : List FreeNode} {previous need : UInt64} {choice : FreeChoice}
    (hList : FreeListAt mem nodes)
    (hTake : takeFirstFitFrom previous need nodes = some choice) :
    ∀ node ∈ choice.remaining,
      regionsDisjoint choice.node.region node.region := by
  obtain ⟨skipped, tail, hnodes, _, _, hremaining, _⟩ :=
    takeFirstFitFrom_some_decompose hTake
  subst nodes
  simpa [hremaining] using hList.selected_disjoint_after

end Project.Runtime
