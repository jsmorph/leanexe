import Verified.Wasi.HostTotal
import Verified.Wasi.OracleSys

/-! When `hostSpecWith host calls` can be satisfied.  `Host.TotalFor` extends `Host.Total` with a
permitted reply to every fitting, accepted request of each call in `calls`, and such a host has a
Talos host environment satisfying `hostSpecWith host calls`, built from the oracles of `OracleHost`
and `OracleSys`.  Conversely, every host environment satisfying `hostSpecWith host calls` answers
each fitting, accepted request whose inputs and output regions fit below `2^32` when laid out one
after another from address 16, with result words and reported regions at multiples of their
alignments.  A theorem that assumes such an environment is vacuous for a host without those
replies. -/

namespace Verified.Wasi

open Wasm LeanExe.Wasi

/-- The least multiple of `align` at or above `address`, or `address` when `align` is 0. -/
def alignUp (address align : Nat) : Nat := address + (align - address % align) % align

/-- The address after the inputs and output regions of a request laid out from `start` in
parameter order: an input or an output buffer at the address reached, and a result word or a
reported region at the next multiple of its alignment.  `sizes` holds the sizes of the reported
regions.  A record has no layout here: the end of a request with a record lies past `2^32`, so
`Host.AnswersFor` asks nothing of a call with a record. -/
def layoutEnd : List Param → List Nat → List Arg → Nat → Nat
  | [], _, _, start => start
  | .word32 :: params, sizes, args, start
  | .enum32 _ :: params, sizes, args, start
  | .flags32 _ :: params, sizes, args, start
  | .flags64 _ :: params, sizes, args, start
  | .word64 :: params, sizes, args, start => layoutEnd params sizes args.tail start
  | .record .. :: _, _, _, start => start + 2 ^ 32 + 1
  | .input :: params, sizes, args, start =>
    layoutEnd params sizes args.tail (start + (args.head?.map Arg.length).getD 0)
  | .output :: params, sizes, args, start =>
    layoutEnd params sizes args.tail (start + (args.head?.map Arg.capacity).getD 0)
  | .result32 :: params, sizes, args, start => layoutEnd params sizes args (alignUp start 4 + 4)
  | .result64 :: params, sizes, args, start => layoutEnd params sizes args (alignUp start 8 + 8)
  | .reported _ align _ :: params, sizes, args, start =>
    layoutEnd params sizes.tail args (alignUp start align + sizes.headD 0)

/-- The pointers of the layout that `layoutEnd` describes, in parameter order. -/
def layoutPointers : List Param → List Nat → List Arg → Nat → List UInt32
  | [], _, _, _ => []
  | .word32 :: params, sizes, args, start
  | .enum32 _ :: params, sizes, args, start
  | .flags32 _ :: params, sizes, args, start
  | .flags64 _ :: params, sizes, args, start
  | .word64 :: params, sizes, args, start => layoutPointers params sizes args.tail start
  | .record .. :: _, _, _, _ => []
  | .input :: params, sizes, args, start =>
    UInt32.ofNat start ::
      layoutPointers params sizes args.tail (start + (args.head?.map Arg.length).getD 0)
  | .output :: params, sizes, args, start =>
    UInt32.ofNat start ::
      layoutPointers params sizes args.tail (start + (args.head?.map Arg.capacity).getD 0)
  | .result32 :: params, sizes, args, start =>
    UInt32.ofNat (alignUp start 4) :: layoutPointers params sizes args (alignUp start 4 + 4)
  | .result64 :: params, sizes, args, start =>
    UInt32.ofNat (alignUp start 8) :: layoutPointers params sizes args (alignUp start 8 + 8)
  | .reported _ align _ :: params, sizes, args, start =>
    UInt32.ofNat (alignUp start align) ::
      layoutPointers params sizes.tail args (alignUp start align + sizes.headD 0)

/-- A 4 GiB memory holding each input of a request at its pointer. -/
def layoutMemory (params : List Param) (args : List Arg) (pointers : List UInt32) : Mem :=
  placeAll (Mem.empty 65536) (inputPlaces params args pointers)

theorem le_alignUp (address align : Nat) : address ≤ alignUp address align :=
  Nat.le_add_right _ _

theorem alignUp_mod (address : Nat) {align : Nat} (positive : 0 < align) :
    alignUp address align % align = 0 := by
  unfold alignUp
  have split := Nat.div_add_mod address align
  have below := Nat.mod_lt address positive
  generalize address / align = quotient at split
  generalize address % align = rest at split below ⊢
  subst split
  rcases Nat.eq_zero_or_pos rest with rfl | pos
  · simp
  · rw [Nat.mod_eq_of_lt (by omega : align - rest < align),
      show align * quotient + rest + (align - rest) = align * (quotient + 1) by
        rw [Nat.mul_add, Nat.mul_one]
        omega]
    exact Nat.mul_mod_right _ _

theorem layoutEnd_ge (params : List Param) :
    ∀ (sizes : List Nat) (args : List Arg) (start : Nat),
      start ≤ layoutEnd params sizes args start := by
  induction params with
  | nil => intros; exact Nat.le_refl _
  | cons param params ih =>
      intro sizes args start
      cases param with
      | word32 | word64 | enum32 _ | flags32 _ | flags64 _ => exact ih sizes args.tail start
      | record => simp only [layoutEnd]; omega
      | input | output => exact Nat.le_trans (Nat.le_add_right _ _) (ih sizes args.tail _)
      | result32 =>
          exact Nat.le_trans (Nat.le_trans (le_alignUp start 4) (Nat.le_add_right _ _))
            (ih sizes args _)
      | result64 =>
          exact Nat.le_trans (Nat.le_trans (le_alignUp start 8) (Nat.le_add_right _ _))
            (ih sizes args _)
      | reported scale align shown =>
          exact Nat.le_trans (Nat.le_trans (le_alignUp start align) (Nat.le_add_right _ _))
            (ih sizes.tail args _)

namespace Layout

/-- `span` starts at `address % 2^32` for an `address` with `start ≤ address` and
`address + span.2 ≤ stop`. -/
def Within (start stop : Nat) (span : Nat × Nat) : Prop :=
  ∃ address, span.1 = address % 2 ^ 32 ∧ start ≤ address ∧ address + span.2 ≤ stop

theorem Within.weaken {start start' stop : Nat} {span : Nat × Nat}
    (within : Within start stop span) (le : start' ≤ start) : Within start' stop span := by
  obtain ⟨address, eq, low, high⟩ := within
  exact ⟨address, eq, Nat.le_trans le low, high⟩

/-- A span that ends at or before `next` is apart from a span within `next` and `stop`.  A span
at `2^32` wraps to address 0 with size 0, which is apart from every span. -/
theorem disjoint_of_below {address size next stop : Nat} {span : Nat × Nat}
    (below : address + size ≤ next) (within : Within next stop span) (fits : stop ≤ 2 ^ 32) :
    LeanExe.Runtime.regionsDisjoint ((UInt32.ofNat address).toNat, size) span := by
  obtain ⟨other, eq, low, high⟩ := within
  simp only [LeanExe.Runtime.regionsDisjoint, UInt32.toNat_ofNat']
  omega

theorem wrap_aligned {address align : Nat} (fits : address ≤ 2 ^ 32)
    (aligned : address % align = 0) : (UInt32.ofNat address).toNat % align = 0 := by
  rw [UInt32.toNat_ofNat']
  rcases Nat.lt_or_ge address (2 ^ 32) with below | top
  · rw [Nat.mod_eq_of_lt below]
    exact aligned
  · rw [show address = 2 ^ 32 by omega, Nat.mod_self, Nat.zero_mod]

/-- The regions `regions` and the input places `places` lie between `start` and `stop`, modulo
`2^32`, apart from one another, and each region's pointer is a multiple of its alignment. -/
structure Laid (start stop : Nat) (regions : List Region)
    (places : List (UInt32 × LeanExe.Bytes)) : Prop where
  region : ∀ region ∈ regions,
    Within start stop region.span ∧ region.pointer.toNat % region.align = 0
  place : ∀ place ∈ places, Within start stop (placeSpan place)
  apart : (regions.map Region.span ++ places.map placeSpan).Pairwise
    LeanExe.Runtime.regionsDisjoint

theorem Laid.nil (start : Nat) : Laid start start [] [] :=
  ⟨nofun, nofun, List.Pairwise.nil⟩

theorem Laid.cons_region {start stop address size align : Nat} {shown : Bool}
    {regions : List Region} {places : List (UInt32 × LeanExe.Bytes)} (low : start ≤ address)
    (aligned : address % align = 0) (high : address + size ≤ stop) (fits : stop ≤ 2 ^ 32)
    (rest : Laid (address + size) stop regions places) :
    Laid start stop (⟨UInt32.ofNat address, size, align, shown⟩ :: regions) places where
  region := by
    intro region member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨⟨address, UInt32.toNat_ofNat', low, high⟩, wrap_aligned (by omega) aligned⟩
    · have inRest := rest.region region member
      exact ⟨inRest.1.weaken (by omega), inRest.2⟩
  place place member := (rest.place place member).weaken (by omega)
  apart := by
    rw [List.map_cons, List.cons_append, List.pairwise_cons]
    refine ⟨?_, rest.apart⟩
    intro span member
    rcases List.mem_append.mp member with inRegions | inPlaces
    · obtain ⟨region, regionMember, rfl⟩ := List.mem_map.mp inRegions
      exact disjoint_of_below (Nat.le_refl _) (rest.region region regionMember).1 fits
    · obtain ⟨place, placeMember, rfl⟩ := List.mem_map.mp inPlaces
      exact disjoint_of_below (Nat.le_refl _) (rest.place place placeMember) fits

theorem Laid.cons_place {start size stop : Nat} {bytes : LeanExe.Bytes} {regions : List Region}
    {places : List (UInt32 × LeanExe.Bytes)} (sized : bytes.data.size = size)
    (high : start + size ≤ stop) (fits : stop ≤ 2 ^ 32)
    (rest : Laid (start + size) stop regions places) :
    Laid start stop regions ((UInt32.ofNat start, bytes) :: places) where
  region region member :=
    have inRest := rest.region region member
    ⟨inRest.1.weaken (by omega), inRest.2⟩
  place := by
    intro place member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨start, UInt32.toNat_ofNat', Nat.le_refl _, by simp only [placeSpan]; omega⟩
    · exact (rest.place place member).weaken (by omega)
  apart := by
    rw [List.map_cons]
    refine (List.Perm.pairwise_iff (fun disjoint => Or.symm disjoint) List.perm_middle).mpr ?_
    rw [List.pairwise_cons]
    refine ⟨?_, rest.apart⟩
    intro span member
    have below : start + bytes.data.size ≤ start + size := by omega
    rcases List.mem_append.mp member with inRegions | inPlaces
    · obtain ⟨region, regionMember, rfl⟩ := List.mem_map.mp inRegions
      exact disjoint_of_below below (rest.region region regionMember).1 fits
    · obtain ⟨place, placeMember, rfl⟩ := List.mem_map.mp inPlaces
      exact disjoint_of_below below (rest.place place placeMember) fits

theorem laid (params : List Param) :
    ∀ (sizes : List Nat) (args : List Arg) (start : Nat),
      (∀ scale align shown, Param.reported scale align shown ∈ params → 0 < align) →
      layoutEnd params sizes args start ≤ 2 ^ 32 →
      Laid start (layoutEnd params sizes args start)
        (outputRegions params sizes args (layoutPointers params sizes args start))
        (inputPlaces params args (layoutPointers params sizes args start)) := by
  induction params with
  | nil => intro sizes args start _ _; exact Laid.nil start
  | cons param params ih =>
      intro sizes args start aligned fits
      have alignedRest :
          ∀ scale align shown, Param.reported scale align shown ∈ params → 0 < align :=
        fun scale align shown member => aligned scale align shown (List.mem_cons_of_mem _ member)
      cases param with
      | word32 | word64 | enum32 _ | flags32 _ | flags64 _ =>
          exact ih sizes args.tail start alignedRest fits
      | record => simp only [layoutEnd] at fits; omega
      | input =>
          simp only [layoutEnd, layoutPointers, outputRegions, inputPlaces, List.tail_cons,
            List.headD_cons] at fits ⊢
          refine Laid.cons_place ?_ (layoutEnd_ge _ _ _ _) fits (ih _ _ _ alignedRest fits)
          cases args with
          | nil => rfl
          | cons arg _ => cases arg <;> rfl
      | output =>
          simp only [layoutEnd, layoutPointers, outputRegions, inputPlaces, List.tail_cons,
            List.headD_cons] at fits ⊢
          exact Laid.cons_region (Nat.le_refl _) (Nat.mod_one _) (layoutEnd_ge _ _ _ _) fits
            (ih _ _ _ alignedRest fits)
      | result32 | result64 =>
          simp only [layoutEnd, layoutPointers, outputRegions, inputPlaces, List.tail_cons,
            List.headD_cons] at fits ⊢
          exact Laid.cons_region (le_alignUp _ _) (alignUp_mod _ (by decide))
            (layoutEnd_ge _ _ _ _) fits (ih _ _ _ alignedRest fits)
      | reported scale align shown =>
          simp only [layoutEnd, layoutPointers, outputRegions, inputPlaces, List.tail_cons,
            List.headD_cons] at fits ⊢
          exact Laid.cons_region (le_alignUp _ _)
            (alignUp_mod _ (aligned scale align shown List.mem_cons_self))
            (layoutEnd_ge _ _ _ _) fits (ih _ _ _ alignedRest fits)

end Layout

end Verified.Wasi

namespace LeanExe.Wasi

open Wasm Verified.Wasi

/-- `host` is total, and it permits a reply to every request of each call in `calls` that fits the
call's parameters and that the call does not reject. -/
structure Host.TotalFor {World : Type} (host : Host World) (calls : List Call) : Prop
    extends host.Total where
  sys : ∀ call ∈ calls, ∀ world request, argsFit call.params request = true →
    call.reject request = 0 → ∃ reply after, host.sys world call request reply after

/-- `Host.Answers`, and a permitted reply to every request of each call in `calls` that fits, that
the call does not reject, and whose regions and inputs fit below `2^32` when laid out one after
another from address 16, for a call whose reported regions have positive alignments. -/
structure Host.AnswersFor {World : Type} (host : Host World) (calls : List Call) : Prop
    extends host.Answers where
  sys : ∀ call ∈ calls,
    (∀ scale align shown, Param.reported scale align shown ∈ call.params → 0 < align) →
    ∀ world request, argsFit call.params request = true → call.reject request = 0 →
      layoutEnd call.params (host.reported world call) request 16 ≤ 2 ^ 32 →
      ∃ reply after, host.sys world call request reply after

namespace Host.TotalFor

variable {World : Type} {host : Host World} {calls : List Call}

open Classical in
/-- An oracle that chooses a permitted reply to each fitting, accepted request of a call in
`calls`.  Any other request gets a trap with an empty message, which no contract constrains. -/
noncomputable def sysOracle (total : host.TotalFor calls) : OracleSys.Oracle World where
  reply world call request :=
    if valid : call ∈ calls ∧ argsFit call.params request = true ∧
        call.reject request = 0 then
      let permitted := total.sys call valid.1 world request valid.2.1 valid.2.2
      (Classical.choose permitted, Classical.choose (Classical.choose_spec permitted))
    else (.trapped "" [], world)

theorem sysOracle_sound (total : host.TotalFor calls) : total.sysOracle.Sound host calls := by
  intro call member world request fits accepted
  have valid : call ∈ calls ∧ argsFit call.params request = true ∧ call.reject request = 0 :=
    ⟨member, fits, accepted⟩
  simp only [sysOracle, dite_eq_left valid]
  exact Classical.choose_spec
    (Classical.choose_spec (total.sys call member world request fits accepted))

/-- A host total for `calls` has a host environment that satisfies `hostSpecWith host calls` for
every module that imports the calls `calls` after the three WASI imports. -/
theorem satisfiableWith (total : host.TotalFor calls) (target : Wasm.Module)
    (imports : target.imports = ABI.importsWith calls) :
    ∃ targetHost : HostEnv (Observed World),
      targetHost.Satisfies target (hostSpecWith host calls) :=
  ⟨OracleSys.env total.toTotal.oracle total.sysOracle calls,
    OracleSys.env_satisfies total.toTotal.oracle_sound total.sysOracle_sound target imports⟩

end Host.TotalFor

namespace Host.Answers

variable {World : Type} {host : Host World} {calls : List Call}

/-- The request store of `world` and the layout memory, with the layout's pointers, satisfies
`SysRequest` for a fitting, accepted request whose layout from address 16 fits below `2^32`. -/
theorem layoutRequest (world : World) (call : Call) (request : List Arg) (sizes : List Nat)
    (fits : argsFit call.params request = true) (accepted : call.reject request = 0)
    (aligned :
      ∀ scale align shown, Param.reported scale align shown ∈ call.params → 0 < align)
    (bound : layoutEnd call.params sizes request 16 ≤ 2 ^ 32) :
    SysRequest
      (requestStore world
        (layoutMemory call.params request (layoutPointers call.params sizes request 16)))
      (lowerArgs call.params request (layoutPointers call.params sizes request 16)) call request
      (layoutPointers call.params sizes request 16) sizes := by
  have laid := Layout.laid call.params sizes request 16 aligned bound
  have apart := List.pairwise_append.mp laid.apart
  refine ⟨fits, accepted, rfl, ?_, ?_, apart.1, fun region regionMember place placeMember =>
    apart.2.2 _ (List.mem_map.mpr ⟨region, regionMember, rfl⟩) _
      (List.mem_map.mpr ⟨place, placeMember, rfl⟩)⟩
  · apply placeAll_at
    · exact (List.pairwise_append.mp laid.apart).2.1
    · intro place member
      obtain ⟨address, eq, _, high⟩ := laid.place place member
      simp only [placeSpan] at eq high
      change _ ∧ _ ≤ 65536 * 65536
      constructor <;> omega
  · intro region member
    obtain ⟨⟨address, eq, _, high⟩, alignment⟩ := laid.region region member
    simp only [Region.span] at eq high
    refine ⟨?_, by omega, alignment⟩
    change _ ≤ (placeAll (Mem.empty 65536) _).pages * 65536
    rw [placeAll_pages]
    change _ ≤ 65536 * 65536
    omega

theorem satisfies_streams {targetHost : HostEnv (Observed World)} {target : Wasm.Module}
    (valid : targetHost.Satisfies target (hostSpecWith host calls))
    (imports : target.imports = ABI.importsWith calls) :
    targetHost.Satisfies { target with imports := ABI.imports } (hostSpec host) := by
  intro index bound
  change index < ABI.imports.length at bound
  rw [ABI.imports_length] at bound
  obtain ⟨fn, contract, found, spec, sound⟩ :=
    valid index (by rw [imports, ABI.importsWith_length]; omega)
  refine ⟨fn, contract, found, ?_, sound⟩
  rw [← spec]
  simp only [hostSpecWith, hostSpec]
  rw [List.getElem?_append_left (by simp only [List.length_cons, List.length_nil]; omega)]

/-- Every host environment that satisfies `hostSpecWith host calls` for a module that imports the
calls `calls` after the three WASI imports answers each stream request that the one-iovec ABI
expresses with its payload at address 16, and each fitting, accepted request of a call in `calls`
whose inputs and regions fit below `2^32` when laid out from address 16. -/
theorem of_satisfiesWith {targetHost : HostEnv (Observed World)} {target : Wasm.Module}
    (valid : targetHost.Satisfies target (hostSpecWith host calls))
    (imports : target.imports = ABI.importsWith calls) : host.AnswersFor calls where
  toAnswers := of_satisfies (target := { target with imports := ABI.imports })
    (satisfies_streams valid imports) rfl
  sys call member aligned world request fits accepted bound := by
    obtain ⟨position, found⟩ := List.mem_iff_getElem?.mp member
    have inCalls : position < calls.length := (List.getElem?_eq_some_iff.mp found).1
    obtain ⟨fn, _, contract⟩ := valid.lookup_contract (i := 3 + position)
      (by rw [imports, ABI.importsWith_length]; omega) (hostSpecWith_sys host found)
    have result := contract _ _ request _
      (layoutRequest world call request _ fits accepted aligned bound)
    generalize fn.invoke _ _ = outcome at result
    cases outcome with
    | Return values after =>
        obtain ⟨_, _, _, relation, _⟩ := result
        exact ⟨_, _, relation.1⟩
    | Trap after message =>
        obtain ⟨_, relation, _⟩ := result
        exact ⟨_, _, relation.1⟩
    | Throw _ _ _ => exact result.elim

end Host.Answers

end LeanExe.Wasi
