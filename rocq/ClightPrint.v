(* The output of the evaluator of ClightEval.v for the generated test programs, in the form of
   the .expected files that tests/TestSupport/Native/ClightDiff.lean writes.  test_output runs
   the function test of a random program or a NaN program and gives the lines that its main
   prints: the result and the bits of the globals.  trace_output runs main of a trace program or
   an input program and gives one line per volatile access, as CompCert's reference interpreter
   prints it (driver/Interp.ml, print_event), and the exit code.  Either gives UB when the
   evaluator is stuck and FUEL when the fuel runs out.  The programs come from clightgen with
   canonical identifiers, so ident_of_string and string_of_ident of export/Ctypesdefs.v convert
   between names and identifiers.  tests/native/clight-rocq.sh states, for each program, that
   the output equals its .expected file. *)

From Coq Require Import String List ZArith.
Require Import Coqlib Integers Values AST Memory Events Globalenvs Ctypes Clight.
Require Ctypesdefs ClightEval.
Import ClightEval.

Local Open Scope string_scope.

(* The fuel of ClightDiff.lean. *)
Definition fuel : nat := Z.to_nat 1000000.

Definition digit (d: Z) : string :=
  match String.get (Z.to_nat d) "0123456789abcdef" with
  | Some c => String c EmptyString
  | None => "?"
  end.

Fixpoint digits (base: Z) (n: nat) (z: Z) (acc: string) : string :=
  match n with
  | O => acc
  | S n' =>
      let acc' := digit (z mod base) ++ acc in
      if Z.eqb (z / base) 0 then acc' else digits base n' (z / base) acc'
  end.

Definition hex (z: Z) : string := digits 16 64 z "".

Definition dec (z: Z) : string :=
  if Z.ltb z 0 then "-" ++ digits 10 64 (- z) "" else digits 10 64 z "".

Definition symbol (name: string) : ident := Ctypesdefs.ident_of_string name.

(* The bits of the chunk at offset ofs of the global name in m. *)
Definition bits_at (p: program) (m: mem) (name: string) (chunk: memory_chunk) (ofs: Z)
    : option Z :=
  match Genv.find_symbol (globalenv p) (symbol name) with
  | None => None
  | Some b =>
      match MemExec.load chunk m b ofs with
      | Some (Vint n) => Some (Int.unsigned n)
      | Some (Vlong n) => Some (Int64.unsigned n)
      | _ => None
      end
  end.

Definition line (label: string) (o: option Z) : string :=
  match o with
  | Some n => label ++ " " ++ hex n
  | None => label ++ " ?"
  end.

Definition test_output (p: program) : list string :=
  match run p (symbol "test") nil fuel with
  | Stuck => "UB" :: nil
  | OutOfFuel => "FUEL" :: nil
  | Done (_, m, v) =>
      line "r" (match v with Vlong n => Some (Int64.unsigned n) | _ => None end) ::
      line "g_u32" (bits_at p m "g_u32" Mint32 0) ::
      line "g_u64" (bits_at p m "g_u64" Mint64 0) ::
      line "g_f64" (bits_at p m "g_f64" Mint64 0) ::
      line "g_f32" (bits_at p m "g_f32" Mint32 0) ::
      map (fun i => line "arr" (bits_at p m "arr" Mint64 (8 * i)))
          (0 :: 1 :: 2 :: 3 :: 4 :: 5 :: 6 :: 7 :: nil) ++
      line "pun" (bits_at p m "pun" Mint64 0) :: nil
  end.

(* PrintAST.name_of_chunk of CompCert's common/PrintAST.ml. *)
Definition chunk_name (c: memory_chunk) : string :=
  match c with
  | Mbool => "bool"
  | Mint8signed => "int8s"
  | Mint8unsigned => "int8u"
  | Mint16signed => "int16s"
  | Mint16unsigned => "int16u"
  | Mint32 => "int32"
  | Mint64 => "int64"
  | Mfloat32 => "float32"
  | Mfloat64 => "float64"
  | Many32 => "any32"
  | Many64 => "any64"
  end.

Definition eventval_text (ev: eventval) : string :=
  match ev with
  | EVint n => dec (Int.signed n)
  | EVlong n => dec (Int64.signed n) ++ "LL"
  | _ => "?"
  end.

Definition location (chunk: memory_chunk) (id: ident) (ofs: ptrofs) : string :=
  let o := Ptrofs.signed ofs in
  chunk_name chunk ++ "[&" ++ Ctypesdefs.string_of_ident id ++
  (if Z.ltb o 0 then dec o else "+" ++ dec o) ++ "]".

Definition event_line (ev: event) : string :=
  match ev with
  | Event_vstore chunk id ofs v =>
      "observable event: volatile store " ++ location chunk id ofs ++ " <- " ++ eventval_text v
  | Event_vload chunk id ofs v =>
      "observable event: volatile load " ++ location chunk id ofs ++ " -> " ++ eventval_text v
  | _ => "observable event: ?"
  end.

Definition trace_output (p: program) : list string :=
  match run_program p fuel with
  | Stuck => "UB" :: nil
  | OutOfFuel => "FUEL" :: nil
  | Done (t, r) =>
      map event_line t ++
      ("program terminated (exit code = " ++ dec (Int.signed r) ++ ")") :: nil
  end.
