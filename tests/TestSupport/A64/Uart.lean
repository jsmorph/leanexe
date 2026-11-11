import TestSupport.A64.Programs
import LeanExe.A64.Proof.InputRuns

/-!
GCD's loop, entry 2 of `loopCompiled.module`, as a bare-metal program that reads its two arguments
from the UART: the image of `genInImage` at `imageBase`, with the stack's room `room` and the
memory's cap `cap` of `TestSupport.A64.Programs`, reads two words of eight bytes each, the lowest
first, and writes the eight bytes of their GCD and the status byte 0.  `uart_runs` is its
theorem in the form `InputRuns`: `loopCompiled.gcd.implements` excludes every trap, and the stack
that the loop uses is at most 4096 bytes.  `cases` lists the pairs on which
`tests/baremetal/a64-uart.sh` runs the image under QEMU.
-/

namespace TestSupport.A64.Uart

open LeanExe.A64 TestSupport.Native.Gcd

/-- The words of a list of two words as GCD's argument. -/
def args (ws : List UInt64) : UInt64 × UInt64 := (ws.getD 0 0, ws.getD 1 0)

/-- The image of GCD's loop that reads its arguments from the UART, at `imageBase`. -/
def image : Except String (List UInt8 × Layout) :=
  genInImage loopCompiled.module 2 2 room cap .word imageBase

/-- The theorem of GCD's loop on two words read from the UART: the program writes the eight
bytes of the GCD of the delivered words and returns 0, and it ends with status 65 when a byte
carries an error flag. -/
theorem uart_runs (room : UInt64) (cap : Nat) :
    InputRuns loopCompiled.module 2 2 room cap .word
      (fun ws => LeanExe.Native.encodeWord (gcd (ws.getD 0 0) (ws.getD 1 0))) fun _ _ => False :=
  input_runs_bounded loopCompiled.gcd.implements args loopCompiled.initial.1
    (fun _ _ _ => trivial) writes_word (.inl (by decide +kernel))
    (hargs := fun ws hws => by
      match ws, hws with
      | [_, _], _ => rfl)

/-- The pairs of words on which the image runs under QEMU: zeros, equal words, the largest word,
words whose GCD is a power of two, consecutive Fibonacci numbers, which take the most steps
below 2^64, and the pair of `TestSupport.A64.Programs`. -/
def cases : List (UInt64 × UInt64) :=
  [(1071, 462), (0, 0), (0, 5), (5, 0), (18446744073709551615, 18446744073709551615),
    (18446744073709551615, 1), (9223372036854775808, 4611686018427387904),
    (12200160415121876738, 7540113804746346429), (0x0123456789ABCDEF, 0xFEDCBA9876543210)]

/-- The bytes that the UART receives for a pair: the eight bytes of each word, the lowest
first. -/
def input (c : UInt64 × UInt64) : List UInt8 := bytesOf c.1 ++ bytesOf c.2

/-- The bytes that the UART must show for a pair: the eight bytes of the GCD and the status byte
0. -/
def expected (c : UInt64 × UInt64) : List UInt8 :=
  LeanExe.Native.encodeWord (gcd c.1 c.2) ++ [0]

end TestSupport.A64.Uart
