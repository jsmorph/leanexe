import Sail
import THE_MODULE_NAME.Defs

/-!
Exact rational numbers in place of the real numbers of Sail's specification, so that the model's
floating-point functions evaluate on concrete operands.  The operations below are exact on
rationals, which contain every value that FPAdd, FPSub, FPMul, FPDiv, and FixedToFP compute.
A square root has no rational value in general: `sqrt_real` is an opaque constant, and FPSqrt is
not evaluated with this file.
-/

namespace THE_MODULE_NAME

abbrev real := Rat

def neg_real (x : real) : real := -x
def mult_real (x y : real) : real := x * y
def sub_real (x y : real) : real := x - y
def add_real (x y : real) : real := x + y
def div_real (x y : real) : real := x / y
opaque sqrt_real (x : real) : real
def abs_real (x : real) : real := if x < 0 then -x else x
def round_down (x : real) : Int := x.floor
def round_up (x : real) : Int := x.ceil
def to_real (x : Int) : real := x
def eq_real (x y : real) : Bool := x == y
def lt_real (x y : real) : Bool := decide (x < y)
def gt_real (x y : real) : Bool := decide (y < x)
def lteq_real (x y : real) : Bool := decide (x ≤ y)
def gteq_real (x y : real) : Bool := decide (y ≤ x)
def real_power (x : real) (n : Int) : real := x ^ n
def print_real (_ : String) (_ : real) : Unit := ()
def prerr_real (_ : String) (_ : real) : Unit := ()
def random_real (_ : Unit) : real := 34
def undefined_real (_ : Unit) : SailM real := return default
