/-! Files of little-endian words and the Wasmtime host's format for arrays, which the order book's
native comparison and its module cases share. -/

namespace TestSupport.OrderBook.Words

/-- The words of a file of little-endian words. -/
def readWords (path : System.FilePath) : IO (Array UInt64) := do
  let bytes ← IO.FS.readBinFile path
  unless bytes.size % 8 == 0 do
    throw (IO.userError s!"{path}: length {bytes.size} bytes is not a multiple of 8")
  let mut ws : Array UInt64 := Array.emptyWithCapacity (bytes.size / 8)
  for i in [0:bytes.size / 8] do
    let mut w : UInt64 := 0
    for j in [0:8] do
      w := w ||| (bytes.get! (8 * i + j)).toUInt64 <<< (8 * j).toUInt64
    ws := ws.push w
  return ws

/-- The little-endian bytes of the words `ws`. -/
def wordBytes (ws : Array UInt64) : ByteArray := Id.run do
  let mut bytes := ByteArray.empty
  for w in ws do
    for j in [0:8] do
      bytes := bytes.push (w >>> (8 * j).toUInt64).toUInt8
  return bytes

/-- An array in the Wasmtime host's output format. -/
def hostArray (xs : Array UInt64) : String :=
  "[" ++ ", ".intercalate (xs.toList.map toString) ++ "]"

end TestSupport.OrderBook.Words
