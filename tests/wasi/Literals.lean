import Verified.Examples.Literals

namespace Verified.Examples.Literals

#guard compiled.literalPool.values.length = 3
#guard compiled.literalPool.payload = [65, 0, 255, 128, 1, 1]
#guard (compiled.literalPool.base, compiled.literalPool.endAddress, compiled.literalPool.top) =
  (4096, 4102, 4104)
#guard (Verified.Bytes.literalOffset compiled.literalPool.values [65, 0, 255],
    Verified.Bytes.literalOffset compiled.literalPool.values [128, 1],
    Verified.Bytes.literalOffset compiled.literalPool.values [1]) = (some 0, some 3, some 5)
#guard (compiled.module.memory.map fun memory =>
    memory.data.map fun segment => (segment.offset, segment.bytes)) =
  some [(some 4096, [65, 0, 255, 128, 1, 1])]
#guard (compiled.module.globals.head?.bind fun global =>
    match global.init with
    | .i64 top => some top
    | _ => none) = some 4104

#guard compiled.nestedIndex.func.modes = [.borrowed]
#guard compiled.arrayFold.func.modes = [.borrowed]
#guard compiled.listFold.func.modes = [.borrowed]
#guard compiled.treeCase.func.modes = [.borrowed]
#guard compiled.tail.func.modes = [.borrowed, .owned]

#guard constant.data.data.toList = [65, 0, 255]
#guard empty.size = 0
#guard (repeated.1.data.data.toList, repeated.2.data.data.toList) =
  ([65, 0, 255], [65, 0, 255])
#guard ((choose true).data.data.toList, (choose false).data.data.toList) =
  ([65, 0, 255], [128, 1])
#guard (lookup 2, lookup 18446744073709551615) = (255, 0)
#guard helper 0 = 65
#guard nestedIndex (bytes![0, 1, 255, 128]) = 1
#guard (byteBuild 4).data.data.toList = [65, 0, 255, 65]
#guard (arrayBuild 4).toList = [65, 0, 255, 65]
#guard loop 4 = 385
#guard arrayFold #[2, 0, 5, 4] = 575
#guard listFold [2, 0, 5, 4] = 575
#guard (treeCase [], treeCase [2, 99], treeCase [3]) = (65, 128, 1)
#guard (tail 3 (bytes![0, 1, 255, 128])).data.data.toList = [65, 0, 255]
#guard guarded 4 = 320

end Verified.Examples.Literals
